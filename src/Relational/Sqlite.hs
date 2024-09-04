{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Relational.Sqlite
  ( Sqlite,
    Exp (..),
    Relation (..),
    pureExpField,
    Transactional (..),
    TransactionT (..),
    Shaped (..),
    shapeOne,
    module Relational.Class,
    TableName,
    ParseExpSqlite (..),
    FromField (..),
    fromFieldViaRead,
    ToField (..),
    toFieldViaShow,
    sqliteTableDecl,
    runTransactionT,
    UnsafeArgument,
    unsafeArgument,
    unsafeFunApp,
    unsafeEqApp,
    unsafeBinopApp,
    field,
    TransactionEnv (..),
    -- Template Haskell
    relationalRecordInstances,
    relationalFieldInstances,
    -- Functions for testing
    ppRel,
    test,
  )
where

import Control.Applicative
import Control.Category
import Control.Exception hiding (TypeError)
import Control.Monad.Except
import Control.Monad.IO.Unlift (MonadUnliftIO)
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.State.Strict qualified as Sqlite.StateT
import Control.Monad.Writer
import Data.Bifunctor
import Data.Char
import Data.Coerce
import Data.Either
import Data.Fixed
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.Kind
import Data.List (stripPrefix)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Maybe
import Data.Monoid
import Data.Profunctor
import Data.Text (Text)
import Data.Text qualified
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Text.Internal.Fusion (Stream)
import Data.Text.Lazy qualified
import Data.Time
import Data.Traversable (for)
import Data.Typeable
import Data.UUID (UUID)
import Data.UUID qualified
import Database.SQLite.Simple hiding (query)
import Database.SQLite.Simple qualified as Sqlite
import Database.SQLite.Simple.FromField as Sqlite
import Database.SQLite.Simple.FromRow as Sqlite
import Database.SQLite.Simple.Internal qualified as Sqlite.Internal
import Database.SQLite.Simple.Ok as Sqlite
import Database.SQLite.Simple.ToField as Sqlite
import Debug.Trace
import GHC.Generics qualified
import GHC.TypeError
import GHC.TypeLits
import Generics.SOP hiding (Shape)
import Generics.SOP.GGP qualified as GGP
import Generics.SOP.Type.Metadata qualified as Metadata
import Language.Haskell.TH hiding (Code, Exp, Type)
import Language.Haskell.TH qualified as TH
import Relational.Class hiding (relationalFieldInstances, relationalRecordInstances)
import Relational.Sqlite.Internal hiding (test)
import Text.Read (readMaybe)
import Prelude hiding (id, maximum, (.))

data Sqlite

class Shaped a where
  shaped :: Proxy a -> Shape
  default shaped :: (GShaped a) => Proxy a -> Shape
  shaped = gshaped

class GShaped a where
  gshaped :: Proxy a -> Shape

instance
  ( Code a ~ '[xs],
    xs ~ x ': xx,
    Generics.SOP.All Shaped xs,
    HasDatatypeInfo a
  ) =>
  GShaped a
  where
  gshaped proxy =
    let (con :* Nil) = constructorInfo $ datatypeInfo proxy

        fieldProxies :: NP Proxy xs
        fieldProxies = hpure @_ @_ @NP @xs Proxy

        fieldShapes :: NP (K (Text, Shape)) xs
        fieldShapes =
          hcliftA2
            (Proxy @Shaped)
            (\proxy (K col) -> K (col, shaped proxy))
            fieldProxies
            (shapeNP @a @xs)
     in case datatypeInfo proxy of
          ADT {} -> npKShapeToShape fieldShapes
          Newtype {} -> shaped (Proxy @x)
    where
      npKShapeToShape :: NP (K (Text, Shape)) xs -> Shape
      npKShapeToShape (s :* ss) = ShapeRecord (unK s NE.:| hcollapse ss)

shapeNP ::
  forall a xs.
  (HasDatatypeInfo a, Code a ~ '[xs]) =>
  NP (K ColumnAlias) xs
shapeNP =
  let (con :* Nil) = constructorInfo $ datatypeInfo (Proxy @a)
   in case con of
        Constructor name -> prefixConName name tagConFields
        Infix name _ _ -> prefixConName name tagConFields
        Record name fieldInfos -> prefixConName name $ tagRecFields name fieldInfos
  where
    prefixConName :: ConstructorName -> NP (K Text) xs -> NP (K Text) xs
    prefixConName name' =
      {- Actually, don't
      let name
            | all isLetter name' = name'
            | all (`elem` "(,)") name' = "" -- "tuple"
            | otherwise = "con"
       in hmap (mapKK ((T.pack name <> "_") <>))
       -} id

    tagConFields :: NP (K Text) xs
    tagConFields =
      flip evalState 1 $
        hsequenceK $
          hpure
            ( K do
                ix <- get
                modify succ
                return ("_" <> T.pack (show ix))
            )

    tagRecFields :: ConstructorName -> NP FieldInfo xs -> NP (K ColumnAlias) xs
    tagRecFields con = hliftA (\(FieldInfo name) -> K (mangleFieldName con name))

-- The situation with record fields in haskell requires a bit of handling in order to
-- make reasonable column names.
--
-- data Foo = Foo {
--    _fooSomeField :: ..,
--    _fooOtherField :: ...
--    }
--
-- Should have columns "some_field" and "other_field".
mangleFieldName :: ConstructorName -> FieldName -> Text
mangleFieldName con field =
  let -- remove prefix underscores
      field' = dropWhile (== '_') field
      -- upper-camel case to match con
      field'' = case field' of
        ch : r -> [toUpper ch] <> r
        [] -> []
      -- remove optional constructor prefix
      field''' = fromMaybe field'' (con `stripPrefix` field'')
      field'''' = case field''' of
        ch : r -> [toLower ch] <> r
        [] -> []
      field''''' = concatMap (\ch -> if isUpper ch then ['_', toLower ch] else [ch]) field''''
   in T.pack field'''''

instance Shaped Int where
  shaped _ = shapeOne

instance Shaped (Fixed n) where
  shaped _ = shapeOne

instance Shaped Double where
  shaped _ = shapeOne

instance Shaped String where
  shaped _ = shapeOne

instance Shaped Text where
  shaped _ = shapeOne

instance Shaped Data.Text.Lazy.Text where
  shaped _ = shapeOne

instance Shaped Bool where
  shaped _ = shapeOne

instance Shaped UUID where
  shaped _ = shapeOne

instance Shaped UTCTime where
  shaped _ = shapeOne

instance Shaped Day where
  shaped _ = shapeOne

instance PureExp Sqlite Data.Text.Lazy.Text where
  pureExp = pureExpField

instance PureExp Sqlite Double where
  pureExp = pureExpField

instance PureExp Sqlite UUID where
  pureExp = pureExpField

instance PureExp Sqlite UTCTime where
  pureExp = pureExpField

instance PureExp Sqlite Day where
  pureExp = pureExpField

instance ParseExpSqlite Data.Text.Lazy.Text where
  expSqliteRowParser = field

instance ParseExpSqlite UTCTime where
  expSqliteRowParser = field

instance ParseExpSqlite Double where
  expSqliteRowParser = field

instance ParseExpSqlite UUID where
  expSqliteRowParser = field

instance ParseExpSqlite Day where
  expSqliteRowParser = field

instance
  ( Code a ~ '[xs],
    KnownSymbol conName,
    GGP.GDatatypeInfoOf a
      ~ 'Metadata.ADT
          _moduleName
          _typeName
          '[ 'Metadata.Record conName _fieldInfos
           ]
          strictnessInfo,
    Generic a
  ) =>
  GProjectExp Sqlite a
  where
  gProjectField ::
    forall (fieldLabel :: Metadata.FieldName).
    (KnownSymbol fieldLabel) =>
    Proxy fieldLabel ->
    Exp Sqlite a ->
    Exp Sqlite (TypeOfField a fieldLabel)
  gProjectField p@Proxy (Exp_Sqlite exp_act) = Exp_Sqlite do
    repr <- exp_act
    -- We should generate this only once as a function of metadata and field.
    -- We shouldn'- be manually mangling names in multiple places.
    let shapeProj = mangleFieldName (symbolVal (Proxy @conName)) $ {-symbolVal (Proxy @conName) <> "_" <>-} symbolVal p
    return (sRecProj repr shapeProj)

instance
  ( Generic a,
    Code a ~ '[xs],
    xs ~ x ': xxs,
    HasDatatypeInfo a
  ) =>
  GConstructExp Sqlite a
  where
  gNew Proxy (Proxy :: Proxy a) =
    let (K colAlias :* rest) = shapeNP @a @xs
     in \(Exp_Sqlite xAction) ->
          let firstCols :: ColumnsSoFar
              firstCols = do
                xVal <- xAction
                return ((colAlias, xVal) NE.:| [])
           in gnew' @a firstCols rest
    where
      gnew' :: forall a xs. ColumnsSoFar -> NP (K ColumnAlias) xs -> ConFun Sqlite a xs
      gnew' colsSoFar Nil = Exp_Sqlite $ do
        SRecCon <$> colsSoFar
      gnew' colsSoFar (K colAlias :* xs) = \(Exp_Sqlite xAction) ->
        let moreCols :: ColumnsSoFar
            moreCols = do
              cols <- colsSoFar
              xVal <- xAction
              return (cols <> ((colAlias, xVal) NE.:| []))
         in gnew' @a moreCols xs

pureExpField :: (ToField a) => a -> Exp Sqlite a
pureExpField x = Exp_Sqlite (return $ SPrimSqlData (toField x))

instance PureExp Sqlite Bool where
  pureExp = pureExpField

instance PureExp Sqlite Int where
  pureExp = pureExpField

instance PureExp Sqlite (Fixed e) where
  pureExp = pureExpField

instance PureExp Sqlite String where
  pureExp str = Exp_Sqlite (return $ SPrimSqlData (toField $ T.pack str))

instance PureExp Sqlite Text where
  pureExp str = Exp_Sqlite (return $ SPrimSqlData (toField str))

instance
  ( Generic a,
    Code a ~ '[xs],
    xs ~ x ': xxs,
    Generics.SOP.All (PureExp Sqlite) xs,
    HasDatatypeInfo a
  ) =>
  GPureExp Sqlite a
  where
  gPureExp x =
    let SOP (Z fieldsNP) = from x
        pureExpNP :: NP (Exp Sqlite) xs
        pureExpNP = hcliftA (Proxy @(PureExp Sqlite)) (\(I x) -> pureExp x) fieldsNP

        recConNP :: NP (K OneCol) xs
        recConNP =
          hliftA2
            ( \(K colAlias) (Exp_Sqlite expAct) -> K do
                xRepr <- expAct
                return (colAlias, xRepr)
            )
            (shapeNP @a @xs)
            pureExpNP
     in Exp_Sqlite $ do
          case recConNP of
            (K firstColAct :* rest) -> do
              firstCol <- firstColAct
              restCols <- sequenceA $ hcollapse rest
              return (SRecCon (firstCol NE.:| restCols))

type OneCol =
  ReaderT
    Int
    (Except Text)
    (ColumnAlias, SqliteExpRepr)

data FooRec = FooRec {fieldA :: Int, fieldB :: Bool}
  deriving (GHC.Generics.Generic)

instance Generic FooRec

instance HasDatatypeInfo FooRec

instance Shaped FooRec

instance ConstructExp Sqlite FooRec

instance ProjectExp Sqlite FooRec

type ColumnsSoFar =
  ReaderT
    Int
    (Except Text)
    (NonEmpty (ColumnAlias, SqliteExpRepr))

class ParseExpSqlite a where
  expSqliteRowParser :: Sqlite.RowParser a
  default expSqliteRowParser :: (GParseExpSqlite a) => Sqlite.RowParser a
  expSqliteRowParser = gExpSqliteRowParser

class GParseExpSqlite a where
  gExpSqliteRowParser :: Sqlite.RowParser a

instance
  ( Code a ~ '[xs],
    Generic a,
    Generics.SOP.All ParseExpSqlite xs
  ) =>
  GParseExpSqlite a
  where
  gExpSqliteRowParser = do
    let parsers :: NP (Sqlite.RowParser :.: I) xs
        parsers = hcpure (Proxy @ParseExpSqlite) (Comp (I <$> expSqliteRowParser))

    parsed :: NP I xs <- hsequence' parsers

    let res = to @a (SOP (Z parsed))

    return res

instance ParseExpSqlite Int where
  expSqliteRowParser = field

instance ParseExpSqlite (Fixed n) where
  expSqliteRowParser = field

instance FromField (Fixed n) where
  fromField :: forall n. FieldParser (Fixed n)
  fromField f = MkFixed <$> fromField f -- Hmm..

instance ToField (Fixed n) where
  toField :: forall n. Fixed n -> SQLData
  toField (MkFixed f) = toField f -- Hmm

instance ParseExpSqlite Bool where
  expSqliteRowParser = field

instance ParseExpSqlite Text where
  expSqliteRowParser = field

instance (ParseExpSqlite a, ParseExpSqlite b) => ParseExpSqlite (a, b) where
  expSqliteRowParser = (,) <$> expSqliteRowParser <*> expSqliteRowParser

instance (PureExp Sqlite a, PureExp Sqlite b) => PureExp Sqlite (a, b)

instance (Shaped a, Shaped b) => Shaped (a, b)

instance ToField UUID where
  toField = Sqlite.SQLText . Data.UUID.toText

toFieldViaShow :: (Show a) => a -> SQLData
toFieldViaShow = Sqlite.SQLText . T.pack . show

instance FromField UUID where
  fromField field = case Sqlite.fieldData field of
    Sqlite.SQLText t -> case Data.UUID.fromText t of
      Nothing -> returnError ConversionFailed field "Field was text, but not in valid uuid format"
      Just uuid -> Ok uuid
    _ -> returnError ConversionFailed field "Field was not text"

fromFieldViaRead :: (Typeable a) => (Read a) => FieldParser a
fromFieldViaRead field = case Sqlite.fieldData field of
  Sqlite.SQLText t -> case readMaybe (T.unpack t) of
    Nothing -> returnError ConversionFailed field "Field was text, but not in valid format"
    Just parsed -> Ok parsed
  _ -> returnError ConversionFailed field "Field was not text"

data UnsafeArgument = forall a. UnsafeArgument (Exp Sqlite a)

unsafeArgument :: forall a. Exp Sqlite a -> UnsafeArgument
unsafeArgument = UnsafeArgument

unsafeFunApp :: forall a. Text -> [UnsafeArgument] -> Exp Sqlite a
unsafeFunApp funName args = Exp_Sqlite $ do
  argsRepr <-
    traverse
      ( \(UnsafeArgument (Exp_Sqlite argExp)) -> argExp
      )
      args

  return (SPrimFunApp funName argsRepr)

instance Relational Sqlite where
  data Relation Sqlite a = Relation_Sqlite
    { unRelation_Sqlite ::
        ReaderT
          Int
          (Except Text)
          SqliteRelationRepr
    }

  data Exp Sqlite a = Exp_Sqlite
    { unExp_Sqlite ::
        ReaderT
          Int
          (Except Text)
          SqliteExpRepr
    }

  (*:) :: Exp Sqlite a -> Exp Sqlite b -> Exp Sqlite (a, b)
  (*:) (Exp_Sqlite e1') (Exp_Sqlite e2') = Exp_Sqlite do
    e1 <- e1'
    e2 <- e2'
    return (SRecCon (("_1", e1) NE.:| [("_2", e2)]))

  exp_fst (Exp_Sqlite ePair') = Exp_Sqlite $ do
    ePair <- ePair'
    return (sRecProj ePair "_1")

  exp_snd (Exp_Sqlite ePair') = Exp_Sqlite $ do
    ePair <- ePair'
    let res = sRecProj ePair "_2"
    {-trace ("exp_snd\n" <>
      "  ePair=" <> show ePair <> "\n" <>
      "  res=" <> show res <> "\n\n"
      ) $-}
    return res

  rel_union :: NonEmpty (Relation Sqlite a) -> Relation Sqlite a
  rel_union (Relation_Sqlite rel' :| rels') = Relation_Sqlite do
    rel <- rel'
    rels <- traverse unRelation_Sqlite rels'
    return $ SRelUnion (relationReprShape rel) (rel :| rels)

  rel_project :: (Exp Sqlite a -> Exp Sqlite b) -> Relation Sqlite a -> Relation Sqlite b
  rel_project projF (Relation_Sqlite rel') = Relation_Sqlite $ do
    rel <- rel'
    withScope "project" \t -> do
      let inputShape = relationReprShape rel
          inputShapeProjExp = shapeExpRepr t inputShape
      projExp <-
        unExp_Sqlite $
          projF $
            Exp_Sqlite $
              return (shapeExpRepr t (relationReprShape rel))
      projNorm <- normalizeExp projExp
      let projRel = case projNorm of
            Left exp ->
              SRelProject shapeOne (unquoteRecRepr (oneRec exp) t) rel
            Right r ->
              let shape = expReprShape projExp
               in {-trace ("rel_project\n" <>
                          "  projExp=" <> show projExp <> "\n" <>
                          "  inputShape=" <> show inputShape <> "\n" <>
                          "  inputShapeProjExp=" <> show inputShapeProjExp <> "\n" <>
                          "  shape=" <> show shape <> "\n" <>
                          "  r=" <> show r <> "\n") $-}
                  SRelProject shape (unquoteRecRepr r t) rel
      return projRel

  rel_cross relA' relB' = Relation_Sqlite do
    relA <- unRelation_Sqlite relA'
    relB <- unRelation_Sqlite relB'
    crossRepr <- withScope "crossA" \t1 -> withScope "crossB" \t2 -> do
      let projA = Exp_Sqlite $ return (shapeExpRepr t1 (relationReprShape relA))
          projB = Exp_Sqlite $ return (shapeExpRepr t2 (relationReprShape relB))
          bothExp = projA *: projB
      unExp_Sqlite bothExp

    let crossShape = expReprShape crossRepr
    return
      ( -- trace ("rel_cross\n  crossRepr=" <> show crossRepr <> "\n  crossShape=" <> show crossShape) $
        SRelCross crossShape relA relB
      )

  rel_restrict predF rel' = Relation_Sqlite $ do
    rel <- unRelation_Sqlite rel'

    -- (relSql, _preparedArgsMap) <- lift $ flip runReaderT 0 $ flip runStateT mempty $ sqlRelQuote rel
    -- let queryStr = ppSql (SqlStatementsSingle relSql)
    -- trace (T.unpack queryStr) (return ())

    withScope "restrict" \x -> do
      predExp <- unExp_Sqlite $ predF $ Exp_Sqlite $ return $ shapeExpRepr x (relationReprShape rel)
      -- trace (show predExp) $ return ()
      predNorm <- normalizeExp predExp
      case predNorm of
        Left filter -> return (SRelRestrict (unquoteExpRepr filter x) rel)
        Right r -> throwError $ "rel_restrict: Expected expression, but got record '" <> T.pack (show r) <> "'"

instance RelationalMinus Sqlite a where
  rel_minus relA' relB' = Relation_Sqlite do
    relA <- unRelation_Sqlite relA'
    relB <- unRelation_Sqlite relB'
    return $ SRelExcept (relationReprShape relA) relA relB

instance RelationalView Sqlite where
  data View Sqlite a = View_Sqlite String (Relation Sqlite a)

  rel_view :: String -> Relation Sqlite a -> View Sqlite a
  rel_view = View_Sqlite

  view_rel :: View Sqlite a -> Relation Sqlite a
  view_rel (View_Sqlite viewName (Relation_Sqlite rel')) = Relation_Sqlite do
    rel <- rel'
    let relShape = relationReprShape rel
    return (SRelTable relShape (Data.Text.pack viewName))

  declare_view :: (TransactionalConstraints Sqlite m) => View Sqlite a -> TransactionT Sqlite m ()
  declare_view (View_Sqlite name (Relation_Sqlite rel')) = TransactionT_Sqlite $ do
    rel <- lift $ mapExceptT (pure . runIdentity) $ runReaderT rel' 0
    relSql <- lift $ flip runReaderT 0 $ unQuoteWithInlining $ sqlRelQuote rel
    let queryStr =
          Data.Text.concat
            [ "CREATE VIEW ",
              Data.Text.pack name,
              " AS ",
              ppSql relSql
            ]

    -- Sigh. We need to supply more kit with 'Sqlite.Internal' stuff because there is no 'queryNamedWith' function that can take an explicit 'RowParser'.
    TransactionEnv {transactionEnvConnection = conn} <- ask

    transactionIO
      $ Sqlite.execute_ conn (Sqlite.Query queryStr)

instance RelationalAggregate Sqlite where
  newtype AggExp Sqlite expA expB = AggExp_Sqlite
    { unAggExp_Sqlite ::
        expA ->
        Writer [ReaderT Int (Except Text) SqliteExpRepr] expB
    }

  rel_aggregate (AggExp_Sqlite aggF) (Relation_Sqlite rel') = Relation_Sqlite $ do
    rel <- rel'
    withScope "project" \t -> do
      let inputShape = relationReprShape rel
          inputShapeProjExp = shapeExpRepr t inputShape
      (projExp, groupExp) <- do
        let (x, groupsAction) =
              runWriter $
                aggF $
                  Exp_Sqlite $
                    return inputShapeProjExp
        res <- unExp_Sqlite x
        groups <- sequenceA groupsAction
        return (res, groups)
      projNorm <- normalizeExp projExp
      groupNorm :: [NormSqliteExpRepr] <- concat <$> traverse (fmap flattenGroupExp . normalizeExp) groupExp
      let (shape, projExpUnQ) = case projNorm of
            Left exp -> (shapeOne, unquoteRecRepr (oneRec exp) t)
            Right r -> (expReprShape projExp, unquoteRecRepr r t)
          projGroupExpUnQ = do
            projExpUnQ' <- projExpUnQ
            groupNormExpQ <- mapM (`unquoteExpRepr` t) groupNorm
            return (projExpUnQ', groupNormExpQ)
          projRel = SRelAggregate shape projGroupExpUnQ rel

      return projRel

  group_by = AggExp_Sqlite \exp1 -> do
    tell [unExp_Sqlite exp1]
    return exp1

  count = AggExp_Sqlite $ \x -> return $ unsafeFunApp "count" [unsafeArgument x]

instance AggregateNum Sqlite Int where
  maximum = AggExp_Sqlite $ \x -> return $ unsafeFunApp "max" [unsafeArgument x]
  sum = AggExp_Sqlite $ \x ->
    return $
      unsafeFunApp
        "coalesce"
        [ unsafeArgument $ unsafeFunApp "sum" [unsafeArgument x],
          unsafeArgument (pureExp (0 :: Int))
        ]

instance AggregateNum Sqlite (Fixed n) where
  maximum = AggExp_Sqlite $ \x -> return $ unsafeFunApp "max" [unsafeArgument x]
  sum = AggExp_Sqlite $ \x -> return $ unsafeFunApp "sum" [unsafeArgument x]

instance AggregateNum Sqlite Double where
  maximum = AggExp_Sqlite $ \x -> return $ unsafeFunApp "max" [unsafeArgument x]
  sum = AggExp_Sqlite $ \x -> return $ unsafeFunApp "sum" [unsafeArgument x]

instance AggregateNum Sqlite UTCTime where
  maximum = AggExp_Sqlite $ \x -> return $ unsafeFunApp "max" [unsafeArgument x]

  -- This is absolutely nonsensical :-/
  sum = AggExp_Sqlite $ \x -> return $ unsafeFunApp "sum" [unsafeArgument x]

flattenGroupExp :: Either NormSqliteExpRepr NormSqliteRecRepr -> [NormSqliteExpRepr]
flattenGroupExp (Left exp) = [exp]
flattenGroupExp (Right (NSRecCon recs)) = map snd recs

instance Functor (AggExp Sqlite a) where
  fmap = rmap

instance Applicative (AggExp Sqlite a) where
  pure = AggExp_Sqlite . const . return
  (AggExp_Sqlite fAgg) <*> (AggExp_Sqlite xAgg) = AggExp_Sqlite ((<*>) <$> fAgg <*> xAgg)

instance Profunctor (AggExp Sqlite) where
  lmap f = AggExp_Sqlite . lmap f . unAggExp_Sqlite
  rmap f = AggExp_Sqlite . rmap (fmap f) . unAggExp_Sqlite

shapeOne :: Shape
shapeOne = ShapeScalarField

-- | From a shape, derive an expression that projects all fields as they are represented.
shapeExpRepr :: TableAlias -> Shape -> SqliteExpRepr
shapeExpRepr t = withShape (sRecProj (SPrimVar t) "scalar") (sRecProj (SPrimVar t)) SRecCon

-- | Decide the 'Shape' of an expression.
-- This function assumes that all record projections only ever reference scalar
-- fields, such as those produced by 'shapeExpRepr'.
--
-- TODO: This might go away now that we have 'class Shaped'?
expReprShape :: SqliteExpRepr -> Shape
expReprShape exp = case exp of
  SRecCon cols -> ShapeRecord (fmap (second expReprShape) cols)
  _ -> ShapeScalarField

instance (Shaped a) => RelationalLiteral Sqlite a where
  rel_literal :: [Exp Sqlite a] -> Relation Sqlite a
  rel_literal rowsExp = Relation_Sqlite do
    rows <- for rowsExp \(Exp_Sqlite expAction) -> do
      exp <- expAction
      normExp <- normalizeExp exp
      return $ either oneRec id normExp
    let shape = shaped (Proxy @a)
    return (SRelLiteral shape rows)

instance Tabular Sqlite where
  data Table Sqlite select insert
    = Table_Sqlite (ReaderT Int (Except Text) (Text, Shape))

  table (Table_Sqlite tableAct) = Relation_Sqlite $ do
    (tableName, shape) <- tableAct
    return (SRelTable shape tableName)

instance MonadTrans (TransactionT Sqlite) where
  lift = TransactionT_Sqlite . lift . lift

instance (MonadIO m) => MonadIO (TransactionT Sqlite m) where
  liftIO = lift . liftIO

data TransactionEnv = TransactionEnv
  { transactionEnvConnection :: Sqlite.Connection
  }

instance Transactional Sqlite where
  newtype TransactionT Sqlite m a = TransactionT_Sqlite
    { runTransactionT_Sqlite :: ReaderT TransactionEnv (ExceptT Text m) a
    }
    deriving newtype (Functor, Applicative, Monad)

  type RelationalOutput Sqlite = ParseExpSqlite

  type TransactionalConstraints Sqlite = MonadIO

  query ::
    forall m a.
    ( ParseExpSqlite a,
      TransactionalConstraints Sqlite m
    ) =>
    Relation Sqlite a ->
    TransactionT Sqlite m [a]
  query (Relation_Sqlite rel') = TransactionT_Sqlite do
    rel <- lift $ mapExceptT (pure . runIdentity) $ runReaderT rel' 0
    (relSql, preparedArgsMap) <- lift $ flip runReaderT 0 $ flip runStateT mempty $ unQuoteWithPreparedArgs $ sqlRelQuote rel
    let queryStr = ppSql relSql
        preparedArgs = map (\(ix, value) -> T.pack (":a" <> show ix) := value) (IntMap.toList preparedArgsMap)

    -- Sigh. We need to supply more kit with 'Sqlite.Internal' stuff because there is no 'queryNamedWith' function that can take an explicit 'RowParser'.
    TransactionEnv {transactionEnvConnection = conn} <- ask

    rows :: [[SQLData]] <-
      transactionIO
        $ Sqlite.queryNamed conn (Sqlite.Query queryStr) preparedArgs
    traverse
      ( runRowParser (expSqliteRowParser @a)
      )
      rows
    where
      runRowParser :: forall m a. (MonadError Text m) => RowParser a -> [SQLData] -> m a
      runRowParser parser sqlDatas = do
        let parserResult =
              flip Sqlite.StateT.evalStateT (0, sqlDatas) $
                flip runReaderT (Sqlite.Internal.RowParseRO (length sqlDatas)) $
                  Sqlite.Internal.unRP parser

        case parserResult of
          Errors exns -> throwError $ T.unlines (map (T.pack . displayException) exns)
          Ok a -> return a

  insert
    (Table_Sqlite tableAct)
    (Relation_Sqlite valuesRel) = TransactionT_Sqlite do
      (tableName, _shape) <- lift $ mapExceptT (pure . runIdentity) $ runReaderT tableAct 0
      rel <- lift $ mapExceptT (pure . runIdentity) $ runReaderT valuesRel 0
      (relSql, preparedArgsMap) <- lift $ flip runReaderT 0 $ flip runStateT mempty $ unQuoteWithPreparedArgs $ sqlRelQuote rel
      let queryStr = ppSql relSql
          preparedArgs = map (\(ix, value) -> T.pack (":a" <> show ix) := value) (IntMap.toList preparedArgsMap)

      let insertStatement = "INSERT INTO " <> ppIdentifierQuote tableName <> " " <> queryStr

      TransactionEnv {transactionEnvConnection = conn} <- ask
      transactionIO
        $ Sqlite.executeNamed conn (Sqlite.Query insertStatement) preparedArgs

-- Bothersome catching of IO errors in TransactionT_Sqlite.
transactionIO :: (MonadIO m) => IO a -> ReaderT TransactionEnv (ExceptT Text m) a
transactionIO x =
  lift $
    withExceptT (Data.Text.pack . show @SomeException) $
      ExceptT $
        liftIO $
          try x

runTransactionT ::
  (Monad m, MonadIO m, MonadUnliftIO m) =>
  TransactionT Sqlite m a ->
  ReaderT TransactionEnv (ExceptT Text m) a
runTransactionT x = do
  TransactionEnv {transactionEnvConnection = conn} <- ask
  res <-
    catchError
      ( do
          liftIO $ Sqlite.execute conn (Sqlite.Query "BEGIN TRANSACTION") ()
          runTransactionT_Sqlite x
      )
      ( \e -> do
          liftIO $ Sqlite.execute conn (Sqlite.Query "ROLLBACK") ()
          throwError e
      )
  liftIO $ Sqlite.execute conn (Sqlite.Query "COMMIT TRANSACTION") ()
  return res

sqliteTableDecl ::
  forall select insert.
  (Shaped select) =>
  TableName ->
  Table Sqlite select insert
sqliteTableDecl tableName = Table_Sqlite $ do
  return (tableName, shaped (Proxy @select))

ppRel :: Relation Sqlite a -> Text
ppRel rel = either id id $ runExcept $ do
  exp <- flip runReaderT 0 $ unRelation_Sqlite rel
  relSql <- flip runReaderT 0 $ unQuoteWithInlining $ sqlRelQuote exp
  return $ ppSql relSql

unsafeEqApp :: (ParseExpSqlite Bool) => Exp Sqlite a -> Exp Sqlite a -> Exp Sqlite Bool
unsafeEqApp = unsafeBinopApp "="

unsafeBinopApp :: (ParseExpSqlite c) => Text -> Exp Sqlite a -> Exp Sqlite b -> Exp Sqlite c
unsafeBinopApp binop aExp bExp = unsafeFunApp binop [unsafeArgument aExp, unsafeArgument bExp]

-- In Sqlite, anything that can go into an Exp can be compared for equality.
instance EqOp Sqlite a where
  (.==) = unsafeEqApp

instance OrdOp Sqlite Double where
  (.>) = unsafeBinopApp ">"
  (.>=) = unsafeBinopApp ">="

instance OrdOp Sqlite (Fixed n) where
  (.>) = unsafeBinopApp ">"
  (.>=) = unsafeBinopApp ">="

instance BoolOps Sqlite where
  (.||) :: Exp Sqlite Bool -> Exp Sqlite Bool -> Exp Sqlite Bool
  (.||) = unsafeBinopApp "or"
  (.&&) :: Exp Sqlite Bool -> Exp Sqlite Bool -> Exp Sqlite Bool
  (.&&) = unsafeBinopApp "and"

  bool_elim falseExp trueExp condExp = Exp_Sqlite do
    false <- unExp_Sqlite falseExp
    true <- unExp_Sqlite trueExp
    cond <- unExp_Sqlite condExp
    return $ SPrimCase cond [(SPrimSqlData (SQLInteger 0), false), (SPrimSqlData (SQLInteger 1), true)]

test :: IO ()
test = do
  describe "Record Expressions" $ do
    it "Single fields have shape 'shapeOne'" $ do
      let rel = rel_literal @Sqlite [pureExp ("hey" :: String)]
          Right relRepr = runExcept $ flip runReaderT 0 $ unRelation_Sqlite rel

      relationReprShape relRepr `shouldBe` shapeOne

    it "Pairs have shape (_1,_2)" $ do
      let rel = rel_literal @Sqlite [pureExp ("hey", "ho")]
          Right relRepr = runExcept $ flip runReaderT 0 $ unRelation_Sqlite rel

      relationReprShape relRepr `shouldBe` ShapeRecord (NE.fromList [("_1", ShapeScalarField), ("_2", ShapeScalarField)])

    it "We can construct field projections" $ do
      let exp = pureExp ("hey", "ho")
          Right expRepr = runExcept $ flip runReaderT 0 $ unExp_Sqlite exp

          expShape = expReprShape expRepr
          expProj = shapeExpRepr "t" expShape

      expProj `shouldBe` SRecCon (("_1", sRecProj (SPrimVar "t") "_1") NE.:| [("_2", sRecProj (SPrimVar "t") "_2")])

    it "Projecting all fields is idempotent" $ do
      let pairExp = pureExp ("hey", "ho")
          Right pairRepr = runExcept $ flip runReaderT 0 $ unExp_Sqlite pairExp
          pairShape = expReprShape pairRepr

          reconExp pair = exp_fst pair *: exp_snd pair
          expProj = shapeExpRepr "t" pairShape

          Right reconRepr =
            runExcept $
              flip runReaderT 0 $
                unExp_Sqlite $
                  reconExp $
                    Exp_Sqlite $
                      return expProj
          Right projNorm = runExcept $ normalizeExp reconRepr

      projNorm `shouldBe` Right (NSRecCon [("_1", NSRecProj "t" "_1"), ("_2", NSRecProj "t" "_2")])

  describe "Relation constructors" $ do
    it "Empty relations have the expected shape" $ do
      let rel = rel_literal @Sqlite @(((String, Int), (String, Int)), Int) []
          Right relRepr = runExcept $ flip runReaderT 0 $ unRelation_Sqlite rel

      relationReprShape relRepr
        `shouldBe` ShapeRecord
          ( ( "_1",
              ShapeRecord
                ( ( "_1",
                    ShapeRecord (("_1", ShapeScalarField) NE.:| [("_2", ShapeScalarField)])
                  )
                    NE.:| [("_2", ShapeRecord (("_1", ShapeScalarField) NE.:| [("_2", ShapeScalarField)]))]
                )
            )
              NE.:| [("_2", ShapeScalarField)]
          )

    it "Empty relations have the expected shape" $ do
      let rel = rel_literal @Sqlite @TestRecNest []
          Right relRepr = runExcept $ flip runReaderT 0 $ unRelation_Sqlite rel

      -- trace (show relRepr) (return ())

      relationReprShape relRepr
        `shouldBe` ShapeRecord
          ( ( "nest1",
              ShapeRecord (("flat1", ShapeScalarField) NE.:| [("flat2", ShapeScalarField)])
            )
              NE.:| [("nest2", ShapeScalarField)]
          )

  describe "Exp embedding" $ do
    it "embedRecExp, appRec produce expected shape, scalars" do
      let recExp = pureExp (TestRecFlat 1 "hey")
          Right recRepr = runExcept $ flip runReaderT 0 $ unExp_Sqlite recExp

      expReprShape recRepr `shouldBe` ShapeRecord (("flat1", ShapeScalarField) NE.:| [("flat2", ShapeScalarField)])

    it "embedRecExp, appRec produce expected shape, nested" do
      let recExp = pureExp (TestRecNest (TestRecFlat 1 "hey") "ho")
          Right recRepr = runExcept $ flip runReaderT 0 $ unExp_Sqlite recExp

      expReprShape recRepr
        `shouldBe` ShapeRecord
          ( ("nest1", ShapeRecord (("flat1", ShapeScalarField) NE.:| [("flat2", ShapeScalarField)]))
              NE.:| [("nest2", ShapeScalarField)]
          )

  describe "bool_elim" $ do
    it "works for scalars" do
      conn <- Sqlite.open ":memory:"
      Sqlite.execute_ conn "CREATE TABLE foo (_1 int primary key, _2 int)"

      let fooTable :: Table Sqlite (Int, Int) (Int, Int) = sqliteTableDecl "foo"

      res <-
        runExceptT $
          flip runReaderT (TransactionEnv conn) $
            runTransactionT $
              insert
                fooTable
                ( rel_literal $
                    map
                      pureExp
                      [ (0, 1),
                        (1, 2)
                      ]
                )
      case res of
        Left er -> error (T.unpack er)
        Right () -> return ()

      res <-
        runExceptT $
          flip runReaderT (TransactionEnv conn) $
            runTransactionT $
              query $
                rel_project
                  ( \foo ->
                      bool_elim
                        (pureExp "neq 1")
                        (pureExp "eq 1")
                        (exp_fst foo .== pureExp 1)
                  )
                  (table fooTable)

      case res of
        Left er -> error (T.unpack er)
        Right res ->
          res
            `shouldBe` [ "neq 1" :: Text,
                         "eq 1"
                       ]

    it "works for records results" do
      conn <- Sqlite.open ":memory:"
      Sqlite.execute_ conn "CREATE TABLE foo (_1 int primary key, _2 int)"

      let fooTable :: Table Sqlite (Int, Int) (Int, Int) = sqliteTableDecl "foo"

      res <-
        runExceptT $
          flip runReaderT (TransactionEnv conn) $
            runTransactionT $
              insert
                fooTable
                ( rel_literal $
                    map
                      pureExp
                      [ (0, 1),
                        (1, 2)
                      ]
                )
      case res of
        Left er -> error (T.unpack er)
        Right () -> return ()

      res <-
        runExceptT $
          flip runReaderT (TransactionEnv conn) $
            runTransactionT $
              query $
                rel_project
                  ( \foo ->
                      bool_elim
                        (pureExp (100, 100))
                        foo
                        (exp_fst foo .== pureExp 1)
                  )
                  (table fooTable)

      case res of
        Left er -> error (T.unpack er)
        Right res ->
          res
            `shouldBe` [ (100, 100),
                         (1, 2)
                       ]

    it "works for record conditions" do
      conn <- Sqlite.open ":memory:"
      Sqlite.execute_ conn "CREATE TABLE foo (_1 int primary key, _2 int)"

      let fooTable :: Table Sqlite (Int, Int) (Int, Int) = sqliteTableDecl "foo"

      res <-
        runExceptT $
          flip runReaderT (TransactionEnv conn) $
            runTransactionT $
              insert
                fooTable
                ( rel_literal $
                    map
                      pureExp
                      [ (0, 1),
                        (1, 2)
                      ]
                )
      case res of
        Left er -> error (T.unpack er)
        Right () -> return ()

      res <-
        runExceptT $
          flip runReaderT (TransactionEnv conn) $
            runTransactionT $
              query $
                rel_project
                  ( \foo ->
                      bool_elim
                        (pureExp "false case")
                        (pureExp "true case")
                        (foo .== pureExp (1, 2))
                  )
                  (table fooTable)

      case res of
        Left er -> error (T.unpack er)
        Right res ->
          res
            `shouldBe` [ "false case" :: Text,
                         "true case"
                       ]

    it "can produce row-value arguments" do
      conn <- Sqlite.open ":memory:"
      Sqlite.execute_ conn "CREATE TABLE foo (_1 int primary key, _2 int)"

      let fooTable :: Table Sqlite (Int, Int) (Int, Int) = sqliteTableDecl "foo"

      res <-
        runExceptT $
          flip runReaderT (TransactionEnv conn) $
            runTransactionT $
              insert
                fooTable
                ( rel_literal $
                    map
                      pureExp
                      [ (0, 1),
                        (1, 2)
                      ]
                )
      case res of
        Left er -> error (T.unpack er)
        Right () -> return ()

      res <-
        runExceptT $
          flip runReaderT (TransactionEnv conn) $
            runTransactionT $
              query $
                rel_project
                  ( \foo ->
                      bool_elim
                        (pureExp (10 :: Int, 20 :: Int))
                        foo
                        (foo .== pureExp (1, 2))
                        .== pureExp (10, 20)
                  )
                  (table fooTable)

      case res of
        Left er -> error (T.unpack er)
        Right res ->
          res
            `shouldBe` [ True,
                         False
                       ]

  describe "Aggregation" $ do
    it "can group" do
      conn <- Sqlite.open ":memory:"
      Sqlite.execute_ conn "CREATE TABLE foo (_1 int primary key, _2 int)"

      let fooTable :: Table Sqlite (Int, Int) (Int, Int) = sqliteTableDecl "foo"

      res <-
        runExceptT $
          flip runReaderT (TransactionEnv conn) $
            runTransactionT $
              insert
                fooTable
                ( rel_literal $
                    map
                      pureExp
                      [ (0, 1),
                        (1, 2),
                        (2, 2),
                        (3, 2)
                      ]
                )
      case res of
        Left er -> error (T.unpack er)
        Right () -> return ()

      let groupQuery =
            rel_aggregate
              (lmap exp_snd group_by)
              (table fooTable)

      groups <-
        runExceptT $
          flip runReaderT (TransactionEnv conn) $
            runTransactionT $
              query
                groupQuery

      case groups of
        Left er -> error (T.unpack er)
        Right groups ->
          groups
            `shouldBe` [ 1,
                         2
                       ]

    it "can count" do
      conn <- Sqlite.open ":memory:"
      Sqlite.execute_ conn "CREATE TABLE foo (_1 int primary key, _2 int)"

      let fooTable :: Table Sqlite (Int, Int) (Int, Int) = sqliteTableDecl "foo"

      res <-
        runExceptT $
          flip runReaderT (TransactionEnv conn) $
            runTransactionT $
              insert
                fooTable
                ( rel_literal $
                    map
                      pureExp
                      [ (0, 1),
                        (1, 2),
                        (2, 2),
                        (3, 3),
                        (4, 3),
                        (5, 3)
                      ]
                )
      case res of
        Left er -> error (T.unpack er)
        Right () -> return ()

      let countQuery =
            rel_aggregate
              ( (\count group max -> group *: (count *: max))
                  <$> lmap exp_fst count
                  <*> lmap exp_snd group_by
                  <*> lmap exp_fst maximum
              )
              (table fooTable)

      counts <-
        runExceptT $
          flip runReaderT (TransactionEnv conn) $
            runTransactionT $
              query
                countQuery

      case counts of
        Left er -> error (T.unpack er)
        Right counts ->
          counts
            `shouldBe` [ (1, (1, 0)),
                         (2, (2, 2)),
                         (3, (3, 5))
                       ]

data TestRecFlat = TestRecFlat
  { testRecFlat1 :: Int,
    testRecFlat2 :: String
  }
  deriving (GHC.Generics.Generic)

instance Generic TestRecFlat

instance HasDatatypeInfo TestRecFlat

instance Shaped TestRecFlat

instance PureExp Sqlite TestRecFlat

instance ProjectExp Sqlite TestRecFlat

instance ConstructExp Sqlite TestRecFlat

data TestRecNest = TestRecNest
  { testRecNest1 :: TestRecFlat,
    testRecNest2 :: String
  }
  deriving (GHC.Generics.Generic)

instance Generic TestRecNest

instance HasDatatypeInfo TestRecNest

instance Shaped TestRecNest

instance PureExp Sqlite TestRecNest

instance ProjectExp Sqlite TestRecNest

instance ConstructExp Sqlite TestRecNest

relationalRecordInstances :: Name -> Q [Dec]
relationalRecordInstances subjectTypeName = do
  [d|
    instance Shaped $(return $ ConT subjectTypeName)

    instance ParseExpSqlite $(return $ ConT subjectTypeName)
    |]

relationalFieldInstances :: Name -> Q [Dec]
relationalFieldInstances subjectTypeName = do
  let subjectType = ConT subjectTypeName
  info <- reify subjectTypeName

  -- We only try to derive FromField/ToField instances for newtypes.
  fromFieldInstances <- case info of
    TyConI NewtypeD {} -> do
      [d|
        deriving newtype instance FromField $(return subjectType)

        deriving newtype instance ToField $(return subjectType)
        |]
    _ -> return []

  otherInstances <-
    [d|
      instance PureExp Sqlite $(return $ ConT subjectTypeName) where
        pureExp = pureExpField

      instance Shaped $(return subjectType) where
        shaped _ = shapeOne

      instance ParseExpSqlite $(return subjectType) where
        expSqliteRowParser = field
      |]

  return $ fromFieldInstances ++ otherInstances
