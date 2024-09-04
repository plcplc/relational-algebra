{-# OPTIONS_GHC -Wincomplete-patterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# LANGUAGE UndecidableInstances #-}

module Relational.Sqlite.Internal
  ( module Relational.Sqlite.Internal,
  )
where

import Control.Exception
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.State.Strict qualified as Sqlite.StateT
import Data.Bifunctor
import Data.Either
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Maybe
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Traversable
import Database.SQLite.Simple as Sqlite
import Database.SQLite.Simple.FromField as Sqlite
import Database.SQLite.Simple.FromRow as Sqlite
import Database.SQLite.Simple.Internal qualified as Sqlite.Internal
import Database.SQLite.Simple.Ok as Sqlite
import Database.SQLite.Simple.ToField as Sqlite
import Debug.Trace
import Relational.Class

data SqlStatementQuote
  = SqlSelect
      { sqlSelectFrom :: [SqlFromQuote],
        sqlSelectProj :: SqlProjectionsQuote,
        sqlSelectWhere :: [SqlExpressionQuote],
        sqlSelectGroupBy :: [SqlExpressionQuote],
        sqlSelectLimit :: Maybe Int
      }
  | SqlValues [[SqlExpressionQuote]]
  | SqlUnionAll (NonEmpty SqlStatementQuote)
  | SqlExcept SqlStatementQuote SqlStatementQuote
  deriving (Show)

-- Smart constructor for SELECT which only requires a projection and leaves sub-clauses empty.
sqlSelect :: SqlProjectionsQuote -> SqlStatementQuote
sqlSelect projQ = SqlSelect [] projQ [] [] Nothing

data SqlFromQuote
  = SqlFromTable Text
  | SqlFromTableAliased Text Text
  | -- Non-normalized, nested query:
    SqlFromStatement SqlStatementQuote Text
  deriving (Show)

data SqlProjectionsQuote
  = SqlProjectionsAliased [(ColumnAlias, SqlExpressionQuote)]
  | SqlProjectionColumns TableName [ColumnAlias]
  | SqlProjectionStar TableName
  deriving (Show)

data SqlExpressionQuote
  = SqlExpBool Bool
  | SqlExpFunApp Text [SqlExpressionQuote]
  | SqlExpInt Int
  | SqlExpFloat Double
  | SqlExpNull
  | SqlExpOpApp Text SqlExpressionQuote SqlExpressionQuote
  | SqlExpProj Text Text
  | SqlExpText Text
  | SqlExpPreparedArg Text
  | SqlExpCase SqlExpressionQuote [(SqlExpressionQuote, SqlExpressionQuote)]
  | -- Sqlite row walues:  https://www.sqlite.org/rowvalue.html
    SqlExpRow [SqlExpressionQuote]
  deriving (Show)

ppSql :: SqlStatementQuote -> Text
ppSql = ppSqlStatementQuote 0

ppSqlStatementQuote :: Int -> SqlStatementQuote -> Text
ppSqlStatementQuote prec (SqlUnionAll (s1 :| [])) = ppSqlStatementQuote prec s1
ppSqlStatementQuote prec (SqlUnionAll (s1 :| (s2 : ss))) =
  parenIndent
    prec
    0
    ( ppSqlStatementQuote 0 s1
        <> "UNION ALL\n"
        <> ppSqlStatementQuote 0 (SqlUnionAll (s2 :| ss))
    )
ppSqlStatementQuote
  prec
  SqlSelect
    { sqlSelectFrom = froms,
      sqlSelectProj = projs,
      sqlSelectWhere = conds,
      sqlSelectGroupBy = groupBy
    } =
    parenIndent
      prec
      0
      ( "SELECT\n"
          <> indent 2 (ppSqlProjectionsQuote projs)
          <> ( if not . null $ froms
                 then
                   "FROM\n"
                     <> indent 2 (T.intercalate ",\n" (map ppSqlFromQuote froms))
                 else ""
             )
          <> ( if not . null $ conds
                 then "WHERE\n" <> indent 2 (T.intercalate " AND " (map (ppSqlExpressionQuote 0) conds))
                 else ""
             )
          <> ( if not . null $ groupBy
                 then "GROUP BY\n" <> indent 2 (T.intercalate ",\n" (map (ppSqlExpressionQuote 0) groupBy))
                 else ""
             )
      )
ppSqlStatementQuote
  prec
  (SqlValues vals) =
    parenIndent
      prec
      0
      ( "VALUES\n"
          <> indent
            2
            ( T.intercalate
                ",\n"
                ["(" <> T.intercalate ", " (map (ppSqlExpressionQuote 0) row) <> ")" | row <- vals]
            )
      )
ppSqlStatementQuote prec (SqlExcept s1 s2) =
  parenIndent
    prec
    0
    ( ppSqlStatementQuote 0 s1
        <> "EXCEPT\n"
        <> ppSqlStatementQuote 0 s2
    )

ppSqlExpressionQuote :: Int -> SqlExpressionQuote -> Text
ppSqlExpressionQuote prec = \case
  SqlExpBool b -> T.pack $ show b
  SqlExpFunApp fn args -> fn <> "(" <> T.intercalate ", " (map (ppSqlExpressionQuote 1) args) <> ")"
  SqlExpInt i -> T.pack $ show i
  SqlExpFloat f -> T.pack $ show f
  SqlExpNull -> "NULL"
  SqlExpOpApp "+" x y -> paren prec 0 (ppSqlExpressionQuote 0 x <> " + " <> ppSqlExpressionQuote 0 y)
  SqlExpOpApp "*" x y -> paren prec 1 (ppSqlExpressionQuote 1 x <> " * " <> ppSqlExpressionQuote 1 y)
  SqlExpOpApp op x y -> ppSqlExpressionQuote 1 x <> " " <> op <> " " <> ppSqlExpressionQuote 1 y
  SqlExpProj table col -> table <> "." <> col
  SqlExpText str -> T.pack $ show str -- TODO: strings should use single quotes..
  SqlExpPreparedArg var -> ":" <> var
  SqlExpCase scrutinee branches -> paren prec 0 ("CASE " <> ppSqlExpressionQuote 0 scrutinee <> "\n" <> indent 2 (T.unlines (map ppSqlCaseBranchQuote branches)) <> "END")
    where
      ppSqlCaseBranchQuote :: (SqlExpressionQuote, SqlExpressionQuote) -> Text
      ppSqlCaseBranchQuote (patExp, resExp) = "WHEN " <> ppSqlExpressionQuote 0 patExp <> " THEN\n" <> indent 2 (ppSqlExpressionQuote 0 resExp)
  SqlExpRow [e] -> ppSqlExpressionQuote prec e
  SqlExpRow es -> "(" <> T.intercalate ", " (map (ppSqlExpressionQuote 0) es) <> ")"

ppSqlFromQuote :: SqlFromQuote -> Text
ppSqlFromQuote = \case
  SqlFromTable table -> table
  SqlFromTableAliased table alias -> ppIdentifierQuote table <> " AS " <> alias
  SqlFromStatement statement alias -> ppSqlStatementQuote 1 statement <> "AS " <> alias

ppSqlProjectionsQuote :: SqlProjectionsQuote -> Text
ppSqlProjectionsQuote = \case
  SqlProjectionColumns t cols -> T.intercalate ",\n" (map (\alias -> ppSqlExpressionQuote 1 (SqlExpProj t alias) <> " AS " <> alias) cols)
  SqlProjectionsAliased aliased -> T.intercalate ",\n" (map (\(alias, ex) -> ppSqlExpressionQuote 1 ex <> " AS " <> alias) aliased)
  SqlProjectionStar table -> table <> ".*"

ppIdentifierQuote :: Text -> Text
ppIdentifierQuote ident = "\"" <> ident <> "\""

indent :: Int -> Text -> Text
indent n = T.unlines . map (T.replicate n " " <>) . T.lines

parenIndent :: Int -> Int -> Text -> Text
parenIndent outerPrec innerPrec str | outerPrec > innerPrec = "(\n" <> indent 2 str <> ")\n"
parenIndent _ _ str = str

paren :: Int -> Int -> Text -> Text
paren outerPrec innerPrec str | outerPrec > innerPrec = "(" <> str <> ")"
paren _ _ str = str

withScope :: (Monad m, MonadReader Int m) => Text -> (Text -> m a) -> m a
withScope prefix binder = do
  x <- ask
  local succ $ binder (prefix <> T.pack (show x))

type TableName = Text

type TableAlias = Text

type ColumnAlias = Text

-- | The 'Shape' data type captures the nested structure of columns that results
-- from flattening types that are records-of-records.
-- newtype Shape = ShapeRec (NonEmpty (ColumnAlias, Maybe Shape))
data Shape
  = ShapeRecord (NonEmpty (ColumnAlias, Shape))
  | ShapeScalarField
  deriving (Eq, Show)

data SqliteRelationRepr
  = SRelTable Shape TableName
  | SRelLiteral Shape [NormSqliteRecRepr]
  | SRelProject Shape (TableAlias -> NormSqliteRecRepr) SqliteRelationRepr
  | SRelAggregate Shape (TableAlias -> (NormSqliteRecRepr, [NormSqliteExpRepr])) SqliteRelationRepr
  | SRelCross Shape SqliteRelationRepr SqliteRelationRepr
  | SRelRestrict (TableAlias -> NormSqliteExpRepr) SqliteRelationRepr
  | SRelUnion Shape (NonEmpty SqliteRelationRepr)
  | SRelExcept Shape SqliteRelationRepr SqliteRelationRepr

data SqliteExpRepr
  = SRecCon (NonEmpty (ColumnAlias, SqliteExpRepr))
  | SRecProj SqliteExpRepr ColumnAlias
  | SPrimCase SqliteExpRepr [(SqliteExpRepr, SqliteExpRepr)]
  | SPrimStrLit Text
  | SPrimSqlData SQLData -- raw data that we can send as prepared arguments
  | SPrimFunApp Text [SqliteExpRepr]
  | SPrimVar TableAlias
  deriving (Eq, Show)

-- TODO: Ensure in types that we always normalize (SRecProj (SRecCon ..) ..)
sRecProj :: SqliteExpRepr -> ColumnAlias -> SqliteExpRepr
sRecProj (SRecCon cols) col = lookupCol cols (NE.toList cols) col
  where
    lookupCol :: NonEmpty (ColumnAlias, SqliteExpRepr) -> [(ColumnAlias, SqliteExpRepr)] -> Text -> SqliteExpRepr
    lookupCol allCols [] col = error $ T.unpack $ "Cannot find col '" <> col <> "' of " <> T.pack (show allCols)
    lookupCol allCols ((col', val) : rest) col
      | col == col' = val
      | otherwise = lookupCol allCols rest col
sRecProj exp col = SRecProj exp col

newtype NormSqliteRecRepr
  = NSRecCon [(ColumnAlias, NormSqliteExpRepr)]
  deriving (Eq, Show)

oneRec :: NormSqliteExpRepr -> NormSqliteRecRepr
oneRec exp = NSRecCon [("scalar", exp)]

data NormSqliteExpRepr
  = NSRecProj TableAlias ColumnAlias
  | NSPrimStrLit Text
  | -- raw data that we can send as prepared arguments
    NSPrimSqlData SQLData
  | NSPrimFunApp Text [Either NormSqliteExpRepr NormSqliteRecRepr]
  | -- Case expression when the scrutinee is a record
    NSPrimCaseRec NormSqliteRecRepr [(NormSqliteRecRepr, NormSqliteExpRepr)]
  | -- Case expression when the scrutinee is a scalar expression
    NSPrimCaseExp NormSqliteExpRepr [(NormSqliteExpRepr, NormSqliteExpRepr)]
  deriving (Eq, Show)

normalizeExp ::
  forall m.
  (MonadError Text m) =>
  SqliteExpRepr ->
  m (Either NormSqliteExpRepr NormSqliteRecRepr)
normalizeExp (SPrimStrLit lit) = return $ Left $ NSPrimStrLit lit
normalizeExp (SPrimSqlData sqlData) = return $ Left $ NSPrimSqlData sqlData
normalizeExp (SPrimFunApp fn args) = do
  normArgs <- mapM normalizeExp args
  return $ Left $ NSPrimFunApp fn normArgs
normalizeExp (SRecCon cols) =
  Right . NSRecCon . concat
    <$> traverse
      ( \(col, val) -> do
          normVal <- normalizeExp val
          case normVal of
            Left normExp -> return [(col, normExp)]
            Right (NSRecCon subCols) -> return [(col <> "_" <> col', val) | (col', val) <- subCols]
      )
      cols
normalizeExp (SRecProj (SPrimVar v) col) = return $ Left $ NSRecProj v col
normalizeExp x@(SRecProj exp col) = do
  throwError $ "Is this actually redundant given smart constructor of 'sRecProj' ?" <> T.pack (show x)
  v <- cancelOut exp col
  -- fmap flattenOneRec (normalizeExp v)
  normalizeExp v
  where
    cancelOut :: SqliteExpRepr -> ColumnAlias -> m SqliteExpRepr
    cancelOut (SRecCon cols) col = lookupCol cols (NE.toList cols) col
    cancelOut (SRecProj r' col') col = do
      cancelled <- cancelOut r' col'
      case cancelled of
        SRecCon cols -> lookupCol cols (NE.toList cols) col
        _ -> throwError "Attempting to cancel out projection from something not a record"
    cancelOut _ _ = throwError "Attempting to cancel out projecton from something not a record"

    lookupCol :: NonEmpty (ColumnAlias, SqliteExpRepr) -> [(ColumnAlias, SqliteExpRepr)] -> Text -> m SqliteExpRepr
    lookupCol allCols [] col = throwError $ "Cannot find col '" <> col <> "' of " <> T.pack (show allCols)
    lookupCol allCols ((col', val) : rest) col
      | col == col' = return val
      | otherwise = lookupCol allCols rest col
-- Case expressions are a bit subtle. We have various cases to deal with:
--
-- The straightforwardly supported by sqlite:
--
--    case <scalar>
--      when <scalar> then <scalar>
--    end
--
--    case <record>
--      when <record> then <scalar>
--    end
--
-- The ones which need to distribute into the record expression, because a case
-- expression can only evaluate to a scalar value:
--
--    case <scalar>
--      when <scalar> then <record>
--    end
--
--    case <record>
--      when <record> then <record>
--    end
--
normalizeExp (SPrimCase scrutineeExp branchExps) = do
  let (patExps, resultExps) = unzip branchExps
  scrutineeNormEither <- normalizeExp scrutineeExp
  (patNormExps, patNormRecs) <- partitionEithers <$> traverse normalizeExp patExps
  (resultNormExps, resultNormRecs) <- partitionEithers <$> traverse normalizeExp resultExps
  matchGen <- case (scrutineeNormEither, patNormExps, patNormRecs) of
    (Left scrutineeNormExp, _, []) -> return $ \resExps -> NSPrimCaseExp scrutineeNormExp (zip patNormExps resExps)
    (Left scrutineeNormExp, [], _) -> throwError "normalizeExp: some patterns were records, where expression was expected"
    (Right scrutineeNormExp, [], _) -> return $ \resExps -> NSPrimCaseRec scrutineeNormExp (zip patNormRecs resExps)
    (Right scrutineeNormExp, _, []) -> throwError "normalizeExp: some patterns were expressions, where record was expected"
    x -> throwError ("normalizeExp: huh? " <> T.pack (show x))
  -- depending on the whether the result is a record or scalar, we may need to distribute
  -- the case expression into the record.
  case (resultNormExps, resultNormRecs) of
    (_, []) -> return $ Left $ matchGen resultNormExps
    ([], _) -> Right <$> distributeRec matchGen resultNormRecs
    x -> throwError ("normalizeExp: huh? " <> T.pack (show x))
  where
    distributeRec :: (MonadError Text m) => ([NormSqliteExpRepr] -> NormSqliteExpRepr) -> [NormSqliteRecRepr] -> m NormSqliteRecRepr
    distributeRec matchGen recs = do
      tabRec :: [(ColumnAlias, [NormSqliteExpRepr])] <- tabulateNormRecs recs
      return $ NSRecCon $ map (second matchGen) tabRec

    -- Turn a list of records into a 'record of lists':
    --
    -- { foo: 1, bar: a}, {foo: 2, bar b}
    --
    -- becomes
    -- {foo: [1,2], bar: [a,b]}
    --
    -- All the while preserving the ordering of keys and values (which are presumed
    -- to be identical across all given records).
    tabulateNormRecs :: (MonadError Text m) => [NormSqliteRecRepr] -> m [(ColumnAlias, [NormSqliteExpRepr])]
    tabulateNormRecs [] = return []
    tabulateNormRecs recs@(NSRecCon (map fst -> header) : _) = for header (\c -> (c,) <$> extract c recs)

    extract :: (MonadError Text m) => ColumnAlias -> [NormSqliteRecRepr] -> m [NormSqliteExpRepr]
    extract c ((NSRecCon r) : rs) = do
      h <- maybe (throwError ("extract: unable to tabulate column " <> c)) return $ lookup c r
      t <- extract c rs
      return (h : t)
    extract _ [] = return []

-- Hmm.. idk.. dealing sensibly with single-field records is a bit hairy..
-- flattenOneRec :: Either NormSqliteExpRepr NormSqliteRecRepr -> Either NormSqliteExpRepr NormSqliteRecRepr
-- flattenOneRec (Right (NSRecCon [(_, x)])) = Left x
-- flattenOneRec x = x
normalizeExp (SPrimVar v) = throwError ("Encountered bare variable '" <> v <> "' not in the context of column projection")

-- normalizeExp exp = throwError ("unable to normalize: " <> T.pack (show exp))

withShape :: forall a. a -> (ColumnAlias -> a) -> (NonEmpty (ColumnAlias, a) -> a) -> Shape -> a
withShape scalarCase k k2 = inner id
  where
    inner :: (ColumnAlias -> ColumnAlias) -> Shape -> a
    inner buildCol ShapeScalarField = scalarCase
    inner buildCol (ShapeRecord cols) =
      k2 $
        NE.map
          ( \(col, shape) ->
              ( col,
                case shape of
                  ShapeScalarField -> k (buildCol col)
                  _ -> inner (buildCol . ((col <> "_") <>)) shape
              )
          )
          cols

-- | Compute columns to project from a Shape.
-- A toplevel ShapeScalarField is Nothing.
shapeProjColumns :: Shape -> NonEmpty ColumnAlias
shapeProjColumns = withShape ("scalar" NE.:| []) (NE.:| []) (snd =<<)

sqlRelQuote :: forall m. (Monad m, MonadReader Int m, ExpressionQuoteM m) => SqliteRelationRepr -> m SqlStatementQuote
sqlRelQuote (SRelTable shape tableName) = do
  withScope tableName \t -> do
    return ((sqlSelect (SqlProjectionColumns t $ NE.toList (shapeProjColumns shape))) {sqlSelectFrom = [SqlFromTableAliased tableName t]})
sqlRelQuote (SRelLiteral shape []) = do
  let valuesProj = [(col, SqlExpNull) | col <- NE.toList $ shapeProjColumns shape]
      projQ = SqlProjectionsAliased valuesProj
  return $
    SqlSelect
      { sqlSelectFrom = [],
        sqlSelectProj = projQ,
        sqlSelectWhere = [SqlExpBool False],
        sqlSelectGroupBy = [],
        sqlSelectLimit = Nothing
      }
sqlRelQuote (SRelLiteral shape rows) = do
  withScope "literal" \var -> do
    rowsQ <- mapM sqlNamedRecQuote rows
    let header = NE.toList $ shapeProjColumns shape
        rowValuesQ = map (map snd) rowsQ
        valuesProj = [(col, SqlExpProj var ("column" <> T.pack (show ix))) | (col, ix) <- zip header [1 ..]]
        projQ = SqlProjectionsAliased valuesProj
    return
      ((sqlSelect projQ) {sqlSelectFrom = [SqlFromStatement (SqlValues rowValuesQ) var]})
sqlRelQuote (SRelRestrict pred' rel') = do
  withScope "restrict" \var -> do
    rel <- sqlRelQuote rel'
    pred <- sqlExpQuote (pred' var)
    return
      ( (sqlSelect (SqlProjectionStar var))
          { sqlSelectFrom = [SqlFromStatement rel var],
            sqlSelectWhere = [pred]
          }
      )
sqlRelQuote (SRelProject _shape projF rel') = do
  withScope "project" \alias -> do
    rel <- sqlRelQuote rel'
    let projExp = projF alias
    projQ <- -- trace ("SRelProject\n  _shape="<> show _shape <> "\n  projExp=" <> show projExp) $
      SqlProjectionsAliased <$> sqlNamedRecQuote projExp
    return ((sqlSelect projQ) {sqlSelectFrom = [SqlFromStatement rel alias]})
sqlRelQuote (SRelAggregate _shape projAggF rel') = do
  withScope "project" \alias -> do
    rel <- sqlRelQuote rel'
    let (projExp, groupExp) = projAggF alias
    projQ <- -- trace ("SRelProject\n  _shape="<> show _shape <> "\n  projExp=" <> show projExp) $
      SqlProjectionsAliased <$> sqlNamedRecQuote projExp
    groupQ <- mapM sqlExpQuote groupExp
    return
      ( (sqlSelect projQ)
          { sqlSelectFrom = [SqlFromStatement rel alias],
            sqlSelectGroupBy = groupQ
          }
      )
sqlRelQuote (SRelCross _shape relA relB) = do
  withScope "crossA" \aliasA -> do
    withScope "crossB" \aliasB -> do
      -- TODO: This would have been so much easier if a rel_cross had a (Exp a -> Exp b -> Exp c) projection function.
      -- Now we have to manually do the same work here as if that function had been (:*), which is brittle.
      relAQ <- sqlRelQuote relA
      relBQ <- sqlRelQuote relB
      let projQ =
            SqlProjectionsAliased $
              ( case relationReprShape relA of
                  ShapeScalarField -> [("_1", SqlExpProj aliasA "scalar")]
                  shape@ShapeRecord {} -> [("_1_" <> colA, SqlExpProj aliasA colA) | colA <- NE.toList $ shapeProjColumns shape]
              )
                ++ ( case relationReprShape relB of
                       ShapeScalarField -> [("_2", SqlExpProj aliasB "scalar")]
                       shape@ShapeRecord {} -> [("_2_" <> colB, SqlExpProj aliasB colB) | colB <- NE.toList $ shapeProjColumns shape]
                   )
      return $
        -- trace ("SRelCross\n  _shape=" <> show _shape <> "\n") $
        (sqlSelect projQ)
          { sqlSelectFrom =
              [ SqlFromStatement relAQ aliasA,
                SqlFromStatement relBQ aliasB
              ]
          }
sqlRelQuote (SRelUnion shape rels) = SqlUnionAll <$> traverse sqlRelQuote rels
sqlRelQuote (SRelExcept sh s1 s2) = SqlExcept <$> sqlRelQuote s1 <*> sqlRelQuote s2

sqlNamedRecQuote :: forall m. (Monad m, ExpressionQuoteM m) => NormSqliteRecRepr -> m [(ColumnAlias, SqlExpressionQuote)]
sqlNamedRecQuote (NSRecCon cols) = mapM (\(alias, expQ) -> (alias,) <$> sqlExpQuote expQ) cols

sqlRowValueQuote :: forall m. (Monad m, ExpressionQuoteM m) => Either NormSqliteExpRepr NormSqliteRecRepr -> m SqlExpressionQuote
sqlRowValueQuote (Left prim) = sqlExpQuote prim
sqlRowValueQuote (Right (NSRecCon row)) = SqlExpRow <$> for row (sqlExpQuote . snd)

sqlExpQuote :: forall m. (Monad m, ExpressionQuoteM m) => NormSqliteExpRepr -> m SqlExpressionQuote
sqlExpQuote (NSRecProj t col) = return $ SqlExpProj t col
sqlExpQuote (NSPrimStrLit t) = return $ SqlExpText t
sqlExpQuote (NSPrimSqlData dat) =
  -- Sometimes we want to use prepared arguments, sometimes we want to inline.
  -- Therefore we defer to 'ExpressionQuoteM(sqlExpQuotePrim)'.
  sqlExpQuotePrim dat
sqlExpQuote (NSPrimFunApp fn args) =
  case fn of
    _ | fn `elem` binops -> case args of
      [x, y] -> SqlExpOpApp fn <$> sqlRowValueQuote x <*> sqlRowValueQuote y
      _ -> error $ "'" <> T.unpack fn <> "' not given 2 args!"
    _ -> SqlExpFunApp fn <$> mapM sqlRowValueQuote args
  where
    binops = ["=", ">", ">=", "and", "or"]
sqlExpQuote (NSPrimCaseExp scrutineeNormExp branchExps) = do
  scrutineeQ <- sqlExpQuote scrutineeNormExp
  SqlExpCase scrutineeQ <$> for branchExps \(patNormExp, resNormExp) -> do
    patQ <- sqlExpQuote patNormExp
    resQ <- sqlExpQuote resNormExp
    return (patQ, resQ)
sqlExpQuote (NSPrimCaseRec (NSRecCon scrutineeNormRec) branchExps) = do
  scrutineeRecQs <- for scrutineeNormRec (sqlExpQuote . snd)
  SqlExpCase (SqlExpRow scrutineeRecQs) <$> for branchExps \(NSRecCon patNormRec, resNormExp) -> do
    patQs <- for patNormRec (sqlExpQuote . snd)
    resQ <- sqlExpQuote resNormExp
    return (SqlExpRow patQs, resQ)

class ExpressionQuoteM m where
  sqlExpQuotePrim :: SQLData -> m SqlExpressionQuote

newtype QuoteWithPreparedArgs m a = QuoteWithPreparedArgs {unQuoteWithPreparedArgs :: m a}
  deriving (Functor, Applicative, Monad)

instance MonadTrans QuoteWithPreparedArgs where
  lift :: Monad m => m a -> QuoteWithPreparedArgs m a
  lift = QuoteWithPreparedArgs

instance MonadReader r m => MonadReader r (QuoteWithPreparedArgs m) where
  ask = lift ask
  local f m = lift $ local f (unQuoteWithPreparedArgs m)

instance (MonadState (IntMap SQLData) m) => ExpressionQuoteM (QuoteWithPreparedArgs m) where
  sqlExpQuotePrim :: (MonadState (IntMap SQLData) m) => SQLData -> QuoteWithPreparedArgs m SqlExpressionQuote
  sqlExpQuotePrim dat = do
    nextId <- QuoteWithPreparedArgs $ gets IntMap.size
    QuoteWithPreparedArgs $ modify (IntMap.insert nextId dat)
    return $ SqlExpPreparedArg ("a" <> T.pack (show nextId))

newtype QuoteWithInlining m a = QuoteWithInlining {unQuoteWithInlining :: m a}
  deriving (Functor, Applicative, Monad)

instance MonadTrans QuoteWithInlining where
  lift :: Monad m => m a -> QuoteWithInlining m a
  lift = QuoteWithInlining

instance MonadReader r m => MonadReader r (QuoteWithInlining m) where
  ask = lift ask
  local f m = lift $ local f (unQuoteWithInlining m)

instance (Monad m) => ExpressionQuoteM (QuoteWithInlining m) where
  sqlExpQuotePrim :: SQLData -> QuoteWithInlining m SqlExpressionQuote
  sqlExpQuotePrim dat =
    return $ case dat of
      SQLInteger x -> SqlExpInt (fromIntegral x)
      SQLFloat x -> SqlExpFloat x
      SQLText x -> SqlExpText x
      SQLBlob _x -> error "TODO: Quoting sql blobs"
      SQLNull -> SqlExpNull

unquoteRecRepr :: NormSqliteRecRepr -> TableAlias -> (TableAlias -> NormSqliteRecRepr)
unquoteRecRepr (NSRecCon rs) var val = NSRecCon (map (\(alias, prim) -> (alias, unquoteExpRepr prim var val)) rs)

unquoteExpRepr :: NormSqliteExpRepr -> TableAlias -> (TableAlias -> NormSqliteExpRepr)
unquoteExpRepr p@(NSRecProj var' field) var val
  | var' == var = NSRecProj val field
  | otherwise = p
unquoteExpRepr p@NSPrimStrLit {} _ _ = p
unquoteExpRepr p@NSPrimSqlData {} _ _ = p
unquoteExpRepr (NSPrimFunApp fn args) var val =
  NSPrimFunApp
    fn
    ( map
        ( \case
            Left prim -> Left $ unquoteExpRepr prim var val
            Right row -> Right $ unquoteRecRepr row var val
        )
        args
    )
unquoteExpRepr (NSPrimCaseExp scrutinee branches) var val =
  NSPrimCaseExp
    (unquoteExpRepr scrutinee var val)
    (map (\(pat, res) -> (unquoteExpRepr pat var val, unquoteExpRepr res var val)) branches)
unquoteExpRepr (NSPrimCaseRec scrutinee branches) var val =
  NSPrimCaseRec
    (unquoteRecRepr scrutinee var val)
    (map (\(pat, res) -> (unquoteRecRepr pat var val, unquoteExpRepr res var val)) branches)

relationReprShape :: SqliteRelationRepr -> Shape
relationReprShape (SRelTable shape _) = shape
relationReprShape (SRelLiteral shape _) = shape
relationReprShape (SRelProject shape _ _) = shape
relationReprShape (SRelAggregate shape _ _) = shape
relationReprShape (SRelCross shape _ _) = shape
relationReprShape (SRelRestrict _ rel) = relationReprShape rel
relationReprShape (SRelUnion shape _) = shape
relationReprShape (SRelExcept shape _ _) = shape

describe :: Text -> IO () -> IO ()
describe header nest = do
  T.putStrLn ("* " <> header)
  nest

it :: Text -> IO () -> IO ()
it header example = do
  T.putStrLn ("** " <> header)
  example

shouldBe :: (Eq a, Show a) => a -> a -> IO ()
shouldBe actual expected
  | actual == expected = return ()
  | otherwise = do
      putStrLn ""
      print actual
      putStrLn "\nis not equal to\n"
      print expected

test :: IO ()
test = do
  describe "Projecting columns from a shape" $ do
    it "Doesn't prescribe any fields in the Scalar case" $ do
      let shape = ShapeScalarField
          actual = shapeProjColumns shape

          expected = "scalar" NE.:| []

      actual `shouldBe` expected

    it "Only mentions record fields" $ do
      let shape =
            ShapeRecord
              ( ("someScalarColumn", ShapeScalarField)
                  NE.:| [("someRecordColum", ShapeRecord (("someRecordScalarField", ShapeScalarField) NE.:| []))]
              )
          actual = shapeProjColumns shape

          expected = "someScalarColumn" NE.:| ["someRecordScalarField_someRecordColum"]

      actual `shouldBe` expected
