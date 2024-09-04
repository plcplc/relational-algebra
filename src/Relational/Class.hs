{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Relational.Class
  ( Relational (..),
    pattern Pair,
    RelationalMinus (..),
    RelationalView (..),
    RelationalLiteral (..),
    PureExp (..),
    GPureExp (..),
    ProjectExp (..),
    TypeOfField (..),
    GProjectExp (..),
    ConstructExp (..),
    ConstructorFunction (..),
    ConFun (..),
    GConstructExp (..),
    RelationalRecordData,
    RelationalFieldData,
    RelationalAggregate (..),
    AggregateNum (..),
    EqOp (..),
    OrdOp (..),
    BoolOps (..),
    Transactional (..),
    TransactionRollback (..),
    RollbackT,
    Tabular (..),
    module Data.Kind,
    module GHC.TypeLits,
    module Data.Proxy,
    module Data.Profunctor,
    NonEmpty (..),

    -- * Template Haskell
    relationalFieldInstances,
    relationalRecordInstances,
    relationalRecordClass,
    relationalRecordClassNoTable,
  )
where

import Control.Monad.Except
import Control.Monad.Trans
import Data.Kind
import Data.List
import Data.List.NonEmpty (NonEmpty (..))
import Data.Profunctor
import Data.Proxy
import Data.Traversable
import GHC.TypeError qualified
import GHC.TypeLits
import Generics.SOP
import Generics.SOP.GGP qualified as GGP
import Generics.SOP.Type.Metadata qualified as Metadata
import Language.Haskell.TH hiding (Code, Exp, Type)
import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Syntax qualified as TH

-- Note the absence of run functions and Observe types. The only place where
-- these are relevant is when you already know what the concrete types are
-- (e.g. in a top-level main-like function), and then you'll have to deal with
-- those concrete types (i.e. There is nothing useful you can do with an
-- 'Observe db' value. And the only thing you can do with an 'Observe DB' value
-- is work with the concrete type it resolves to for your concrete 'DB' type.)
--
-- If any client user of this library needs to work with Transaction values
-- generically they can build that encapsulation themselves.
--
-- As a matter of convention however, modules defining instances of
-- 'Transactional' should provide a function:
--
--   'run<DbType>TransactionT :: TransactionalConstraints DbType m => TransactionT DbType m a -> ?'

class
  ( forall m. (Monad m) => Monad (TransactionT db m),
    MonadTrans (TransactionT db)
  ) =>
  Transactional db
  where
  data TransactionT db :: (Type -> Type) -> Type -> Type
  type RelationalOutput db :: Type -> Constraint

  -- Why this?
  -- Alternatively we could have made 'm' a type class parameter, but this is a
  -- bit awkward since it affords making instances based on various concrete
  -- types when what we really want is for clients to pick their own 'm'.
  -- We'll have to see how the ergonomics of this play out in practise.
  type TransactionalConstraints db :: (Type -> Type) -> Constraint

  query ::
    ( TransactionalConstraints db m,
      RelationalOutput db a
    ) =>
    Relation db a ->
    TransactionT db m [a]
  insert ::
    (TransactionalConstraints db m) =>
    Table db select insert ->
    Relation db insert ->
    TransactionT db m ()

-- The ability to rollback transactions:
--
-- For now we keep rollback as a separate Monad Transformer effect on top of
-- 'TransactionT'.
--
-- This means that you have to explicitly 'lift' to use query and insert. We'll
-- see how the ergonomics of this play out in practise.

newtype RollbackT m a = RollbackT {runRollbackT :: ExceptT () m a}
  deriving (Functor, Applicative, Monad, MonadTrans)

class TransactionRollback db where
  rollbackable :: RollbackT (TransactionT db m) a -> TransactionT db m (Maybe a)
  rollback :: RollbackT (TransactionT db m) a

class Tabular db where
  data Table db :: Type -> Type -> Type
  table :: Table db select insert -> Relation db select

class Relational db where
  data Relation db :: Type -> Type
  data Exp db :: Type -> Type

  -- Maybe make a cartesian category instead?
  (*:) :: Exp db a -> Exp db b -> Exp db (a, b)
  exp_fst :: Exp db (a, b) -> Exp db a
  exp_snd :: Exp db (a, b) -> Exp db b

  rel_union :: NonEmpty (Relation db a) -> Relation db a
  rel_project :: (Exp db a -> Exp db b) -> Relation db a -> Relation db b
  rel_restrict :: (Exp db a -> Exp db Bool) -> Relation db a -> Relation db a
  rel_cross :: Relation db a -> Relation db b -> Relation db (a, b)

class RelationalMinus db a where
  rel_minus :: Relation db a -> Relation db a -> Relation db a

pattern Pair :: (Relational db) => Exp db a -> Exp db b -> Exp db (a, b)
pattern Pair x y <- (\p -> (exp_fst p, exp_snd p) -> (x, y))
  where
    Pair x y = x *: y

class (Relational db) => RelationalLiteral db a where
  rel_literal :: [Exp db a] -> Relation db a

class (Relational db) => RelationalView db where
  data View db :: Type -> Type

  rel_view :: String -> Relation db a -> View db a
  view_rel :: View db a -> Relation db a

  declare_view :: (TransactionalConstraints db m) => View db a -> TransactionT db m ()

class PureExp db a where
  pureExp :: a -> Exp db a
  default pureExp :: (GPureExp db a) => a -> Exp db a
  pureExp = gPureExp

class GPureExp db a where
  gPureExp :: a -> Exp db a

class ProjectExp db a where
  projectField ::
    forall (fieldLabel :: Metadata.FieldName).
    (KnownSymbol fieldLabel) =>
    Proxy fieldLabel ->
    Exp db a ->
    Exp db (TypeOfField a fieldLabel)
  default projectField ::
    forall (fieldLabel :: Metadata.FieldName).
    ( GProjectExp db a,
      KnownSymbol fieldLabel
    ) =>
    Proxy fieldLabel ->
    Exp db a ->
    Exp db (TypeOfField a fieldLabel)
  projectField = gProjectField @db @a

class GProjectExp db a where
  gProjectField ::
    forall (fieldLabel :: Metadata.FieldName).
    (KnownSymbol fieldLabel) =>
    Proxy fieldLabel ->
    Exp db a ->
    Exp db (TypeOfField a fieldLabel)

type TypeOfField a f = Lookup (FieldTable a) f

type family Lookup (table :: [(p, q)]) (key :: p) :: q where
  Lookup ('(key, value) ': _) key = value
  Lookup (_ ': table) key = Lookup table key
  Lookup '[] key =
    TypeError
      ( GHC.TypeError.Text "Unable to find "
          :<>: ShowType key
          :<>: GHC.TypeError.Text " in lookup table"
      )

class ConstructExp db a where
  new :: Proxy db -> Proxy a -> ConstructorFunction db a
  default new :: (GConstructExp db a) => Proxy db -> Proxy a -> ConstructorFunction db a
  new = gNew

type ConstructorFunction db a = ConFun db a (SingleElement (Code a))

class GConstructExp db a where
  gNew :: Proxy db -> Proxy a -> ConstructorFunction db a

type family SingleElement (xs :: [p]) :: p where
  SingleElement '[x] = x

type family ConFun db (res :: Type) (args :: [Type]) :: Type where
  ConFun db res '[] = Exp db res
  ConFun db res (b ': args) = Exp db b -> ConFun db res args

type family ZipLists (xs :: [p]) (ys :: [q]) :: [(p, q)] where
  ZipLists (x ': xs) (y ': ys) = '(x, y) ': ZipLists xs ys
  ZipLists '[] '[] = '[]
  ZipLists _ _ = TypeError (GHC.TypeError.Text "ZipList lists have different length")

type family FieldTable a :: [(Metadata.FieldName, Type)] where
  FieldTable a = MakeFieldTable (Code a) (GGP.GDatatypeInfoOf a)

type family
  MakeFieldTable (fieldTypes :: [[Type]]) (metadata :: Metadata.DatatypeInfo) ::
    [(Metadata.FieldName, Type)]
  where
  MakeFieldTable '[fieldTypes] metadata = ZipLists (GetFieldNames (GetFieldInfos metadata)) fieldTypes

type family GetFieldInfos (metadata :: Metadata.DatatypeInfo) :: [Metadata.FieldInfo] where
  GetFieldInfos
    ( 'Metadata.ADT
        _moduleName
        _typeName
        '[ 'Metadata.Record
             _conName
             fieldInfos
         ]
        _strictnessInfo
    ) =
    fieldInfos

type family GetFieldNames (infos :: [Metadata.FieldInfo]) :: [Metadata.FieldName] where
  GetFieldNames '[] = '[]
  GetFieldNames ('Metadata.FieldInfo fieldName ': infos) = fieldName ': GetFieldNames infos

type RelationalRecordData db a =
  ( PureExp db a,
    ProjectExp db a,
    ConstructExp db a,
    RelationalOutput db a,
    RelationalLiteral db a,
    EqOp db a
  )

type RelationalFieldData db a =
  ( PureExp db a,
    RelationalOutput db a,
    RelationalLiteral db a,
    EqOp db a
  )

class
  ( forall a. Applicative (AggExp db a),
    Profunctor (AggExp db),
    Relational db
  ) =>
  RelationalAggregate db
  where
  data AggExp db :: Type -> Type -> Type

  rel_aggregate :: AggExp db (Exp db a) (Exp db b) -> Relation db a -> Relation db b

  group_by :: AggExp db (Exp db a) (Exp db a)
  count :: AggExp db (Exp db a) (Exp db Int)

class (RelationalAggregate db) => AggregateNum db a where
  maximum :: AggExp db (Exp db a) (Exp db a)
  sum :: AggExp db (Exp db a) (Exp db a)

class EqOp db a where
  (.==) :: Exp db a -> Exp db a -> Exp db Bool

infix 4 .==

class BoolOps db where
  (.||) :: Exp db Bool -> Exp db Bool -> Exp db Bool
  (.&&) :: Exp db Bool -> Exp db Bool -> Exp db Bool

  bool_elim :: Exp db a -> Exp db a -> Exp db Bool -> Exp db a

infixr 3 .&&

infixr 2 .||

class OrdOp db a where
  (.>) :: Exp db a -> Exp db a -> Exp db Bool
  (.>=) :: Exp db a -> Exp db a -> Exp db Bool

infix 4 .>

infix 4 .>=

-- Template Haskell
relationalFieldInstances :: Name -> Name -> Q [Dec]
relationalFieldInstances subjectTypeName dbTypeName = do
  --   info <- reify subjectTypeName
  --   -- We only try to derive PureExp for newtypes.
  --   case info of
  --    TyConI NewtypeD{} -> do
  --     [d|
  --       instance PureExp $(return $ ConT dbTypeName) $(return $ ConT subjectTypeName)
  --       |]
  --
  --   e -> return [] -- error (show e)
  --
  return []

relationalRecordInstances :: Name -> Name -> Q [Dec]
relationalRecordInstances subjectTypeName dbTypeName = do
  [d|
    instance ProjectExp $(return $ ConT dbTypeName) $(return $ ConT subjectTypeName)

    instance ConstructExp $(return $ ConT dbTypeName) $(return $ ConT subjectTypeName)

    instance PureExp $(return $ ConT dbTypeName) $(return $ ConT subjectTypeName)
    |]

relationalRecordClassMethods :: Name -> (TH.Type -> Q [Dec]) -> Q [Dec]
relationalRecordClassMethods subjectTypeName rest = do
  let subjectType = ConT subjectTypeName
  let TH.Name (TH.OccName occName) _ = subjectTypeName
  let relClassName = mkName $ "Rel" ++ occName

  dbTyVarName <- newName "db"
  let dbTyVar = VarT dbTyVarName

  -- We only support regular, single-constructor record types.
  TyConI (DataD [] _name [] Nothing [RecC _recConName fields] _derivClause) <- reify subjectTypeName

  let fieldTypes = nub $ map (\(_fieldName, _, fieldType) -> fieldType) fields

  fieldsContext <- for fieldTypes \fieldType -> do
    [t|RelationalFieldData $(return dbTyVar) $(return fieldType)|]

  selfContext <- [t|RelationalRecordData $(return dbTyVar) $(return subjectType)|]

  expFields <- for fields $ \(fieldName, _, fieldType) -> do
    let TH.Name (TH.OccName occName) _ = fieldName
    Just prefixless <- return (stripPrefix "_" occName)
    let prefixlessName = mkName prefixless
    fieldExpType <- [t|Exp $(return dbTyVar) $(return fieldType)|]
    return (prefixlessName, fieldExpType)

  expResType <- [t|Exp $(return dbTyVar) $(return subjectType)|]

  projectionMethods <- fmap concat $ for expFields $ \(fieldName, fieldType) -> do
    let TH.Name (TH.OccName occName) _ = fieldName
    methodSig <- SigD fieldName <$> [t|$(return expResType) -> $(return fieldType)|]

    -- methodImpl <- [d| someField = projectField (Proxy @"_someField")|]
    let methodImpl =
          ValD
            (VarP fieldName)
            ( NormalB
                ( AppE
                    (VarE 'Relational.Class.projectField)
                    ( AppTypeE
                        (ConE 'Data.Proxy.Proxy)
                        ( LitT
                            (StrTyLit ("_" ++ occName))
                        )
                    )
                )
            )
            []

    return [methodSig, methodImpl]

  let constructionMethodName = mkName $ "new" ++ occName
  let constructionMethodType = foldr (\(_, fieldTy) acc -> AppT (AppT ArrowT fieldTy) acc) expResType expFields
  let constructionMethodSig = SigD constructionMethodName constructionMethodType
  let constructionMethodImpl =
        ValD
          (VarP constructionMethodName)
          ( NormalB
              ( AppE
                  ( AppE
                      (VarE 'Relational.Class.new)
                      (AppTypeE (ConE 'Data.Proxy.Proxy) dbTyVar)
                  )
                  (AppTypeE (ConE 'Data.Proxy.Proxy) subjectType)
              )
          )
          []

  restMethods <- rest dbTyVar

  let relClassDecl =
        [ ClassD
            (fieldsContext ++ [selfContext])
            relClassName
            [PlainTV dbTyVarName ()]
            []
            (projectionMethods ++ [constructionMethodSig, constructionMethodImpl] ++ restMethods)
        ]

  return relClassDecl

-- | Define a class to collect the various projectinn and construction functions
-- for a record type used in the relational algebra DSL, as per convention.
--
-- A data type
--
--    data Foo = Foo { _fieldA :: A, _fieldB :: B }
--
-- Gives rise to the type class
--
--    class (
--      RelationalFieldData db A,
--      RelationalFieldData db B,
--      RelationalRecordData db Foo
--      ) => RelFoo db where
--
--      fieldA :: Exp db Foo -> Exp db A
--      fieldA = projectField (Proxy @"_fieldA")
--
--      fieldB :: Exp db Foo -> Exp db B
--      fieldB = projectField (Proxy @"_fieldB")
--
--      newFoo :: Exp db A -> Exp db B -> Exp db Foo
--      newFoo = new (Proxy @db) (Proxy @Foo)
--
--      tableFoo :: Table db Foo Foo
relationalRecordClass :: Name -> Q [Dec]
relationalRecordClass subjectTypeName = do
  relationalRecordClassMethods subjectTypeName $ \dbTyVar -> do
    let subjectType = ConT subjectTypeName
    let TH.Name (TH.OccName occName) _ = subjectTypeName
    tableMethodTpe <- [t|Table $(return dbTyVar) $(return subjectType) $(return subjectType)|]
    return [SigD (mkName $ "table" ++ occName) tableMethodTpe]

-- | The same as 'relationalRecordClass', but don't generate the 'table' method.
relationalRecordClassNoTable :: Name -> Q [Dec]
relationalRecordClassNoTable subjectTypeName = relationalRecordClassMethods subjectTypeName (const (return []))
