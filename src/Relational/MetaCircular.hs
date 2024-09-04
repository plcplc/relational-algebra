{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant return" #-}
module Relational.MetaCircular
  ( R (..),
    Exp (..),
    Relation (..),
    Transactional (..),
    TransactionT (..),
    runTransactionT,
    Table (..),
    module Relational.Class,
    -- Template Haskell
    relationalMetaCyclicalInstances,
  )
where

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.State.Strict
import Data.Aeson
import Data.Fixed
import Data.Kind
import Generics.SOP.Type.Metadata qualified as Metadata
import Language.Haskell.TH (Extension (TemplateHaskell))
import Language.Haskell.TH.Syntax hiding (Exp, lift)
import Relational.Class

newtype R tables = R tables

instance Relational (R tables) where
  newtype Relation (R tables) a = Relation_R {unRelation_R :: State tables [a]}
    deriving (Functor)
  newtype Exp (R tables) a = Exp_R {unExp_R :: a}
    deriving (Functor)

  (*:) = liftA2 (,)

  exp_fst = fmap fst
  exp_snd = fmap snd

  rel_union rels = Relation_R $ concat <$> traverse unRelation_R rels

  rel_cross (Relation_R rel1) (Relation_R rel2) = Relation_R do
    xs <- rel1
    ys <- rel2
    return do
      x <- xs
      y <- ys
      return (x, y)
  rel_project f = Relation_R . fmap (map (unExp_R . f . Exp_R)) . unRelation_R
  rel_restrict f = Relation_R . fmap (filter (unExp_R . f . Exp_R)) . unRelation_R

instance (Eq a, Relational (R tables)) => RelationalMinus (R tables) a where
  rel_minus (Relation_R rel1) (Relation_R rel2) = Relation_R do
    xs <- rel1
    ys <- rel2
    return $ [x | x <- xs, x `notElem` ys]

instance RelationalView (R tables) where
  data View (R tables) a = View_R (Relation (R tables) a)

  rel_view :: String -> Relation (R tables) a -> View (R tables) a
  rel_view _ = View_R

  view_rel :: View (R tables) a -> Relation (R tables) a
  view_rel (View_R rel) = rel

  declare_view ::
    (TransactionalConstraints (R tables) m) =>
    View (R tables) a ->
    TransactionT (R tables) m ()
  declare_view _ = return ()

instance Functor (AggExp (R tables) x) where
  fmap :: (a -> b) -> AggExp (R tables) x a -> AggExp (R tables) x b
  fmap = undefined

instance Applicative (AggExp (R tables) x) where
  pure :: a -> AggExp (R tables) x a
  pure = undefined
  (<*>) :: AggExp (R tables) x (a -> b) -> AggExp (R tables) x a -> AggExp (R tables) x b
  (<*>) = undefined

instance Profunctor (AggExp (R tables)) where
  lmap :: (a -> b) -> AggExp (R tables) b c -> AggExp (R tables) a c
  lmap = undefined
  rmap :: (b -> c) -> AggExp (R tables) a b -> AggExp (R tables) a c
  rmap = undefined

instance RelationalAggregate (R tables) where
  data AggExp (R tables) a b = AggExp_TODO

  rel_aggregate ::
    AggExp (R tables) (Exp (R tables) a) (Exp (R tables) b) ->
    Relation (R tables) a ->
    Relation (R tables) b
  rel_aggregate = undefined

  group_by :: AggExp (R tables) (Exp (R tables) a) (Exp (R tables) a)
  group_by = undefined

  count :: AggExp (R tables) (Exp (R tables) a) (Exp (R tables) Int)
  count = undefined

instance AggregateNum (R tables) Int where
  maximum :: AggExp (R tables) (Exp (R tables) Int) (Exp (R tables) Int)
  maximum = undefined
  sum :: AggExp (R tables) (Exp (R tables) Int) (Exp (R tables) Int)
  sum = undefined

instance AggregateNum (R tables) (Fixed n) where
  maximum :: AggExp (R tables) (Exp (R tables) (Fixed n)) (Exp (R tables) (Fixed n))
  maximum = undefined
  sum :: AggExp (R tables) (Exp (R tables) (Fixed n)) (Exp (R tables) (Fixed n))
  sum = undefined

instance AggregateNum (R tables) Double where
  maximum :: AggExp (R tables) (Exp (R tables) Double) (Exp (R tables) Double)
  maximum = undefined
  sum :: AggExp (R tables) (Exp (R tables) Double) (Exp (R tables) Double)
  sum = undefined

instance BoolOps (R tables) where
  (.||) :: Exp (R tables) Bool -> Exp (R tables) Bool -> Exp (R tables) Bool
  (.||) = undefined
  (.&&) :: Exp (R tables) Bool -> Exp (R tables) Bool -> Exp (R tables) Bool
  (.&&) = undefined
  bool_elim :: Exp (R tables) a -> Exp (R tables) a -> Exp (R tables) Bool -> Exp (R tables) a
  bool_elim = undefined

instance Applicative (Exp (R t)) where
  pure = Exp_R
  (Exp_R f) <*> (Exp_R x) = Exp_R (f x)

instance RelationalLiteral (R tables) a where
  rel_literal rows = Relation_R $ return (map unExp_R rows)

instance Transactional (R tables) where
  newtype TransactionT (R tables) m a = TransactionT_R {runTransactionT_R :: StateT tables m a}
    deriving newtype (Functor, Applicative, Monad, MonadTrans)

  type RelationalOutput (R tables) = Top
  type TransactionalConstraints (R tables) = Monad

  query = TransactionT_R . mapStateT (return . runIdentity) . unRelation_R

  insert ::
    forall select insert m.
    (Monad m) =>
    Table (R tables) select insert ->
    Relation (R tables) insert ->
    TransactionT (R tables) m ()
  insert t (Relation_R rel) = TransactionT_R do
    rows <- mapStateT (return . runIdentity) rel
    modify (table_R_Insert t rows)

instance (MonadIO m) => MonadIO (TransactionT (R tables) m) where
  liftIO = lift . liftIO

runTransactionT = runTransactionT_R

instance Tabular (R tables) where
  data Table (R tables) select insert = Table_R
    { table_R_Select :: tables -> [select],
      table_R_Insert :: [insert] -> tables -> tables
    }
  table t = Relation_R (gets (table_R_Select t))

class Top a

instance Top a

instance PureExp (R tables) a where
  pureExp = Exp_R

instance ProjectExp (R ts) a

instance GProjectExp (R ts) a where
  gProjectField = error "todo"

instance ConstructExp (R ts) a

instance GConstructExp (R ts) a where
  gNew = error "todo"

instance (Eq a) => EqOp (R ts) a where
  (Exp_R a) .== (Exp_R b) = Exp_R (a == b)

instance (Ord a) => OrdOp (R ts) a where
  (Exp_R a) .> (Exp_R b) = Exp_R (a > b)
  (Exp_R a) .>= (Exp_R b) = Exp_R (a >= b)

-- Derive the instances necessary for a record type to be used in a relational algebra DSL expression.
relationalMetaCyclicalInstances :: Name -> Q [Dec]
relationalMetaCyclicalInstances subjectTypeName = do
  let subjectType = ConT subjectTypeName

  -- For MetaCircular.
  aeson <-
    [d|
      instance FromJSON $(return subjectType)

      instance ToJSON $(return subjectType)
      |]

  return aeson
