{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}

import Generics.MultiRec
-- import Generics.MultiRec.Base

main = putStrLn "hello"

-- 6.2 -----------------------------------------------------------------

data Expr
  = EAdd Expr Expr
  | EMul Expr Expr
  | ETup Expr Expr
  | EIntLit Int
  | ETyped Expr Type
  deriving (Eq, Show)

data Type
  = TyInt
  | TyTup Type Type
  deriving (Eq, Show)

-- Multirec definitions

type PFExpr =
      I Expr :*: I Expr :*: U
  :+: I Expr :*: I Expr :*: U
  :+: I Expr :*: I Expr :*: U
  :+: K Int :*: U
  :+: I Expr :*: I Type :*: U

type PFType = U
          :+: I Type :*: I Type :*: U

type PFTuples = PFExpr :>: Expr :+: PFType :>: Type

data Tuples :: * -> * where
  Expr :: Tuples Expr
  Type :: Tuples Type


instance Fam Tuples where
  from Expr ex = L . Tag $ case ex of
    EAdd x y -> L $ I (I0 x) :*: I (I0 y) :*: U
    EMul x y -> R . L $ I (I0 x) :*: I (I0 y) :*: U
    ETup x y -> R . R . L $ I (I0 x) :*: I (I0 y) :*:U
    EIntLit n -> R . R . R . L $ K n :*: U
    ETyped e t -> R . R . R . R $ I (I0 e) :*: I (I0 t) :*: U
