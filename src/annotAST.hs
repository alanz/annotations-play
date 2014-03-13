{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}


-- import Generics.MultiRec (children)  hiding (show)
-- import Generics.MultiRec.HFix (children)

import Annotations.MultiRec.Annotated (children)
-- import Annotations.MultiRec.Any (children)

-- import AST
-- import ASTTHUse
import ASTExpr
import Annotations.Bounds
import Annotations.MultiRec.Annotated (AnnFix,AnnFix1)
import Control.Applicative hiding (Const)
import Control.Monad.State.Strict
import Control.Monad.Identity
import Data.Monoid
import Generics.MultiRec.Base
import Generics.MultiRec.HFix
import Generics.MultiRec.HFunctor
import qualified Generics.MultiRec.Fold as F
import Generics.MultiRec.FoldAlg as FA

main = putStrLn "hello"

-- | Example expression

-- example :: Expr String
-- example = Let (Seq ["x" := Mul (Const 6) (Const 9), "z" := Const 1])
--               (Mul (EVar "z") (Add (EVar "x") (EVar "y")))

example :: Expr
example = undefined

{-
type family PF phi :: (* -> *) -> * -> *


type AnnFix x s = HFix (K x :*: PF s)
-- A fully annotated tree.


type AnnFix1 x s = PF s (AnnFix x s)
-- A functor with fully annotated children.

mkAnnFix :: x -> AnnFix1 x s ix -> AnnFix x s ix
-- Supply a tree with an annotation at the top level.
-}


-- type

-- foo :: AnnFix1 Bounds ExprF
-- foo :: AnnFix1 Bounds (AST (Expr x)) r
-- foo = Expr Expr (Const 11)

-- ff :: AST String r
-- ff = undefined


nullBounds :: Bounds
nullBounds = Bounds (0,0) (0,0)

-- type AnnotExpr = AnnFix Bounds (AST (Expr String))

-- annotConst :: AnnotExpr r
-- annotConst = AnnFix nullBounds (Const 1)

-- foo :: AnnFix1 Bounds (s a)
-- foo = undefined

-- type instance PF (AST a)


data Except e a = Failed e | OK a
                  deriving (Functor,Show)

instance Monoid e => Applicative (Except e) where
  pure                    = OK
  OK f      <*> OK x      = OK (f x)
  OK _      <*> Failed e  = Failed e
  Failed e  <*> OK _      = Failed e
  Failed e1 <*> Failed e2 = Failed (e1 `mappend` e2)

type ErrorAlgebra f e a =           f   a      -> Either e a

-- exprEval :: ErrorAlgebra ExprF String Int
-- exprEval = undefined

-- type ErrorAlgPF   f e a = forall ix.f (K a  ) ix -> Either e a
type ErrorAlgPF   f e a r = forall ix.f (K a r) ix -> Either e a
-- type ErrorAlgPF   f e a = forall ix.f (K a r) ix -> Either e a
--                                 (f (K a r) ix -> Either e a)

{-
errorCata1 :: (HFunctor phi f )
  =>
     ErrorAlgPF f e r
  -> phi ix
  -> HFix (K x :*: f ) ix
  -> Except [(e, x)] r
errorCata1 = undefined
-}

-- type Foo f e a r = (forall ix.f (K a r) ix -> Either e a)

errorCata :: HFunctor phi f
  =>
     ErrorAlgPF f e a r
  -> phi ix
  -> HFix (K x :*: f) ix
  -> Except [(e, x)] a
errorCata alg pf (HIn (K k :*: f )) =
  case hmapA (\pg g -> K <$> errorCata alg pg g) pf f of
    Failed xs -> Failed xs
    OK expr' -> case alg expr' of
      Left x' -> Failed [(x', k)]
      Right v -> OK v


-- Page 57
type family ErrorAlg
  (f :: (* -> *) -> * -> *) -- pattern functor
  (e :: *)                  -- error type
  (a :: *)                  -- result type
  :: *                      -- resulting algebra type

type instance ErrorAlg U e a             =          Either e a
type instance ErrorAlg (K b  :*: f ) e a = b -> ErrorAlg f e a
type instance ErrorAlg (I xi :*: f ) e a = a -> ErrorAlg f e a


type instance ErrorAlg (f :+: g)  e a = (ErrorAlg f e a, ErrorAlg g e a)
type instance ErrorAlg (f :>: xi) e a =  ErrorAlg f e a



infixr 5 :&:
-- Note: This is a type synonym, so normal tuple processing stuff will
--       still work
type (:&:) = (,)



type ExprErrorAlg e a
 =   (a -> a -> Either e a) -- EAdd
 :&: (a -> a -> Either e a) -- EMul
 :&: (a -> a -> Either e a) -- ETup
 :&: (Int    -> Either e a) -- EIntLit
 :&: (a -> a -> Either e a) -- ETyped

type TypeErrorAlg e a
 =   (          Either e a) -- TyInt
 :&: (a -> a -> Either e a) -- TyTup

-- -------------------------------------

class MkErrorAlg f where
  mkErrorAlg :: ErrorAlg f e a -> ErrorAlgPF f e a r

instance MkErrorAlg U where
  mkErrorAlg x U = x

instance MkErrorAlg f => MkErrorAlg (K a :*: f ) where
  mkErrorAlg alg (K x :*: f ) = mkErrorAlg (alg x) f

instance MkErrorAlg f => MkErrorAlg (I xi :*: f ) where
  mkErrorAlg alg (I (K x) :*: f ) = mkErrorAlg (alg x) f

instance MkErrorAlg f => MkErrorAlg (f :>: xi) where
  mkErrorAlg alg (Tag f ) = mkErrorAlg alg f

instance (MkErrorAlg f , MkErrorAlg g) => MkErrorAlg (f :+: g) where
  mkErrorAlg (algf ,_ ) (L x) = mkErrorAlg algf x
  mkErrorAlg (_ , algg) (R y) = mkErrorAlg algg y

-- -------------------------------------


inferType :: ExprErrorAlg String Type :&: TypeErrorAlg String Type
inferType =
   (equal "+" &   -- EAdd
    equal "*" &   -- EMul
    tup &         -- ETup
    const (Right TyInt)  & -- EIntLit
    equal "::"    -- ETyped
   )
   &
   (
   Right TyInt & -- TyInt
   tup           -- TyTup
   )
  where
    equal op ty1 ty2
      | ty1 == ty2 = Right ty1
      | otherwise = Left ("lhs and rhs of "
                          ++ op ++ " must have equal types")
    tup ty1 ty2 = Right (TyTup ty1 ty2)


-- >let expr1 = readExpr "(1, (2, 3))"
tt expr = errorCata (mkErrorAlg inferType) Expr expr
-- OK (TyTup TyInt (TyTup TyInt TyInt))

exprE :: Expr
exprE = ETup (EIntLit 1) (ETup (EIntLit 2) (EIntLit 3))

-- f must be PF s
-- expr1 :: HFix (K x :*: f) ix
expr1 :: AnnFix String Tuples r
-- expr1 f = HIn . (K "foo" r Expr :*: from Expr (EIntLit 1))
expr1 = undefined

zz = from Expr (EIntLit 1)

-- ---------------------------------------------------------------------
-- Section 6.6 p60

{-
type family PF phi :: (* -> *) -> * -> *


type AnnFix x s = HFix (K x :*: PF s)
-- A fully annotated tree.

data HFix h ix = HIn {hout :: h (HFix h) ix}

type AnnFix1 x s = PF s (AnnFix x s)
-- A functor with fully annotated children.

mkAnnFix :: x -> AnnFix1 x s ix -> AnnFix x s ix
-- Supply a tree with an annotation at the top level.
-}

-- mkAnnFix :: x -> AnnFix1 x s ix -> AnnFix x s ix
-- mkAnnFix x = HIn . (K x :*:)


class Monad m => MonadYield m where
  type ΦYield m :: * -> *
  type AnnType m :: *
  yield :: ΦYield m ix -> AnnType m -> ix -> m ix

data AnyF φ f where
  AnyF :: φ ix -> f ix -> AnyF φ f

type AnyAnnFix x φ = AnyF φ (AnnFix x φ)

newtype YieldT x φ m a = YieldT (StateT [AnyAnnFix x φ] m a)
  deriving (Functor,Monad)

instance MonadTrans (YieldT x φ) where
   lift = YieldT . lift

instance (Monad m, HFunctor φ (PF φ), EqS φ,Fam φ) => MonadYield (YieldT x φ m) where
  type ΦYield (YieldT x φ m) = φ
  type AnnType (YieldT x φ m) = x
  yield = doYield


doYield :: (Monad m, HFunctor φ (PF φ), EqS φ,Fam φ)
   => φ ix -> x -> ix -> YieldT x φ m ix
doYield p bounds x = YieldT $ do
  let pfx = from p x
  let n = length (children p pfx)
  stack <- get
  if length stack < n
     then error $ "structure mismatch: required "++ show n
                  ++ " accumulated children but found only "
                  ++ show (length stack)
     else do
       let (cs, cs') = splitAt n stack
       let newChild = evalState (hmapM distribute p pfx) (reverse cs)
       put (AnyF p (HIn (K bounds :*: newChild)) : cs')
       return x

distribute :: EqS φ => φ ix -> I0 ix -> State [AnyAnnFix x φ] (AnnFix x φ ix)
distribute p1 _ = do
  xs <- get
  case xs of
    [] ->  error "structure mismatch: too few children"
    AnyF p2 x : xs' ->
      case eqS p1 p2 of
        Nothing -> error "structure mismatch: incompatible child type"
        Just Refl -> do put xs'; return x

{-
buildExpr :: MonadYield m => m (AnnFix1 Bounds Tuples r)
buildExpr =
  do
    n2 <- yield Expr (Bounds {leftMargin = (0, 0), rightMargin = (1, 2)}) (EIntLit 2)
    n3 <- yield Expr (Bounds {leftMargin = (3, 4), rightMargin = (5, 5)}) (EIntLit 3)
    n5 <- yield Expr (Bounds {leftMargin = (0, 0), rightMargin = (5, 5)}) (EAdd n2 n3)
    return n5

-- yield :: Monad m => ix -> Bounds -> Expr -> m (AnnFix1 Bounds Tuples r)
-- yield = undefined
-}
