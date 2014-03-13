{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

import ASTExpr

import Annotations.MultiRec.Any
import Annotations.Bounds
import Annotations.MultiRec.Annotated
import Annotations.MultiRec.Yield
import Annotations.MultiRec.ShowFam
import Control.Applicative hiding (Const)
import Control.Monad.Identity
import Control.Monad.State.Strict
-- import Data.Monoid
import Generics.MultiRec.Base
import Generics.MultiRec.Compos
import Generics.MultiRec.FoldAlg as FA
import Generics.MultiRec.HFix
import Generics.MultiRec.HFunctor
import qualified Generics.MultiRec.Fold as F
-- import Generics.MultiRec.Show as GS
import Data.Maybe

main = putStrLn "Hello"

-- runYield :: EqS fam => fam a -> Yield x fam a -> Maybe (AnnFix x fam a)


-- tt = runYield

-- type YT a = Yield Bounds (Tuples Expr) a

-- tt :: Tuples Expr -> YT a -> Maybe (AnnFix Bounds Tuples a)
-- tt :: Tuples Expr -> Yield Bounds (Tuples Expr) a -> Maybe (AnnFix Bounds Tuples a)
-- tt = undefined


{-
buildExpr :: MonadYield m => m (AnnFix1 Bounds Tuples Expr)
buildExpr =
  do
    n2 <- yield Expr (Bounds {leftMargin = (0, 0), rightMargin = (1, 2)}) (EIntLit 2)
    n3 <- yield Expr (Bounds {leftMargin = (3, 4), rightMargin = (5, 5)}) (EIntLit 3)
    n5 <- yield Expr (Bounds {leftMargin = (0, 0), rightMargin = (5, 5)}) (EAdd n2 n3)
    return n5

-- yield :: Monad m => ix -> Bounds -> Expr -> m (AnnFix1 Bounds Tuples r)
-- yield = undefined


-- gg1 :: Maybe (AnnFix Bounds Tuples Expr)
-- gg1 = runYield (PF Tuples (AnnFix Bounds Tuples) Exp) buildExpr

buildExprIO :: IO (AnnFix1 Bounds Tuples Expr)
buildExprIO = buildExpr
-}

sx :: IO ()
sx = debugFlatten Expr xx

sx' :: HFix (PF Tuples) Expr
sx' = unannotate Expr xx

sx'' :: Expr
sx'' = hto Expr sx'

xx :: AnnFix Bounds Tuples Expr
xx = case (runYield Expr bb) of
       Nothing -> error "got Nothing"
       Just r -> r

bb :: Yield Bounds Tuples Expr
bb = do
    void $ yield Expr (Bounds {leftMargin = (0, 0), rightMargin = (1, 2)}) (EIntLit 2)
    void $ yield Expr (Bounds {leftMargin = (3, 4), rightMargin = (5, 5)}) (EIntLit 3)
    void $ yield Expr (Bounds {leftMargin = (0, 0), rightMargin = (5, 5)}) (EAdd undefined undefined)
    return (EIntLit 1)


instance ShowFam Tuples where
  showFam Expr (EAdd x1 x2)  = "(EAdd " ++ showFam Expr x1 ++ " " ++ showFam Expr x2 ++ ")"
  showFam Expr (EMul x1 x2)  = "(EMul " ++ showFam Expr x1 ++ " " ++ showFam Expr x2 ++ ")"
  showFam Expr (ETup x1 x2)  = "(ETup " ++ showFam Expr x1 ++ " " ++ showFam Expr x2 ++ ")"
  showFam Expr (EIntLit x)   = "(EIntLit " ++ show x ++ ")"
  showFam Expr (ETyped x t)  = "(ETyped " ++ showFam Expr x ++ " " ++ showFam Type t ++ ")"

  showFam Type (TyInt)       = "(TyInt)"
  showFam Type (TyTup x1 x2) = "(TyTup " ++ showFam Type x1 ++ " " ++ showFam Type x2 ++ ")"

-- ---------------------------------------------------------------------
-- Based on
-- stackoverflow.com/questions/9725796/how-does-hfix-work-in-haskells-multirec-package
{-
type Even' = HFix PFEO Even
type Odd'  = HFix PFEO Odd

test :: Even'
test = hfrom E (ESucc (OSucc Zero))

test' :: Even
test' = hto E test
-}

type Expr' = HFix (PF Tuples) Expr

te :: Expr
te = (EAdd (EIntLit 1) (EIntLit 2))

tte :: Expr
tte = (ETyped (EIntLit 1) TyInt)

test :: Expr'
test = hfrom Expr te

test' :: Expr
test' = hto Expr test

newtype Const a b = Const { unConst :: a }

{-
valueAlg :: Algebra EO (Const Int)
valueAlg _ = tag (\U             -> Const 0)
           & tag (\(I (Const x)) -> Const (succ x))
           & tag (\(I (Const x)) -> Const (succ x))

value :: Even -> Int
value = unConst . fold valueAlg E
-}

-- ---------------------------------------------------------------------

{-
-- | Renaming variables using 'compos'

renameVar :: Expr String -> Expr String
renameVar = renameVar' Expr
  where
    renameVar' :: AST String a -> a -> a
    renameVar' Var x = x ++ "_"
    renameVar' p   x = compos renameVar' p x

-- | Test for 'renameVar'

testRename :: Expr String
testRename = renameVar example
-}


addOne :: Expr -> Expr
addOne = addOne' Expr
  where
    addOne' :: Tuples a -> a -> a
    addOne' Expr (EIntLit x) = EIntLit (x+1)
    addOne' p x = compos addOne' p x

-- =====================================================================
-- ---------------------------------------------------------------------
-- Now for the annotated version

-- First. How to annotate an expression
{-

Yield expects a stack, and pops off it. So we must first serialize the
structure.

So
  (EAdd
    (EIntLit 2)
    (EIntLit 3))

arises from

    yield Expr ann1 (EIntLit 2)
    yield Expr ann2 (EIntLit 3)
    yield Expr ann3 (EAdd undefined undefined)

We need a depth-first traversal, building back up.

-}

-- | Flatten a tree to a list of subtrees
flatten'' :: forall s ix. (HFunctor s (PF s), Fam s) =>
    s ix -> HFix (PF s) ix -> [Any s]
flatten'' p tree@(HIn y) = (Any p (hto p tree)) :
    concatMap (flatten'' $?) (children p y)

xxx :: [Any Tuples]
xxx = flatten'' Expr $ hfrom Expr te

sw :: IO ()
sw = debugFlatten Expr ww

sw' :: HFix (PF Tuples) Expr
sw' = unannotate Expr ww

sw'' :: Expr
sw'' = hto Expr sw'


ww :: AnnFix Bounds Tuples Expr
ww = case (runYield Expr zz) of
       Nothing -> error "got Nothing"
       Just r -> r

zz' :: Yield Bounds Tuples Expr
zz' = do
    let ann = (Bounds {leftMargin = (0, 0), rightMargin = (1, 2)})
    void $ yield Expr ann (EIntLit 2)
    void $ yield Expr ann (EIntLit 3)
    yield Expr ann  (EAdd undefined undefined)


-- zz :: Yield Bounds Tuples Expr
zz :: Yield Bounds Tuples Expr
zz = do
  -- let x = head $ reverse xxx

  mapM_ doYield $ reverse xxx
  return (EIntLit 2)

  where
    ann = (Bounds {leftMargin = (0, 0), rightMargin = (1, 2)})

    doYield x = case x of
     Any Expr v' -> yield Expr ann v'

