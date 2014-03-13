{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}

--

import Annotations.Bounds
import Annotations.Except
import Control.Applicative
import Data.Foldable
import Data.Monoid
import Data.Traversable
import Text.Parsec.Combinator

import Text.ParserCombinators.Parsec
import Text.Parsec.Combinator
import qualified Text.Parsec.Prim as T
import Text.Parsec.Error
import Text.Parsec.Char

main = putStrLn "hello"

{-
exprEval expr = case expr of
  Num n -> Right n
  Add x y -> Right (x + y)
  Sub x y -> Right (x - y)
  Mul x y -> Right (x * y)
  Div x y
    | y == 0  -> Left "division by zero"
    | otherwise -> Right (x `div` y)
-}

{-
data BareExpr = Num Int
          | Add BareExpr BareExpr
          | Sub BareExpr BareExpr
          | Mul BareExpr BareExpr
          | Div BareExpr BareExpr
          deriving (Eq,Show)

type ParseTree a = Rose (Bounds, a)
data Rose a = Rose a [Rose a]
            deriving (Show)

example :: ParseTree BareExpr
example =
  let one = Num 1
      two = Num 2
      three = Num 3
      mul = Mul two three
      add = Add one mul
  in Rose (Bounds (0, 0) (9, 9), add)
            [Rose (Bounds (0, 0) (1, 2), one) [ ]
            , Rose (Bounds (3, 4) (9, 9), mul)
                [Rose (Bounds (3, 4) (5, 6), two) [ ]
                , Rose (Bounds (7, 8) (9, 9), three) [ ]
                ]
            ]
-}

------------------------------------------------------------------------


data ExprF r = Num Int
             | Add r r
             | Sub r r
             | Mul r r
             | Div r r


deriving instance Functor ExprF


deriving instance Foldable ExprF


newtype Fix f = In {out :: f (Fix f) }
newtype Expr = Expr {runExpr :: Fix ExprF}

instance Num Expr where
  -- a + b = undefined
  Expr (In (Num x)) + Expr (In (Num y)) = Expr $ In (Num (x+y))
  -- a * b = undefined
  Expr (In (Num x)) * Expr (In (Num y)) = Expr $ In (Num (x*y))
  abs a = error "abs undefined"
  signum a = error "signum undefined"
  -- fromInteger a = error "fromInteger undefined"
  fromInteger x = (Expr (In (Num (fromIntegral x))))


-- runExpr (2+3 ∗ 4)
rr = In {out = Add
                 (In {out = Num 2})
                 (In {out = Mul (In {out = Num 3})
                                (In {out = Num 4})})}

------------------------------------------------------------------------

data Ann x f a = Ann x (f a)

instance Functor f => Functor (Ann x f ) where
  fmap f (Ann x t) = Ann x (fmap f t)

newtype PositionalExpr = PositionalExpr {runPositionalExpr :: Fix (Ann Bounds ExprF)}

type AnnFix  x f = Fix (Ann x f)
type AnnFix1 x f = f (AnnFix x f)

mkAnnFix :: x -> AnnFix1 x f -> AnnFix x f
mkAnnFix x = In . Ann x

unannotate :: Functor f => AnnFix x f  -> Fix f
unannotate (In (Ann _ tree)) = In (fmap unannotate tree)

-- 5.1 -----------------------------------------------------------------

data ExprAlg a = ExprAlg
  { cataNum :: Int -> a
  , cataAdd :: a -> a -> a
  , cataSub :: a -> a -> a
  , cataMul :: a -> a -> a
  , cataDiv :: a -> a -> a
  }

cataExpr :: ExprAlg a -> Fix ExprF -> a
cataExpr alg = f where
  f (In expr) = case expr of
     Num n   -> cataNum alg n
     Add x y -> cataAdd alg (f x) (f y)
     Sub x y -> cataSub alg (f x) (f y)
     Mul x y -> cataMul alg (f x) (f y)
     Div x y -> cataDiv alg (f x) (f y)


cataExpr' :: (ExprF a -> a) -> Fix ExprF -> a
cataExpr' f (In expr) = f (fmap (cataExpr' f ) expr)

type Algebra f a = f a -> a
cata :: Functor f => Algebra f a -> Fix f -> a
cata f = f . fmap (cata f) . out


{-
exprEval :: Algebra ExprF Int
exprEval expr = case expr of
  Num n -> n
  Add x y -> x + y
  Sub x y -> x - y
  Mul x y -> x * y
  Div x y -> x `div` y
-}
-- t = cata exprEval (runExpr (1 + 2 * 3))


-- 5.2 -----------------------------------------------------------------

exprEval' :: Algebra (Ann Bounds ExprF) (Either (Bounds, String) Int)
exprEval' (Ann z expr) = case expr of
  Num n -> Right n
  Add x y -> (+) <$> x <*> y
  Sub x y -> (-) <$> x <*> y
  Mul x y -> (*) <$> x <*> y
  Div x y -> do
    x' <- x
    y' <- y
    if y' /= 0
       then Left (z, "division by zero")
       else Right (x' `div` y')


type ErrorAlgebra f e a = f a -> Either e a

exprEval :: ErrorAlgebra ExprF String Int
exprEval expr = case expr of
  Num n -> Right n
  Add x y  -> Right (x+y)
  Sub x y -> Right (x - y)
  Mul x y -> Right (x * y)
  Div x y
   | y == 0  -> Left "division by zero"
   | otherwise -> Right (x `div` y)


instance Traversable ExprF where
  traverse f expr = case expr of
    Num n -> pure (Num n)
    Add x y -> Add <$> f x <*> f y
    Sub x y -> Sub <$> f x <*> f y
    Mul x y -> Mul <$> f x <*> f y
    Div x y -> Div <$> f x <*> f y

-- t = cata exprEval (runExpr (1 + 2 * 3))

cascade :: (Traversable f, Monoid e) => ErrorAlgebra f e a -> Algebra f (Except e a)
cascade alg expr = case sequenceA expr of
  Failed xs -> Failed xs
  OK tree'  -> case alg tree' of
    Left xs -> Failed xs
    Right res -> OK res


errorCata :: Traversable f => ErrorAlgebra f e a -> AnnFix x f -> Except [(e, x)] a
errorCata alg (In (Ann x expr)) =
  case traverse (errorCata alg) expr of
    Failed xs -> Failed xs
    OK expr' -> case alg expr' of
      Left x' -> Failed [(x', x)]
      Right v -> OK v

-- 5.3 -----------------------------------------------------------------

data ExprToken
  = TNum Int
  | TPlus
  | TMinus
  | TStar
  | TSlash
  | TPOpen
  | TPClose
  | TSpace String

isSpace (TSpace _) = True
isSpace _         = False

isNum (TNum _) = True
isNum _        = False

-- type P = T.Parsec Char ()
-- type P = GenParser Char st
-- number :: P Integer
-- pNumber = do { ds <- many1 digit; return (read ds) } P.<?> "number"

pNum :: GenParser Char st ExprToken
pNum = do
  s <- many1 digit
  return (TNum $ read s)

pPlus :: GenParser Char st ExprToken
pPlus = char '+' >> return TPlus

pMinus :: GenParser Char st ExprToken
pMinus = char '-' >> return TMinus

pStar :: GenParser Char st ExprToken
pStar = char '*' >> return TMinus

pSlash :: GenParser Char st ExprToken
pSlash = char '/' >> return TMinus

pOpen :: GenParser Char st ExprToken
pOpen = char '(' >> return TMinus

pClose :: GenParser Char st ExprToken
pClose = char ')' >> return TMinus

pSpace :: GenParser Char st ExprToken
pSpace = do
  s <- many1 space
  return (TSpace s)

pToken :: GenParser Char st ExprToken -> GenParser Char st ()
pToken t = do
  _ <- t
  return ()


pExpr :: GenParser Char st Expr
pExpr = chainl1 pTerm   (Add <$ pToken TPlus
                     T.<|> Sub <$ pToken TMinus)

pTerm = chainl1 pFactor (Mul <$ pToken TStar
                     T.<|> Div <$ pToken TSlash)
pFactor = pNum
       T.<|> pToken TPOpen *> pExpr <* pToken TPClose
 
-- pNum = ( \(TNum n) -> Num n) <$> satisfy isNum

