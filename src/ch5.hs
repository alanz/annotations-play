{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

-- Based on ch 5 of 'Generic Selections of Subexpressions'
-- by M van Steenbergen

import Annotations.Bounds
import Annotations.Except
import Control.Applicative
import Control.Monad.Identity
import Data.Foldable (Foldable,toList)
import Data.List
import Data.Maybe
import Data.Monoid
import Data.Ord
import Data.Traversable
-- import Text.Parsec.Char
-- import Text.Parsec.String
-- import Text.Parsec.Combinator
-- import qualified Text.Parsec.Prim as P
-- import Text.ParserCombinators.Parsec
-- import qualified Text.ParserCombinators.Parsec as P
import Text.Parsec.Combinator hiding (chainl1)
import Text.Parsec.Prim as P
import Text.Parsec.Char hiding (satisfy)
import Text.Parsec.String
import Text.Parsec.Pos

main = putStrLn "hello"


-- p25

{-
type PositionalExpr = (Bounds, PositionalExpr')
data PositionalExpr'
  = Num Int
  | Add PositionalExpr PositionalExpr
  | Sub PositionalExpr PositionalExpr
  | Mul PositionalExpr PositionalExpr
  | Div PositionalExpr PositionalExpr
  deriving (Show)
-}

data ExprF r = Num Int
             | Add r r
             | Sub r r
             | Mul r r
             | Div r r
      deriving (Show)

-- newtype Expr           = Expr                    (ExprF Expr)
-- newtype PositionalExpr = PositionalExpr (Bounds, (ExprF PositionalExpr))


newtype Fix f = In { out :: f (Fix f) }
newtype Expr = Expr {runExpr :: Fix ExprF}

-- > runExpr (2+3 ∗ 4)
v = In {out = Add (In {out = Num 2})
               (In {out = Mul (In {out = Num 3})
                              (In {out = Num 4})})}

instance Num Expr where
  -- (Expr (In (Num a))) + (Expr (In (Num b))) = Expr (In (Add (In (Num a)) (In (Num b))))
  (Expr a) + (Expr b) = Expr (In (Add a b))
  (Expr a) - (Expr b) = Expr (In (Sub a b))
  (Expr a) * (Expr b) = Expr (In (Mul a b))
  -- (Expr a) / (Expr b) = Expr (In (Div a b))

  fromInteger a = Expr (In (Num $ fromIntegral a))
  signum _a = 0 -- ignore for now
  abs a = a -- ignore for now

instance Show (Fix ExprF) where
  show (In a) = "(In (" ++ show a ++ "))"

yy :: Expr
yy = Expr (In {out = Num 4})


-- ---------------------------------------------------------------------

-- p 26
data Ann x f a = Ann x (f a)

instance Functor f => Functor (Ann x f) where
   fmap f (Ann x t) = Ann x (fmap f t)

newtype PositionalExpr = PositionalExpr {runPositionalExpr :: Fix (Ann Bounds ExprF)}


type AnnFix  x f = Fix (Ann x f)
type AnnFix1 x f = f (AnnFix x f)

mkAnnFix :: x -> AnnFix1 x f -> AnnFix x f
-- mkAnnFix x ann1 = In (Ann x ann1)
mkAnnFix x = In . Ann x

unannotate :: Functor f => AnnFix x f -> Fix f
unannotate (In (Ann _ tree)) = In (fmap unannotate tree)

deriving instance Functor ExprF
{-
instance Functor ExprF where
  fmap _ (Num a) = Num a
  fmap f (Add a b) = Add (f a) (f b)
  fmap f (Sub a b) = Sub (f a) (f b)
  fmap f (Mul a b) = Mul (f a) (f b)
  fmap f (Div a b) = Div (f a) (f b)

-}

data ExprAlg a = ExprAlg
  { cataNum :: Int -> a
  , cataAdd :: a -> a -> a
  , cataSub :: a -> a -> a
  , cataMul :: a -> a -> a
  , cataDiv :: a -> a -> a
  }

{-
cataExpr :: ExprAlg a -> Fix ExprF -> a
cataExpr alg = f where
  f (In expr) = case expr of
    Num n -> cataNum alg n
    Add x y -> cataAdd alg (f x) (f y)
    Sub x y -> cataSub alg (f x) (f y)
    Mul x y -> cataMul alg (f x) (f y)
    Div x y -> cataDiv alg (f x) (f y)
-}

cataExpr :: (ExprF a -> a) -> Fix ExprF -> a
cataExpr f (In expr) = f (fmap (cataExpr f ) expr)

type Algebra f a = f a -> a
cata :: Functor f => Algebra f a -> Fix f -> a
cata f = f . fmap (cata f ) . out
-- cata f fp = f (fmap (cata f) (out fp))

exprEval0 :: Algebra ExprF Int
exprEval0 expr = case expr of
  Num n -> n
  Add x y -> x+y
  Sub x y -> x - y
  Mul x y -> x * y
  Div x y -> x `div` y

v3 = cata exprEval0 (runExpr (1 + 2 * 3))

-- ---------------------------------------------------------------------
 -- Section 5.2 p 30

exprEval' :: Algebra (Ann Bounds ExprF) (Either (Bounds, String) Int)
exprEval' (Ann z expr) = case expr of
  Num n -> Right n
  Add x y -> (+) <$> x <*> y
  Sub x y -> (-) <$> x <*> y
  Mul x y -> (*) <$> x <*> y
  Div x y -> do
     x' <- x
     y' <- y
     if y' == 0
       then Left (z, "division by zero")
       else Right (x' `div` y')

type ErrorAlgebra f e a = f a -> Either e a

exprEval :: ErrorAlgebra ExprF String Int
exprEval expr = case expr of
  Num n  -> Right n
  Add x y -> Right (x + y)
  Sub x y -> Right (x - y)
  Mul x y -> Right (x * y)
  Div x y
   | y == 0    -> Left "division by zero"
   | otherwise -> Right (x `div` y)

-- p31

-- class Traversable t where
--   traverse :: Applicative f => (a -> f b) -> t a -> f (t b)

deriving instance Foldable ExprF

instance Traversable ExprF where
  traverse f expr = case expr of
    Num n   -> pure (Num n)
    Add x y -> Add <$> f x <*> f y
    Sub x y -> Sub <$> f x <*> f y
    Mul x y -> Mul <$> f x <*> f y
    Div x y -> Div <$> f x <*> f y


cascade :: (Traversable f, Monoid e) => ErrorAlgebra f e a -> Algebra f (Except e a)
cascade alg expr = case sequenceA expr of
  Failed xs -> Failed xs
  OK tree'  -> case alg tree' of
    Left xs   -> Failed xs
    Right res -> OK res

errorCata :: Traversable f => ErrorAlgebra f e a -> AnnFix x f -> Except [(e, x)] a
errorCata alg (In (Ann x expr)) =
  case traverse (errorCata alg) expr of
    Failed xs  -> Failed xs
    OK expr'  -> case alg expr' of
       Left x' -> Failed [(x', x)]
       Right v -> OK v

------------------------------------------------------------------------
-- section 5.3 p 33

data ExprToken = TNum Int
               | TPlus
               | TMinus
               | TStar
               | TSlash
               | TPOpen
               | TPClose
               | TSpace String
             deriving (Show,Eq)

instance Symbol ExprToken where
  unparse (TNum v) = show v
  unparse TPlus = "+"
  unparse TMinus = "-"
  unparse TStar = "*"
  unparse TSlash = "/"
  unparse TPOpen = "("
  unparse TPClose = ")"
  unparse (TSpace s) = s


isSpace (TSpace _) = True
isSpace _ = False

isNum (TNum _) = True
isNum _ = False

-- type P = Parsec Char ()

tNum :: Parser ExprToken
tNum = do { ds <- many1 digit; return (TNum (read ds)) } <?> "number"

tPlus :: Parser ExprToken
tPlus = do { char '+'; return TPlus }

tMinus :: Parser ExprToken
tMinus = do { char '-'; return TMinus }

tStar :: Parser ExprToken
tStar = do { char '*'; return TStar }

tSlash :: Parser ExprToken
tSlash = do { char '/'; return TSlash }

tPOpen :: Parser ExprToken
tPOpen = do { char '('; return TPOpen }

tPClose :: Parser ExprToken
tPClose = do { char ')'; return TPClose }

tSpace :: Parser ExprToken
tSpace = do { ss <- many1 space; return (TSpace ss) }

pOneTok :: Parser ExprToken
pOneTok = tNum
    P.<|> tMinus
    P.<|> tStar
    P.<|> tSlash
    P.<|> tPOpen
    P.<|> tPClose
    P.<|> tSpace

{-


-- tp = parse pExpr "filename" "(1 + 2)"
-}
-- --------------------------------------------------------

-- p 34
collapse :: Symbol s => (s -> Bool) -> [s] -> [(s, Bounds)]
collapse space ts = collapse' (0, symbolSize lefts) space rest
  where (lefts, rest) = span space ts

collapse' :: Symbol s => Range -> (s -> Bool) -> [s] ->[(s, Bounds)]
collapse' _ _ [] = []
collapse' left space (t : ts) = new : collapse' right space rest
  where (_, leftInner) = left
        rightInner = leftInner + symbolSize t
        rightOuter = rightInner+symbolSize rights
        right = (rightInner, rightOuter)
        (rights, rest) = span space ts
        new = (t, Bounds left right)


class Symbol s where
  unparse :: s -> String
  symbolSize :: s -> Int
  symbolSize = length . unparse

instance Symbol s => Symbol [s] where
  unparse = concatMap unparse
  symbolSize = sum . fmap symbolSize


------------------

type P s = ParsecT [(s, Bounds)] Range

satisfy :: (Monad m, Symbol s) => (s -> Bool) -> P s m s
satisfy ok = do
  let pos _ (_, bounds) _ = newPos "" 0 (fst (rightMargin bounds)+1)
  let match x@(tok,_)
        | ok tok = Just x
        | otherwise = Nothing
  (tok, bounds) <- tokenPrim (unparse . fst) pos match
  setState (rightMargin bounds)
  return tok

{-
instance (Monad m) => Stream [(s, Bounds)] m (s, Bounds) where
  -- uncons :: s -> m (Maybe (t, s))
    uncons []     = return $ Nothing
    uncons (t:ts) = return $ Just (t,ts)
-}

getPos :: Monad m => P s m Range
getPos = getState


-- ---------------------------------------------------------------------

pToken :: (Monad m,Symbol s, Eq s) => s -> P s m s
pToken = satisfy . (==)

pExpr :: ExprParser (AnnFix Bounds ExprF)
pExpr = chainl1 pTerm (Add <$ pToken TPlus
                           P.<|>
                       Sub <$ pToken TMinus)
pTerm :: ExprParser (AnnFix Bounds ExprF)
pTerm = chainl1 pFactor
                   (Mul <$ pToken TStar
                      P.<|>
                    Div <$ pToken TSlash)

pFactor :: ExprParser (AnnFix Bounds ExprF)
pFactor = pNum
            P.<|>
          pToken TPOpen *> pExpr <* pToken TPClose

-- ---------------------------------------------------------------------
-- 5.3.3. p 36

type ExprParser = P ExprToken Identity

pNum :: ExprParser (AnnFix Bounds ExprF)
pNum = unit $ (\(TNum n) -> Num n) <$> satisfy isNum

unit :: Monad m => P s m (AnnFix1 Bounds f ) -> P s m (AnnFix Bounds f)
unit p = do
  left <- getPos
  x  <- p
  mkBounded left x

mkBounded :: Monad m => Range -> AnnFix1 Bounds f -> P s m (AnnFix Bounds f)
mkBounded left x = do
  right <- getPos
  return (mkAnnFix (Bounds left right) x)


chainl1 :: Monad m =>
     P s m (AnnFix Bounds f)
  -> P s m (AnnFix Bounds f -> AnnFix Bounds f -> AnnFix1 Bounds f)
  -> P s m (AnnFix Bounds f)

chainl1 px pf = do
  left <- getPos
  px >>= rest left
 where
  rest left = fix $ \loop x -> option x $ do
   f <- pf
   y <- px
   mkBounded left (f x y) >>= loop

chainr1 :: Monad m =>
     P s m (AnnFix Bounds f )
  -> P s m (AnnFix Bounds f -> AnnFix Bounds f -> AnnFix1 Bounds f )
  -> P s m (AnnFix Bounds f)
chainr1 px pf = fix $ \loop ->do
   left<- getPos
   x <- px
   option x $ do
     f <- pf
     y <- loop
     mkBounded left (f x y)

-- ---------------------------------------------------------------------

-- p39

data Zipper a = Zipper
  { zFocus :: a
  , zUp :: Maybe (Zipper a)
  , zLeft :: Maybe (Zipper a)
  , zRight :: Maybe (Zipper a)
  , zDown :: Maybe (Zipper a)
  }

enter :: Foldable f => Fix f -> Zipper (Fix f)
enter f = fromJust (enter' Nothing Nothing [f])


enter' :: Foldable f =>
     Maybe (Zipper (Fix f ))
  -> Maybe (Zipper (Fix f ))
  -> [Fix f]
  -> Maybe (Zipper (Fix f ))
enter' _ _ [] = Nothing
enter' up left (focus@(In f ) : fs) = here
   where
     here = Just (Zipper focus up left right down)
     right = enter' up here fs
     down = enter' here Nothing (toList f)

leave :: Zipper a -> a
leave z = maybe (zFocus z) leave (zUp z)

child :: Int -> Zipper a -> Maybe (Zipper a)
child 0 = zDown
child n = child (n-1) >=> zRight


data ExploreHints = ExploreHints
  { matchHere :: Bool
  , exploreDown :: Bool
  , exploreRight :: Bool
  }


deriving instance Foldable f => Foldable (Ann x f)

explore :: Foldable f => (x -> ExploreHints) -> AnnFix x f  -> [Zipper (AnnFix x f )]
explore hints = explore' hints . enter

explore' :: Foldable f => (x -> ExploreHints) -> Zipper (AnnFix x f ) -> [Zipper (AnnFix x f )]
explore' hints root = [z | (dirOk, zs) <- dirs, dirOk (hints x), z <- zs]
 where
  In (Ann x _) = zFocus root
  dirs = [(matchHere,[root])
         , (exploreDown, exploreMore (zDown root))
         , (exploreRight, exploreMore (zRight root))
         ]
  exploreMore = maybe [ ] (explore' hints)

selectByRange :: Foldable f => Range -> AnnFix Bounds f  -> Maybe (Zipper (AnnFix Bounds f))
selectByRange range@(left, _) = listToMaybe . reverse . explore hints
   where hints bounds@(Bounds _(ir, _)) =
           ExploreHints { matchHere = range `rangeInBounds` bounds
                        , exploreDown = range `rangeInRange` outerRange bounds
                        , exploreRight = left >= ir
                        }


findLeftmostDeepest :: Foldable f => (x -> Bool) -> (AnnFix x f ) -> Maybe (Zipper (AnnFix x f ))
findLeftmostDeepest down = listToMaybe . reverse . explore hints
  where
    hints x
      | down x    = ExploreHints True  True  False
      | otherwise = ExploreHints False False True

selectByPos :: Foldable f => Int -> AnnFix Bounds f -> Maybe (Zipper (AnnFix Bounds f ))
selectByPos pos = findLeftmostDeepest (posInRange pos . innerRange)



-------------------

repairBy :: (Foldable f ,Ord dist) =>  (Range -> Range -> dist) -> AnnFix Bounds f  -> Range -> Bounds
repairBy cost tree range = head (sortOn (cost range . innerRange) (validBounds tree))


sortOn :: Ord b => (a ->b) -> [a] -> [a]
sortOn = sortBy . comparing

validBounds :: Foldable f => AnnFix Bounds f -> [Bounds]
validBounds (In (Ann b f )) = b : concatMap validBounds (toList f )



repair :: Foldable f => AnnFix Bounds f -> Range -> Bounds
repair = repairBy distRange

-- distRange :: Range -> Range -> Int
-- distRange (l1, r1) (l2, r2) = abs (l1 -l2) + abs (r1 - r2)

newtype Nav = Nav {nav :: forall a . Zipper a -> Maybe (Zipper a)}

instance Monoid Nav where
   mempty = Nav return
   mappend (Nav n1) (Nav n2) = Nav (n1 >=> n2)


moveSelection :: Foldable f => AnnFix Bounds f -> Nav -> Range -> Maybe Bounds
moveSelection tree (Nav nav) range
   = (rootAnn . zFocus) <$> (selectByRange range tree >>= nav)


rootAnn :: AnnFix x f -> x
rootAnn (In (Ann x _)) = x

--------------------------


