{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Modify ch6 to use an annotation of (Bounds,[ExprToken])

import Generics.MultiRec hiding ( (&), show )
import Generics.MultiRec.Base
-- import Generics.MultiRec.Fold
import Generics.MultiRec.HFix
import Generics.MultiRec.HFunctor
-- import qualified Generics.MultiRec.Fold as F
import Generics.MultiRec.FoldAlg as FA

import Control.Monad.Identity
import Control.Monad.State.Strict
import Data.Maybe
import Data.List.Ordered

import Annotations.Bounds
import Annotations.BoundsParser as BP
import Annotations.Except
import Annotations.ExploreHints
import Annotations.MultiRec.Annotated
import Annotations.MultiRec.Any
import Annotations.MultiRec.ParserCombinators
import Annotations.MultiRec.Yield
import Annotations.MultiRec.Zipper
import Annotations.MultiRec.ZipperFix
import Annotations.MultiRec.ShowFam

import Control.Applicative hiding (many)

import Text.Parsec.Combinator hiding (chainl1,chainl)
import qualified Text.Parsec.Prim as P
import Text.Parsec.Char hiding (satisfy)
import Text.Parsec.Error
import Text.Parsec.String
import Text.Parsec.Pos


main = putStrLn "hello"

-- ---------------------------------------------------------------------
-- chapter 6 p 50

data Expr = EAdd Expr Expr
          | EMul Expr Expr
          | ETup Expr Expr
          | EIntLit Int
          | ETyped Expr Type
          deriving (Eq, Show)

data Type = TyInt
          | TyTup Type Type
          deriving (Eq, Show)

-- Sums of products representation
type PFExpr =
      I Expr :*: I Expr :*: U  -- EAdd
  :+: I Expr :*: I Expr :*: U  -- EMul
  :+: I Expr :*: I Expr :*: U  -- ETup
  :+: K Int  :*: U             -- EIntLit
  :+: I Expr :*: I Type :*:U   -- ETyped

type PFType =
      U                        -- TyInt
  :+: I Type :*: I Type :*:U   -- TyTup

-- The pattern family
type PFTuples =
      PFExpr :>: Expr
  :+: PFType :>: Type


-- Index type phi
data Tuples :: * -> * where
   Expr :: Tuples Expr
   Type :: Tuples Type

-- In this declaration phi stands for Tuples
-- type family PF phi :: (* -> *) -> * -> *
-- | Type family describing the pattern functor of a family.
-- type family PF (phi :: * -> *) :: (* -> *) -> * -> *

type instance PF Tuples = PFTuples

------------------------------------------------------------------------

instance Fam Tuples where
  from Expr ex = L . Tag $ case ex of
    EAdd x y   -> L             $ I (I0 x) :*: I (I0 y) :*: U
    EMul x y   -> R . L         $ I (I0 x) :*: I (I0 y) :*: U
    ETup x y   -> R . R . L     $ I (I0 x) :*: I (I0 y) :*: U
    EIntLit n  -> R . R . R . L $ K n      :*: U
    ETyped e t -> R . R . R . R $ I (I0 e) :*: I (I0 t) :*: U
  from Type ty = R . Tag $ case ty of
     TyInt     -> L $ U
     TyTup x y -> R $ I (I0 x) :*: I (I0 y) :*: U

  to Expr (L (Tag ex)) = case ex of
    L (I          (I0 x) :*: I (I0 y) :*: U)    -> EAdd x y
    R (L (I       (I0 x) :*: I (I0 y) :*: U))   -> EMul x y
    R (R (L (I    (I0 x) :*: I (I0 y) :*: U)))  -> ETup x y
    R (R (R (L    (K n                :*: U)))) -> EIntLit n
    R (R (R (R (I (I0 x) :*: I (I0 y) :*: U)))) -> ETyped x y
  to Type (R (Tag ty)) = case ty of
    L U -> TyInt
    R (I (I0 x) :*: I (I0 y) :*: U) -> TyTup x y


instance El Tuples Expr where
  proof = Expr

instance El Tuples Type where
  proof = Type


-- ---------------------------------------------------------------------

instance ShowFam Tuples where
  showFam Expr (EAdd e1 e2) = "(EAdd " ++ (showFam Expr e1) ++ " " ++ (showFam Expr e2) ++ ")"
  showFam Expr (EMul e1 e2) = "(EMul " ++ (showFam Expr e1) ++ " " ++ (showFam Expr e2) ++ ")"
  showFam Expr (ETup e1 e2) = "(ETup " ++ (showFam Expr e1) ++ " " ++ (showFam Expr e2) ++ ")"
  showFam Expr (EIntLit e1) = "(EIntlit " ++ (show e1) ++ ")"
  showFam Expr (ETyped e1 t1) = "(ETyped " ++ (showFam Expr e1) ++ " " ++ (showFam Type t1) ++ ")"

  showFam Type TyInt = "TyInt"
  showFam Type (TyTup t1 t2) = "(ETyTup " ++ (showFam Type t1) ++ " " ++ (showFam Type t2) ++ ")"

-- ---------------------------------------------------------------------

-- p 55

-- Note: K x is the annotation
-- type AnnFix  x φ = HFix (K x :*: PF φ)
-- type AnnFix1 x φ = (PF φ) (AnnFix x φ)


-- p57
type ErrorAlgPF f e a = forall ix.f (K0 a) ix -> Either e a

errorCata :: (HFunctor φ f )
  => ErrorAlgPF f e r
  -> φ ix
  -> HFix (K x :*: f ) ix
  -> Except [(e, x)] r
errorCata alg pf (HIn (K k :*: f )) =
  case hmapA (\pg g -> K0 <$> errorCata alg pg g) pf f of
    Failed xs -> Failed xs
    OK expr' -> case alg expr' of
      Left x' -> Failed [(x', k)]
      Right v -> OK v

type family ErrorAlg
  (f :: (* -> *) -> * -> *) -- pattern functor
  (e :: *) -- error type
  (a :: *) -- result type
  :: *     -- resulting algebra type

type instance ErrorAlg  U            e a = Either e a
type instance ErrorAlg (K b  :*: f ) e a = b -> ErrorAlg f e a
type instance ErrorAlg (I xi :*: f ) e a = a -> ErrorAlg f e a

type instance ErrorAlg (f :+: g)  e a = (ErrorAlg f e a, ErrorAlg g e a)
type instance ErrorAlg (f :>: xi) e a = ErrorAlg f e a

-- ---------------------------------------------------------------------

type ExprErrorAlg e a
  =   (a -> a -> Either e a) -- EAdd
  :&: (a -> a -> Either e a) -- EMul
  :&: (a -> a -> Either e a) -- ETup
  :&: (Int    -> Either e a) -- EIntLit
  :&: (a -> a -> Either e a) -- ETyped

type TypeErrorAlg e a
  =   (Either e a)           -- TyInt
  :&: (a -> a -> Either e a) -- TyTup

infixr 5 :&:
-- Note: This is a type synonym, so normal tuple processing stuff will
--       still work
type (:&:) = (,)


class MkErrorAlg f where
   mkErrorAlg :: ErrorAlg f e a -> ErrorAlgPF f e a

instance MkErrorAlg U where
  mkErrorAlg x U = x

instance MkErrorAlg f => MkErrorAlg (K a :*: f ) where
  mkErrorAlg alg (K x :*: f ) = mkErrorAlg (alg x) f

instance MkErrorAlg f => MkErrorAlg (I xi :*: f ) where
  mkErrorAlg alg (I (K0 x) :*: f ) = mkErrorAlg (alg x) f

instance MkErrorAlg f => MkErrorAlg (f :>: xi) where
  mkErrorAlg alg (Tag f ) = mkErrorAlg alg f

instance (MkErrorAlg f, MkErrorAlg g) => MkErrorAlg (f :+: g) where
  mkErrorAlg (algf, _) (L x) = mkErrorAlg algf x
  mkErrorAlg (_, algg) (R y) = mkErrorAlg algg y

-- --------------------------

inferType :: ExprErrorAlg String Type :&: TypeErrorAlg String Type
inferType = ( equal "+" -- EAdd
            & equal "*" -- EMul
            & tup       -- ETup
            & const (Right TyInt) -- EIntLit
            & equal "::")   -- ETyped
           &
            (Right TyInt -- TyInt
            & tup)       -- TyTup
  where
    equal op ty1 ty2
      | ty1 == ty2 = Right ty1
      | otherwise = Left ("lhs and rhs of "++ op ++ " must have equal types")
    tup ty1 ty2 = Right (TyTup ty1 ty2)


{- When we have implemented readExpr...
-- p 59

>let expr1 = readExpr "(1, (2, 3))"
>errorCata (mkErrorAlg inferType) Expr expr1 OK (TyTup TyInt (TyTup TyInt TyInt))

-}

------------------------------------------------------------------------
-- section 6.6 constructing recursively annotated trees p 60

mkAnnFix :: x -> AnnFix1 x s ix -> AnnFix x s ix
mkAnnFix x = HIn . (K x :*:)

{-

Parsing "2+3"

First push EIntLit 2, then EIntLit 3 and finally EAdd (EIntLit 2) (EIntLit 3).
-}


{-

class Monad m => MonadYield m where
  type ΦYield m :: * -> *
  type AnnType m:: *
  yield :: ΦYield m ix -> AnnType m -> ix -> m ix

-- Value to be pushed on the parse stack
-- data AnyF φ f where
--   AnyF :: φ ix -> f ix -> AnyF φ f

-- type AnyAnnFix x φ = AnyF φ (AnnFix x φ)


newtype YieldT x φ m a = YieldT (StateT [AnyAnnFix x φ] m a) deriving (Functor,Monad)

instance MonadTrans (YieldT x φ) where
  lift = YieldT . lift

instance (Monad m, HFunctor φ (PF φ), EqS φ,Fam φ) => MonadYield (YieldT x φ m) where
  type ΦYield (YieldT x φ m) = φ
  type AnnType (YieldT x φ m) = x
  yield = doYield


doYield :: (Monad m, HFunctor φ (PF φ), EqS φ,Fam φ) => φ ix -> x -> ix -> YieldT x φ m ix
doYield p bounds x = YieldT $ do
  let pfx = from p x
  let n = length (children p pfx)
  stack <- get
  if length stack < n
    then error $ "structure mismatch: required "++ show n
              ++ " accumulated children but found only "++ show (length stack)
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
    AnyF p2 x : xs' -> case eqS p1 p2 of
       Nothing -> error "structure mismatch: incompatible child type"
       Just Refl -> do put xs'; return x
-}

-- ----------------------------------------------------
-- section 6.7 parsing   p 64

-- Note: this Monad stack make use of Parsec 'try' dangerous as it may
-- yield values before discarding the parse leg
-- type YP s φ m = P s (YieldT Bounds φ m)


instance EqS Tuples where
  eqS Expr Expr = Just Refl
  eqS Type Type = Just Refl
  eqS _    _    = Nothing


data ExprToken = TIntLit Int
               | TPlus
               | TMinus
               | TStar
               | TSlash
               | TLParen
               | TRParen
               | TSpace String
               | TComma
               | TDoubleColon
               | TInt
             deriving (Show,Eq)

instance Symbol ExprToken where
  unparse (TIntLit v) = show v
  unparse TPlus = "+"
  unparse TMinus = "-"
  unparse TStar = "*"
  unparse TSlash = "/"
  unparse TLParen = "("
  unparse TRParen = ")"
  unparse (TSpace s) = s
  unparse TComma = ","
  unparse TDoubleColon = "::"
  unparse TInt = "Int"

isIntLit (TIntLit _) = True
isIntLit _ = False

isSpace (TSpace _) = True
isSpace _          = False

-- ---------------------------------------------------------------------

-- Lexical analysis

tIntLit :: Parser ExprToken
tIntLit = do { ds <- many1 digit; return (TIntLit (read ds)) } P.<?> "number"

tPlus :: Parser ExprToken
tPlus = do { char '+'; return TPlus }

tMinus :: Parser ExprToken
tMinus = do { char '-'; return TMinus }

tStar :: Parser ExprToken
tStar = do { char '*'; return TStar }

tSlash :: Parser ExprToken
tSlash = do { char '/'; return TSlash }

tLParen :: Parser ExprToken
tLParen = do { char '('; return TLParen }

tRParen :: Parser ExprToken
tRParen = do { char ')'; return TRParen }

tSpace :: Parser ExprToken
tSpace = do { ss <- many1 space; return (TSpace ss) }

tComma :: Parser ExprToken
tComma = do { char ','; return TComma }

tDoubleColon :: Parser ExprToken
tDoubleColon = do { string "::"; return TDoubleColon }

tInt :: Parser ExprToken
tInt = do { string "Int"; return TInt }

pOneTok :: Parser ExprToken
pOneTok = tIntLit
    P.<|> tPlus
    P.<|> tMinus
    P.<|> tStar
    P.<|> tSlash
    P.<|> tLParen
    P.<|> tRParen
    P.<|> tSpace
    P.<|> tComma
    P.<|> tDoubleColon
    P.<|> tInt

pManyToks :: Parser [ExprToken]
pManyToks = P.many pOneTok

pM = undefined

tFoo :: P (String,Bounds) Identity ExprToken
tFoo = do
  -- string "::"
  return TDoubleColon

{-
pO :: P ExprToken Identity (ExprToken,Bounds)
pO = do
  _ <- tFoo
  satisfy (\_ -> True)
-}

-- parseTokens :: String -> Either ParseError [ExprToken]
-- parseTokens :: String -> BP.P ExprToken Identity [(ExprToken,Bounds)]
-- parseTokens :: String -> BP.P ExprToken Identity a
parseTokens str =
 case P.parse pManyToks "string" str of
  Left _ -> []
  Right toks -> toks

{-
parseTokens str = do
  let pr = runParser pManyToks [] "src" str
  case pr of
    Left err -> undefined
    -- Right toks -> return $ collapse isSpace toks
    -- Right toks -> toks
    Right toks -> undefined
-}

pp = parseTokens "1 + 2"

ppp :: [(ExprToken, Bounds)]
ppp = collapse isSpace pp

{-
ppp = do
  v <- runParsecT [] pp
  show v
-}

-- ---------------------------------------------------------------------

type ExprParser = YP ExprToken Tuples Identity


pExpr :: ExprParser Expr
pExpr = do
  left <- getPos
  ex <- pAdd
  option ex $ do
    pToken TDoubleColon
    ty <- pType
    mkBounded Expr left (ETyped ex ty)

pAdd :: ExprParser Expr
pAdd = chainl Expr pMul (EAdd <$ pToken TPlus)

pMul :: ExprParser Expr
pMul = chainl Expr pFactor (EAdd <$ pToken TStar)

pFactor :: ExprParser Expr
pFactor = pIntLit P.<|> pTupleVal

pIntLit :: ExprParser Expr
pIntLit = unit Expr $ (\(TIntLit n) -> EIntLit n) <$> satisfy isIntLit

pTupleVal :: ExprParser Expr
pTupleVal = pTuple Expr pExpr ETup

pType :: ExprParser Type
pType = pTyInt P.<|> pTyTuple

pTyInt :: ExprParser Type
pTyInt = unit Type $ TyInt <$ pToken TInt

pTyTuple :: ExprParser Type
pTyTuple = pTuple Type pType TyTup

pTuple :: Tuples ix -> ExprParser ix -> (ix -> ix -> ix) -> ExprParser ix
pTuple w pEl f = do
  left <- getPos
  pToken TLParen
  lhs <- pEl
  ty <- option lhs $ do
     pToken TComma
     rhs <- pEl
     mkBounded w left (f lhs rhs)
  pToken TRParen
  return ty


-- -----------

  -- pn

-- pn = runYieldT Tuples

-- type ExprParser = YP ExprToken Tuples Identity
-- type YP s         fam    m        = P s         (YieldT Bounds fam    m)
-- so   YP ExprToken Tuples Identity = P ExprToken (YieldT Bounds Tuples Identity)

-- type P s
--      = ParsecT [(s,         Bounds)] Range
-- so   P ExprToken (YieldT Bounds Tuples Identity)
--      = ParsecT [(ExprToken, Bounds)] Range (YieldT Bounds Tuples Identity)
-- newtype ParsecT s u m a
--   So s = [(ExprToken, Bounds)]
--      u = Range
--      m = (YieldT Bounds Tuples Identity)
--      a = Expr

-- runYieldT :: fam   a     -> YieldT x      fam    m        a    -> m        (Maybe (AnnFix x      fam    a)
--              Tuples a    -> YieldT Bounds Tuples Identity a    -> Identity (Maybe (AnnFix Bounds Tuples a) 
-- We need a = Expr
--              Tuples Expr -> YieldT Bounds Tuples Identity Expr -> Identity (Maybe (AnnFix Bounds Tuples Expr) 

-- pExpr :: ExprParser Expr



g :: Tuples Expr
g = Expr

ff = runYield g

-- newtype YieldT x fam m a
--   = Annotations.MultiRec.Yield.YieldT (StateT [AnyAnnFix x fam] m a)

xx :: YieldT Bounds Tuples Identity Expr
xx = undefined

gg :: Maybe (AnnFix Bounds Tuples Expr)
gg = runIdentity $ runYieldT g xx

ggg :: Identity (Maybe (AnnFix Bounds Tuples Expr))
ggg = runYieldT g xx

initState :: [(ExprToken, Bounds)] -> P.State [(ExprToken, Bounds)] Range
initState toks
  = P.State
   { P.stateInput = toks
   , P.statePos   = initialPos "src"
   , P.stateUser  = (0,0)
   }


hh ::
  -- P.State [(ExprToken, Bounds)] Range
  -- ->
    YieldT
       Bounds -- annotation
       Tuples -- fam
       Identity -- m
       (P.Consumed
          (YieldT
             Bounds Tuples Identity (P.Reply [(ExprToken, Bounds)] Range Expr)))

hh = P.runParsecT pExpr (initState [])

-- ii = runIdentity $ runYieldT g hh

-- jj = (runParsecT (runYieldT g pExpr) initState)

-- jj ::
--   YieldT
--     Bounds
--     Tuples
--     Identity
--     (YieldT
--        Bounds Tuples Identity (Reply [(ExprToken, Bounds)] Range Expr))
jj = do
  x <- P.runParsecT pExpr (initState [])
  let x' = case x of
        P.Consumed a -> a
        P.Empty a -> a
  --let y = case runYieldT g x' of
  --         yy -> yy
           -- Ok a b c -> (a,b,c)
           -- Error e -> error "parse error"

  -- y <- runIdentity $ runYieldT g x'
  -- y <- runIdentity $ runYieldT g x'
  -- y <- runIdentity $ runYieldT x'
  return x'

-- readExpr :: String -> AnnFix Bounds Tuples Expr
-- readExpr str = parse pExpr "src"
-- readExpr :: String -> YieldT Bounds Tuples Identity Expr
readExpr' :: String -> YieldT Bounds Tuples Identity Expr
readExpr' str = do
  -- let toks = []
  let toks = parseTokens str
  let toks' = collapse isSpace toks

  x <- P.runParsecT pExpr (initState toks')
  x' <- case x of
         P.Consumed a -> a
         P.Empty a -> a
  (p',q',r') <- case x' of
          P.Ok p q r -> return (p,q,r)
          P.Error e -> error $ "parse error:" ++ show e
  -- x''' <- x''
  -- x''' <- runYieldT g x''
  return p'


-- type Annot = Bounds

readExpr :: String -> AnnFix Bounds Tuples Expr
readExpr str =
  case runIdentity $ runYieldT g (readExpr' str) of
     Nothing -> error "parse failed"
     Just r -> r

{-
>let expr1 = readExpr "(1, (2, 3))"
 >errorCata (mkErrorAlg inferType) Expr expr1
 OK (TyTup TyInt (TyTup TyInt TyInt))
-}

expr1 :: AnnFix Bounds Tuples Expr
expr1 = readExpr "(1, (2, 3))"

ee = errorCata (mkErrorAlg inferType) Expr expr1

{-
>let expr2 = readExpr "(1 :: (Int, Int), 2 + (3, 4))"
 >errorCata (mkErrorAlg inferType) Expr expr2
 Failed
[("lhs and rhs of :: must have equal types", Bounds {leftMargin = (1, 1), rightMargin = (16, 16)})
, ("lhs and rhs of + must have equal types"
-}

expr2 = readExpr "(1 :: (Int, Int), 2 + (3, 4))"
ee2 = errorCata (mkErrorAlg inferType) Expr expr2

-- ---------------------------------------------------------------------

-- Playing with Algebra's.

data RV = RVE Expr | RVT Type deriving Show

-- Just return the tree, without an annotation
stripAnnot :: ExprErrorAlg String RV :&: TypeErrorAlg String RV
stripAnnot = ( eadd    -- EAdd
             & emul    -- EMul
             & etup    -- ETup
             & eint    -- EIntLit
             & etyped) -- ETyped
           &
            ( etyint  -- TyInt
            & etytup) -- TyTup
  where
    eadd (RVE r1) (RVE r2)   = Right (RVE $ EAdd r1 r2)
    emul (RVE r1) (RVE r2)   = Right (RVE $ EMul r1 r2)
    eint r1                  = Right (RVE $ EIntLit r1)
    etup (RVE ty1) (RVE ty2) = Right (RVE $ ETup ty1 ty2)
    -- etyped r1 r2 = Right (ETyped r1 r2)
    etyped (RVE r1)  (RVT r2) = Right (RVE $ ETyped r1 r2)

    etyint       = Right (RVT TyInt)
    etytup (RVT r1) (RVT r2) = Right (RVT $ TyTup r1 r2)

es = errorCata (mkErrorAlg stripAnnot) Expr expr1

-- ---------------------------------------------------------------------

-- Zippers ch 6.8 p 67

-- type AnnZipper φ x = FixZipper φ (K x :*: PF φ)

-- focusAnn :: AnnZipper φ x ix -> x
-- focusAnn = on (\ (HIn (K x :*: _)) -> x)

-- instance (Zipper Tuples f) where




myenter ::  Zipper phi f => phi ix -> r ix -> Loc phi f r ix
myenter = undefined

zenter :: Zipper φ f => φ ix -> HFix f ix -> FixZipper φ f ix
zenter = enter

z1 :: FixZipper Tuples (K Bounds :*: PFTuples) Expr
z1 = zenter Expr expr1

f1 = focusAnn z1

-- explore :: Zipper φ (PF φ)⇒ φ ix→(x→ExploreHints)→(AnnFix x φ) ix→[AnnZipper φ x ix] explore p hints = explore? hints ◦ enter p

selectByRange :: Zipper φ (PF φ) => φ ix -> Range -> AnnFix Bounds φ ix -> Maybe (AnnZipper φ Bounds ix)
selectByRange p range@(left, _) = listToMaybe . reverse . explore p hints
  where
    hints bounds@(Bounds _ (ir, _)) =
      ExploreHints
       { matchHere   = range `rangeInBounds` bounds
       , exploreDown = range `rangeInRange` outerRange bounds
       , exploreRight = left >= ir
       }

selectByPos :: (Zipper φ (PF φ)) => φ ix -> Int -> AnnFix Bounds φ ix -> Maybe (AnnZipper φ Bounds ix)
selectByPos p pos = findLeftmostDeepest p (posInRange pos . innerRange)

repairBy :: (Ord dist, HFunctor φ (PF φ)) => φ ix -> (Range -> Range -> dist) -> AnnFix Bounds φ ix -> Range -> Bounds
repairBy p cost tree range = head (sortOn (cost range . innerRange) (allAnnotations p tree))

repair :: HFunctor φ (PF φ) => φ ix -> AnnFix Bounds φ ix -> Range -> Bounds
repair p = repairBy p distRange

moveSelection :: Zipper φ (PF φ) => φ ix -> AnnFix Bounds φ ix -> Nav -> Range -> Maybe Bounds
moveSelection p tree nav range = focusAnn <$> (selectByRange p range tree >>= nav)

-- -------------------------------------------------------------------1

-- Simplest solution, closes to GHC: convert
-- (AnnFix Bounds Tuples Expr) to
-- (AnnFix (Bounds,[ExprToken] Tuples Expr)
{-
:i AnnFix
type AnnFix x s = HFix (K x :*: PF s)
  	-- Defined in `Annotations.MultiRec.Annotated'
:i HFix
data HFix h ix = HIn {hout :: h (HFix h) ix}
  	-- Defined in `Generics.MultiRec.HFix'

so
AnnFix Bounds Tuples Expr = HFix (K Bounds :*: PF Tuples) Expr
-}
type Annot = (Bounds,[ExprToken])

addToks ::
     [(ExprToken,Bounds)]
  -> AnnFix Bounds Tuples Expr -- HFix (K Bounds :*: PF Tuples)
  -> AnnFix Annot  Tuples Expr -- HFix (K Annot :*: PF Tuples)
  -- -> AnnFix Bounds  Tuples Expr -- HFix (K Annot :*: PF Tuples)
addToks btoks fp = addToks' p fp
  where
    p = Expr

    -- Note: p parameter has to be able to vary as we recurse into the family
    addToks' :: HFunctor s (PF s) =>
        s ix
     -> AnnFix Bounds s ix -- HFix (K Bounds :*: PF Tuples)
     -> AnnFix Annot  s ix -- HFix (K Annot :*: PF Tuples)
    addToks' p fp' = HIn {- $ xform -}
                 -- $ hmap addToks' p
                 $ hmap addToks' p
                 -- $ xx
                 $ xform
                 $ hout fp'

    xx :: (f :*: g) r ix -> (f :*: g) r ix
    xx (x :*: y) = (x :*: y)

{-
addToks btoks fp = HIn r
  where
    f1 = hout fp
    f2 = hmap Expr xform f2
    r = undefined
-}

xform :: (K Bounds :*: g) r ix -> (K Annot :*: g) r ix
xform (b :*: x) = K (unK b,[]) :*: x

{-
*Main> :i AnnFix
type AnnFix x s = HFix (K x :*: PF s)
  	-- Defined in `Annotations.MultiRec.Annotated'
-}

getToksForBounds :: [(ExprToken,Bounds)] -> Bounds -> [ExprToken]
getToksForBounds btoks pos = map fst $ filter p btoks
  where
    pos' = outerRange pos
    -- p (_,b) = rangeInBounds pos' b
    p (_,b) = rangeInRange (outerRange b) pos'


parseToks :: String -> [(ExprToken, Bounds)]
parseToks = collapse isSpace . parseTokens

btoks1 = parseToks "(1, (2, 3))"

b1 = Bounds {leftMargin = (1,1), rightMargin = (2,2)}
b2 = Bounds {leftMargin = (1,1), rightMargin = (3,4)}

--------------

-- From http://hackage.haskell.org/package/Annotations-0.2/docs/src/Annotations-MultiRec-Annotated.html

-- | Removes all annotations from a recursively annotated fixpoint.
unannotate' :: HFunctor s (PF s) => s ix -> AnnFix x s ix -> HFix (PF s) ix
-- unannotate' p = HIn . hmap unannotate p . snd' . hout
-- unannotate' p fp = (HIn . hmap unannotate p . snd' . hout) fp
unannotate' p fp = HIn $ hmap unannotate' p $ snd' $ hout fp

fst' :: (f :*: g) r ix -> f r ix
fst' (x :*: _) = x

snd' :: (f :*: g) r ix -> g r ix
snd' (_ :*: y) = y
