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
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}

import qualified GHC.SYB.Utils         as SYB

import qualified GHC        as GHC
import qualified HsDecls    as GHC

import Generics.MultiRec hiding ( (&), show )

import Generics.MultiRec.Base
-- import Generics.MultiRec.Fold
import Generics.MultiRec.HFix
import Generics.MultiRec.HFunctor
-- import qualified Generics.MultiRec.Fold as F
import Generics.MultiRec.FoldAlg as FA
import qualified GHC.Generics as G
import qualified Generics.Deriving.Base as GD

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

import Language.Haskell.GhcMod
import Language.Haskell.Refact.API


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

-- ---------------------------------------------------------------------

deriving instance G.Generic Expr
deriving instance G.Generic Type

data MyDescriptor = MD
  {
  pfTypes :: (Expr,Type)
  }

-- We need index type, PF, Fam and El instances, coming from GHC.Generics


main = do
  cradle <- findCradle
  putStrLn $ "cradle=" ++ show cradle
  let settings = defaultSettings { rsetVerboseLevel = Debug }
  runRefacSession settings cradle comp

comp :: RefactGhc [ApplyRefacResult]
comp = do
  getModuleGhc "ch6-hare.hs"
  (r,_) <- applyRefac genPFEtc RSAlreadyLoaded
  return [r]

-- We need index type, PF, Fam and El instances
genPFEtc :: RefactGhc ()
genPFEtc = do
  renamed <- getRefactRenamed
  let pos = (97,8) -- location of MyDescriptor
  let Just (GHC.L _ n) = locToName pos renamed
  let res = definingTyClDeclsNames [n] renamed
  logm $ "res=" ++ showGhc res

  let (GHC.L _ (GHC.TyDecl _n _v decl _fvs)) = head res
  logm $ "decl=" ++ showGhc decl
  let (GHC.TyData _ _ctx _ct _ks cons _ds) = decl
  logm $ "cons=" ++ showGhc cons

  [pfTypesName] <- GHC.parseName "pfTypes"
  logm $ "pfTypesName=" ++ showGhc pfTypesName

  let mdcon = head cons


  -- logm $ "mdcon=" ++ showGhc mdcon
  -- logm $ "pfTypesName=" ++ showGhc pft

  let (GHC.L _ (GHC.ConDecl _ _ _ _ dets _ _ _)) = mdcon
  logm $ "dets=" ++ showDets dets

  let (GHC.RecCon [GHC.ConDeclField _n bt _]) = dets
  -- logm $ "bt=" ++ showGhc bt
  logm $ "bt=" ++ (SYB.showData SYB.Renamer 0 bt)


  return ()

filterCons :: GHC.Name -> [GHC.LConDecl GHC.Name] -> [GHC.LConDecl GHC.Name]
filterCons n cds = filter check cds
  where
    check (GHC.L _ (GHC.ConDecl (GHC.L _ cn) _ _ _ _ _ _ _)) = cn == n



-- showDets (GHC.HsConDetails bt fs) = "(HsConDetails " ++ showGhc bt ++ " " ++ showGhc fs ++ ")"
showDets (GHC.PrefixCon bts) = "(PrefixCon " ++ showGhc bts ++ ")"
showDets (GHC.RecCon fs) = "(RecCon " ++ showGhc fs ++ ")"
showDets (GHC.InfixCon bt1 bt2) = "(InfixCon " ++ showGhc bt1 ++ " " ++ showGhc bt2 ++ ")"
