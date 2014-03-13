{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE TemplateHaskell       #-}

module ASTExpr where

import Generics.MultiRec.Base
import Generics.MultiRec.TH

-- * The AST type from the 'Generic Selections of Subexpressions' paper

-- -------------------------------

data Expr = EAdd Expr Expr
          | EMul Expr Expr
          | ETup Expr Expr
          | EIntLit Int
          | ETyped Expr Type
          deriving (Eq, Show)

data Type = TyInt
          | TyTup Type Type
          deriving (Eq, Show)

-- ** Index type

data Tuples :: * -> * where
  Expr  ::  Tuples Expr
  Type  ::  Tuples Type


$(deriveAll ''Tuples)
{-
src/ASTExpr.hs:1:1: Splicing declarations
    deriveAll ''Tuples
  ======>
    src/ASTExpr.hs:37:3-20
    data EAdd
    data EMul
    data ETup
    data EIntLit
    data ETyped
    instance Constructor EAdd where
      conName _ = "EAdd"
    instance Constructor EMul where
      conName _ = "EMul"
    instance Constructor ETup where
      conName _ = "ETup"
    instance Constructor EIntLit where
      conName _ = "EIntLit"
    instance Constructor ETyped where
      conName _ = "ETyped"
    data TyInt
    data TyTup
    instance Constructor TyInt where
      conName _ = "TyInt"
    instance Constructor TyTup where
      conName _ = "TyTup"

    type instance PF Tuples =
        :+: (:>: (:+: (C EAdd (:*: (I Expr) (I Expr))) (
        :+: (C EMul (:*: (I Expr) (I Expr))) (
        :+: (C ETup (:*: (I Expr) (I Expr))) (
        :+: (C EIntLit (K Int))
            (C ETyped ( :*: (I Expr) (I Type)))))))
            Expr)
       (:>:
        (:+: (C TyInt U)
             (C TyTup (:*: (I Type) (I Type))))
           Type)

    instance El Tuples Expr where
      proof = Expr

    instance El Tuples Type where
      proof = Type

    instance Fam Tuples where
      from Expr (EAdd f0 f1)
        = L (Tag (L (C ((:*:) ((I . I0) f0) ((I . I0) f1)))))
      from Expr (EMul f0 f1)
        = L (Tag (R (L (C ((:*:) ((I . I0) f0) ((I . I0) f1))))))
      from Expr (ETup f0 f1)
        = L (Tag (R (R (L (C ((:*:) ((I . I0) f0) ((I . I0) f1)))))))
      from Expr (EIntLit f0) = L (Tag (R (R (R (L (C (K f0)))))))
      from Expr (ETyped f0 f1)
        = L (Tag (R (R (R (R (C ((:*:) ((I . I0) f0) ((I . I0) f1))))))))
      from Type TyInt = R (Tag (L (C U)))
      from Type (TyTup f0 f1)
        = R (Tag (R (C ((:*:) ((I . I0) f0) ((I . I0) f1)))))
      to Expr (L (Tag (L (C (:*: f0 f1)))))
        = EAdd ((unI0 . unI) f0) ((unI0 . unI) f1)
      to Expr (L (Tag (R (L (C (:*: f0 f1))))))
        = EMul ((unI0 . unI) f0) ((unI0 . unI) f1)
      to Expr (L (Tag (R (R (L (C (:*: f0 f1)))))))
        = ETup ((unI0 . unI) f0) ((unI0 . unI) f1)
      to Expr (L (Tag (R (R (R (L (C f0))))))) = EIntLit (unK f0)
      to Expr (L (Tag (R (R (R (R (C (:*: f0 f1))))))))
        = ETyped ((unI0 . unI) f0) ((unI0 . unI) f1)
      to Type (R (Tag (L (C U)))) = TyInt
      to Type (R (Tag (R (C (:*: f0 f1)))))
        = TyTup ((unI0 . unI) f0) ((unI0 . unI) f1)

    instance EqS Tuples where
      eqS Expr Expr = Just Refl
      eqS Type Type = Just Refl
      eqS _ _ = Nothing
Ok, modules loaded: ASTExpr.
-}

