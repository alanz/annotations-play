-- Based on ch 4 of 'Generic Selections of Subexpressions'
-- by M van Steenbergen

import Annotations.Bounds
-- import Data.Tree
import Control.Applicative

main = putStrLn "hello"


-- p 21
type ParseTree a = Rose (Bounds, a)
data Rose a = Rose a [Rose a]
            deriving (Show)

data BareExpr = Num Int
              | Add BareExpr BareExpr
              | Sub BareExpr BareExpr
              | Mul BareExpr BareExpr
              | Div BareExpr BareExpr
             deriving (Eq,Show)

-- The parse tree for the sentence "1 + 2 * 3" looks like this

example :: ParseTree BareExpr
example =
  let one = Num 1
      two = Num 2
      three = Num 3
      mul = Mul two three
      add = Add one mul
  in Rose (Bounds (0, 0) (9, 9), add)
          [Rose (Bounds (0, 0) (1, 2), one) [ ],
           Rose (Bounds (3, 4) (9, 9), mul)
             [Rose (Bounds (3, 4) (5, 6), two) [ ],
              Rose (Bounds (7, 8) (9, 9), three) [ ]
             ]
          ]

eval :: ParseTree BareExpr -> Either Bounds Int
eval (Rose (bounds, expr) cs) =
  case (expr, cs) of
   (Num n,[])  -> pure n
   (Add _ _, [x, y]) -> (+) <$> eval x <*> eval y
   (Sub _ _, [x, y]) -> (-) <$> eval x <*> eval y
   (Mul _ _, [x, y]) -> (*) <$> eval x <*> eval y
   (Div _ _, [x, y]) -> do
     x' <- eval x
     y' <- eval y
     case y' of
       0 -> Left bounds
       _ -> pure (x' `div` y')


