module Utils where

import Parser
import Common

-- Show behavior for Prim
instance Show (Op) where
  show (Plus) = " + "
  show (Minus) = " - "
  show (Times) = " * "
  show (Div) = " / "
  
instance Eq (Op) where
  (Plus) == (Plus) = True
  (Minus) == (Minus) = True
  (Times) == (Times) = True
  (Div) == (Div) = True
  (_) == (_) = False
  
-- Show behavior for Expr e
-- ASK: Can I have my show instance rewriting terms like (λx.(λy.x)y) to (λxy.xy)?
instance Show (Expr e) where
  show (T) = "True"
  show (F) = "False"
  show (Nil) = "∅"
  show (Var v) = [v]
  show (Const c) = show c
  show (Lambda s e) = "λ" ++ [s] ++ (showBody e)
  show (App t1 t2) = "(" ++ (show t1) ++ ") (" ++ (show t2) ++ ")"
  show (Let (l) (m) (n)) = "let " ++ (show l) ++ " = (" ++ (show m) ++ ") in (" ++ (show n) ++ ")"
  show (Constr (a) (e)) = "[" ++ (show a) ++ ":" ++ (show e) ++ "]"
  show (Prim (x) op (y)) = (show x) ++ (show op) ++ (show y)
  show (If (e) (e1) (e2)) = "if (" ++ (show e) ++ ") then (" ++ (show e1) ++ ") else (" ++ (show e2) ++ ")"

showBody :: Expr e -> [Char]
showBody (Lambda s e) = [s] ++ (showBody e)
showBody (App m (Var y)) = (showBody m) ++ [y]
showBody e = "." ++ (show e)

-- Eq behavior for Expr e
instance Eq (Expr e) where
  (T) == (T) = True
  (F) == (F) = True
  (Nil) == (Nil) = True
  (Var x) == (Var y) = x == y
  (Const a) == (Const b) = a == b
  (Lambda x (m)) == (Lambda y (n)) = (x == y) && (m == n)
  (App (m) (n)) == (App (l) (p)) = (m == l) && (n == p)
  (Let x n m) == (Let y p l) = (x == y) && (n == p) && (m == l)
  (Constr (a) (e)) == (Constr (b) (f)) = (a == b) && (e == f)
  (Prim (x) op1 (y)) == (Prim (z) op2 (k)) = (x == z) && (y == k) && (op1 == op2)
  (_) == (_) = False

lexData :: [Char] -> Expr e
lexData s = toData (lexer s)

lexNorm :: [Char] -> Expr e
lexNorm s = normalize (lexData s)