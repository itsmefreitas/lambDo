module Utils where

import Parser

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
instance Show (Expr e) where
  show (Var v) = (show v)
  show (Const c) = (show c)
  show (Lambda s e) = "\\\\" ++ (show s) ++ "." ++ (show e)
  show (App t1 t2) = "(" ++ (show t1) ++ ") (" ++ (show t2) ++ ")"
  show (Let (l) (m) (n)) = "let " ++ (show l) ++ " = (" ++ (show m) ++ ") in (" ++ (show n) ++ ")"
  show (Constr (x,y)) = "cons(" ++ (show x) ++ "," ++ (show y) ++ ")"
  show (Prim (x) op (y)) = (show x) ++ (show op) ++ (show y)

-- Eq behavior for Expr e
instance Eq (Expr e) where
  (Var x) == (Var y) = x == y
  (Const a) == (Const b) = a == b
  (Lambda x (m)) == (Lambda y (n)) = (x == y) && (m == n)
  (App (m) (n)) == (App (l) (p)) = (m == l) && (n == p)
  (Let x n m) == (Let y p l) = (x == y) && (n == p) && (m == l)
  (Constr (x,y)) == (Constr (z,w)) = (x == z) && (y == w)
  (Prim (x) op1 (y)) == (Prim (z) op2 (k)) = (x == z) && (y == k) && (op1 == op2)