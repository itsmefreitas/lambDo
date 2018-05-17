module Launchbury where

import Data.List
import Utils
import Common

-- Ask: why was the last definition not working with guards?

constApp :: Op -> Expr e -> Expr e -> Expr e
constApp Plus c1 c2 = (Const ((getConst c1)+(getConst c2)))
constApp Minus c1 c2 = (Const ((getConst c1)-(getConst c2)))
constApp Times c1 c2 = (Const ((getConst c1)*(getConst c2)))
constApp Div c1 c2 = (Const (quot (getConst c1) (getConst c2)))
constApp Eql c1 c2 = if (c1 == c2) then T else F

-- ASK: Not sure about how to deal with case rule and which examples to use while testing...
-- ASK: Can we use the constructors to perform operations such as map (+1) [1,2,3] a la Haskell?

evalLaunch :: [(Char, (Expr e))] -> Expr e -> ([(Char, (Expr e))], Expr e)
evalLaunch h (T) = (h, T)
evalLaunch h (F) = (h, F)
evalLaunch h (Nil) = (h, Nil)
evalLaunch h (Constr (x) (y)) = (h, (Constr (x) (y)))
evalLaunch h (Lambda x e) = (h, (Lambda x e))
evalLaunch h (Const c) = (h, (Const c))
evalLaunch h (Var x)
  | (b /= []) = evalLaunch ((x,n):(h \\ b)) (e)
  | otherwise = (h, (Var x))
  where b = (getBinding h x)
        e = snd (head b)
        v = evalLaunch (h \\ b) (e)
        n = snd v
evalLaunch h (Let (Var x) n m) =  evalLaunch ((x,n):h) m
evalLaunch h (App m (Var x)) = evalLaunch (delta) (sub (eprime) (Var x) lvar)
  where lresult = evalLaunch (h) m
        lexpr = (snd lresult)
        delta = (fst lresult)
        eprime = getExpr lexpr
        lvar = getVar lexpr
evalLaunch h (Prim (m) op (n)) = ((theta), (constApp op (c1) (c2)))
  where n1 = evalLaunch h m
        delta = (fst n1)
        n2 = evalLaunch (delta) n
        theta = (fst n2)
        c1 = (snd n1)
        c2 = (snd n2)
evalLaunch h (If (e) (e1) (e2))
  | (eprime == T) = evalLaunch (delta) (e1)
  | (eprime == F) = evalLaunch (delta) (e2)
  where lresult = evalLaunch h e
        eprime = (snd  lresult)
        delta = (fst lresult)
evalLaunch h (Case e ((Nil),(e1)) ((Constr (y1) (ys)),(e2)))
  | (isNil eprime) = evalLaunch (delta) (e1)
  | (isConstr eprime) = evalLaunch (delta) (sub (sub (e2) (x) (getCVar y1)) (xs) (getCVar ys))
  where lresult = evalLaunch h e
        eprime = (snd lresult)
        delta = (fst lresult)
        x = (getCFst eprime)
        xs = (getCSnd eprime)

-- FIXME: polymorphic behaviour for (App () ()), evaluation MUST continue with the left-hand side.

evalStep :: [(Char, (Expr e))] -> Expr e -> ([(Char, (Expr e))], Expr e)
evalStep h (T) = (h, T)
evalStep h (F) = (h, F)
evalStep h (Nil) = (h, Nil)
evalStep h (Constr (x) (y)) = (h, (Constr (x) (y)))
evalStep h (Lambda x e) = (h, (Lambda x e))
evalStep h (Const c) = (h, (Const c))
evalStep h (Var x)
  | (b /= []) = evalStep ((x,n):(h \\ b)) (e)
  | otherwise = (h, (Var x))
  where b = (getBinding h x)
        e = snd (head b)
        v = evalStep (h \\ b) (e)
        n = snd v
evalStep h (Let (Var x) n m) = (((x,n):h), m)
evalStep h (App m (Var x)) = ((delta), (sub (eprime) (Var x) lvar))
  where lresult = evalStep (h) m
        lexpr = (snd lresult)
        delta = (fst lresult)
        eprime = getExpr lexpr
        lvar = getVar lexpr
evalStep h (Prim (m) op (n)) = ((theta), (constApp op (c1) (c2)))
  where n1 = evalStep h m
        delta = (fst n1)
        n2 = evalStep (delta) n
        theta = (fst n2)
        c1 = (snd n1)
        c2 = (snd n2)
evalStep h (If (e) (e1) (e2))
  | (eprime == T) = ((delta), (e1))
  | (eprime == F) = ((delta), (e2))
  where lresult = evalStep h e
        eprime = (snd  lresult)
        delta = (fst lresult)
evalStep h (Case e ((Nil),(e1)) ((Constr (y1) (ys)),(e2)))
  | (isNil eprime) = ((delta), (e1))
  | (isConstr eprime) = ((delta), (sub (sub (e2) (x) (getCVar y1)) (xs) (getCVar ys)))
  where lresult = evalStep h e
        eprime = (snd lresult)
        delta = (fst lresult)
        x = (getCFst eprime)
        xs = (getCSnd eprime)