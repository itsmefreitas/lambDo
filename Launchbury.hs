module Launchbury where

import Parser
import Data.List
import Utils
import Common

constApp :: Op -> Int -> Int -> Expr e
constApp Plus c1 c2 = (Const (c1+c2))
constApp Minus c1 c2 = (Const (c1-c2))
constApp Times c1 c2 = (Const (c1*c2))
constApp Div c1 c2 = (Const (quot c1 c2))

-- FIXME: test-case for evalLaunch [] (normalize (toData (lexer "(\\x.y) (\\x.xx) (\\x.xx)"))) -> figure out what I am passing to getExpr and what I should return from it.

evalLaunch :: [(Char, (Expr e))] -> Expr e -> ([(Char, (Expr e))], Expr e)
evalLaunch h (Constr (x,y)) = (h, (Constr(x,y)))
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
        lexpr = snd (lresult)
        delta = (fst lresult)
        eprime = getExpr lexpr
        lvar = getVar lexpr
evalLaunch h (Prim (m) op (n))
  | ((isConst c1) && (isConst c2)) = ((theta), (constApp op (getConst c1) (getConst c2)))
  where n1 = evalLaunch h m
        delta = (fst n1)
        n2 = evalLaunch (delta) n
        theta = (fst n2)
        c1 = (snd n1)
        c2 = (snd n2)

