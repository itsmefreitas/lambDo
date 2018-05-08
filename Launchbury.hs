module Launchbury where

import Lambda
import Parser
import Data.List
import Utils
import BetaTests

freshVar :: Expr e -> Char
freshVar m = head ((['z','y'..'a'] ++ ['Z','Y'..'A']) \\ (freeVar(m) `union` boundVar(m)))

-- ASK: Can "eager" normalization be done in terms to ensure "freshness" of variables? A: yes.
-- ASK: In the Variable rule, how to proceed if no bindings are found? Simply return the variable with the queue we had as the evaluation result? A: yes.
-- ASK: Is substitution supposed to be implemented inside (let x = ... in ...) constructs? A: find it in the notes teacher gave you.

normalize :: Expr e -> Expr e
normalize (Var x) = Var x
normalize (Const c) = Const c
normalize (Lambda x m) = Lambda x (normalize m)
normalize (Let x n m) = Let x (normalize n) (normalize m)
normalize (App m n)
  | (isVar n) = App (m') (n)
  | otherwise = Let (Var fresh) (n') (App (m') (Var fresh))
  where fresh = freshVar (App (m') (n'))
        n' = (normalize n)
        m' = (normalize m)

getBinding :: [(Char, (Expr e))] -> Char -> [(Char, (Expr e))]
getBinding [] _ = []
getBinding (x:xs) c
  | ((fst x) == c) = [x]
  | otherwise = (getBinding xs c)

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

-- Test cases for single-step evalLaunch version.
-- FIXME: doesn't handle intermediate (App (Var _) (Var _)) very well...

stp1 = evalLaunch [] (normalize pairTestFst)
stp2 = evalLaunch (fst stp1) (snd stp1)
stp3 = evalLaunch (fst stp2) (snd stp2)
stp4 = evalLaunch (fst stp3) (snd stp3)

