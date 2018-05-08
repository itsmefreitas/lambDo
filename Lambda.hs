module Lambda where

import Data.List
import Parser
import BetaTests
import Utils

boundVar :: Expr e -> [Char]
boundVar (Var v) = []
boundVar (Const c) = []
boundVar (Lambda s e) = [s] ++ (boundVar e)
boundVar (Let x n m) = (freeVar x) ++ (boundVar n) ++ (boundVar m)
boundVar (App t1 t2)
  | ((boundVar t1) == (boundVar t2)) = (boundVar t1)
  | otherwise = (boundVar t1) ++ (boundVar t2)

freeVar :: Expr e -> [Char]
freeVar (Var v) = [v]
freeVar (Const c) = []
freeVar (Lambda s e) = ((freeVar e) \\ [s])
freeVar (Let x m n) = ((freeVar m) ++ (freeVar n)) \\ ((freeVar x) ++ (boundVar m) ++ (boundVar n))
freeVar (App t1 t2)
  | ((freeVar t1) == (freeVar t2)) = (freeVar t1)
  | otherwise = (freeVar t1) ++ (freeVar t2)

-- Implementation for variable substituting

sub :: Expr e -> Expr e -> Char -> Expr e
sub (Const c) (_) _ = Const c
sub (Var v) (l) s
  | (not (capture (Var v) (l))) =
    if (v == s) then l
    else (Var v)
  | otherwise = (Var v)
sub (Lambda v e) (l) s
  | (not (capture (Lambda v e) (l))) =
    if (v == s) then (Lambda v e)
    else (Lambda v (sub e l s))
  | otherwise = (Lambda v e)
sub (Let (Var v) n m) (l) s
  | (not (capture (n) (l)) && not (capture (m) (l))) =
    if (v == s) then (Let (Var v) n m)
    else (Let (Var v) (sub n l s) (sub m l s))
  | otherwise = (Let (Var v) n m)
sub (App t1 t2) (l) s = (App (sub t1 l s) (sub t2 l s))

-- Function to check if variable capture happens, refer to sub's cases of "unsafe" substitutions...

capture :: Expr e -> Expr e -> Bool
capture m n = ((boundVar(m) `intersect` freeVar(n)) /= [])

-- EvalV: function for evaluation of lambda terms using call-by-value

evalV :: Expr e -> Expr e
evalV (Const c) = Const c
evalV (Var v) = Var v
evalV (Lambda v e) = Lambda v e
evalV (App t1 t2)
  | (isLambda t') = apply (evalV t1) $! (evalV t2)
  | ((isConst t') && (isConst n')) = (App (t') (n'))
  | not (isReducible (App t' n')) = (App t' n')
    where n' = (evalV t2)
          t' = (evalV t1)
          
apply (Lambda x e) v = evalV(sub e v x)
apply m n = (App m n)
          
-- TODO: implement [Expr e] with list of intermediate steps for reduction, with possible depth limit.
          
-- EvalN: function for evaluation of lambda terms using call-by-name

evalN :: Expr e -> Expr e
evalN (Const c) = Const c
evalN (Var v) = Var v
evalN (Lambda v e) = Lambda v e
evalN (App t1 t2)
  | (isLambda t') = evalN ((sub (m') (t2) (v')))
  | not (isReducible (App t' t2)) = (App t' t2)
    where t' = (evalN t1)
          m' = (getExpr t')
          v' = (getVar t')

-- Helper function to handle cases such as (App (Var 'x') (Lambda 'y' (Var 'y'))) which are not reducible through lambda calculus.

isReducible :: Expr e -> Bool
isReducible (Var _) = False
isReducible (Const _) = False
isReducible (Lambda _ (_)) = True
isReducible (App (Lambda _ (_)) (_)) = True
isReducible (App (Var _) (n)) = False
isReducible (App (Const _) (n)) = False
isReducible (App m _) = (isReducible m)

isVar :: Expr e -> Bool
isVar (Var _) = True
isVar _ = False

isLambda :: Expr e -> Bool
isLambda (Lambda _ _) = True
isLambda _ = False

isConst :: Expr e -> Bool
isConst (Const e) = True
isConst _ = False

getVar :: Expr e -> Char
getVar (Lambda v e) = v
getVar _ = error "Var not in scope!"

getConst :: Expr e -> Int
getConst (Const c) = c
getConst _ = error "Constant not in scope!"

getExpr :: Expr e -> Expr e
getExpr (Lambda v e) = e
getExpr _ = error "Var not in scope!"

-- Check whether a term has a variable-bound context, useful in the pattern guards on the (V) axiom.

hasContext :: Expr e -> Expr e -> Bool
hasContext (Var x) (Const c) = False
hasContext (Var x) (Var v) = (x == v)
hasContext (Var x) (Lambda v m) = hasContext (Var x) (m)
hasContext (Var x) (App m n) = (hasContext (Var x) m) || (hasContext (Var x) n)

-- FillContext: Given a variable and an expression in which the variable is supposed to appear, replace it by the "new" expression z

fillContext :: Expr e -> Expr e -> Expr e -> Expr e
fillContext (Var v) (Var w) (z)
  | (hasContext (Var v) (Var w)) = z
fillContext (Var v) (Lambda w e) (z)
  | (hasContext (Var v) (Lambda w e)) = Lambda w (fillContext (Var v) (e) (z))
fillContext (Var v) (App m n) (z)
  | (hasContext (Var v) (m)) = App (fillContext (Var v) (m) (z)) (n)
  | (hasContext (Var v) (n)) = App m (fillContext (Var v) (n) (z))

-- ASK: What should I do with non-terminating terms when implementing rule (G)? Merge it with (V) like I did? A: YES
-- ASK: is the pattern (App (m) (n)) well matched? A: YES.

evalNeed :: Expr e -> Expr e
evalNeed (Const c) = Const c
evalNeed (Var v) = Var v
evalNeed (Lambda x m) = Lambda x m
evalNeed (App (Lambda x m) (n)) = evalNeed(Let (Var x) (n) (m))
evalNeed (Let (Var x) (v) (cx))
  | (not (x `elem` freeVar(cx))) = evalNeed (cx)
  | ((hasContext (Var x) (cx))) = evalNeed (Let (Var x) (v) (fillContext (Var x) (cx) (v)))
evalNeed (App (Let (Var x) (l) (m)) (n)) = evalNeed (Let (Var x) (l) (App (m) (n)))
evalNeed (App (m) (n))
  | (isReducible (m)) = evalNeed (App (evalNeed m) (evalNeed n))
  | otherwise = (App (m) (n))
evalNeed (Let (Var y) (Let (Var x) (l) (m)) (n)) = evalNeed (Let (Var x) (l) (Let (Var y) (m) (n)))

occurs :: Expr e -> Expr e -> Bool
occurs (Var v) (Var x) = (v == x)
occurs (Var v) (Lambda x e)
  | (v == x) = True
  | otherwise = (occurs (Var v) (e))
occurs (Var v) (App (m) (n)) = occurs (Var v) (m)

evalMain :: String -> String -> Expr e
evalMain t l
  | (t == "N") = evalN (ins)
  | (t == "V") = evalV (ins)
  | (t == "L") = evalNeed (ins)
    where ins = toData (lexer l)
