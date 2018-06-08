module Lambda where

import Data.List
import Utils
import Common
-- EvalV: function for evaluation of lambda terms using call-by-value

evalV :: Expr e -> Expr e
evalV (Const c) = Const c
evalV (Var v) = Var v
evalV (Lambda v m) = Lambda v m
evalV (App m n)
  | (isLambda m') = apply (evalV m) $! (evalV n)
  | not (isReducible (App m n)) = (App m n)
    where m' = (evalV m)
          
apply (Lambda x e) v = evalV(sub e v x)
apply m n = (App m n)
          
-- TODO: implement [Expr e] with list of intermediate steps for reduction, with possible depth limit.
          
-- EvalN: function for evaluation of lambda terms using call-by-name

evalN :: Expr e -> Expr e
evalN (Const c) = Const c
evalN (Var v) = Var v
evalN (Lambda v m) = Lambda v m
evalN (App m n)
  | (isLambda m') = evalN ((sub (body) (n) (var)))
  | not (isReducible (App m n)) = (App m n)
    where m' = (evalN m)
          body = (getExpr m')
          var = (getVar m')

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