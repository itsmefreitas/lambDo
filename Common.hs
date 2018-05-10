module Common where

import Data.List

data Expr e = Var Char | Const Int | Lambda Char (Expr e) | App (Expr e) (Expr e) | Let (Expr e) (Expr e) (Expr e) | Constr ((Expr e),(Expr e)) | Prim (Expr e) Op (Expr e)

data Op = Plus | Minus | Times | Div

-- Helper function to get a fresh var (used in normalization).

freshVar :: [Char] -> Expr e -> Char
freshVar l m = head ((((['z','y'..'a'] ++ ['Z','Y'..'A']) \\ (freeVar(m) `union` boundVar(m))) \\ l))

-- Check which vars are bound in a lambda term.

boundVar :: Expr e -> [Char]
boundVar (Var v) = []
boundVar (Const c) = []
boundVar (Lambda s e) = [s] ++ (boundVar e)
boundVar (Let x n m) = (freeVar x) ++ (boundVar n) ++ (boundVar m)
boundVar (App t1 t2)
    | ((boundVar t1) == (boundVar t2)) = (boundVar t1)
    | otherwise = (boundVar t1) ++ (boundVar t2)
    
-- Check which vars are free in a lambda term.

freeVar :: Expr e -> [Char]
freeVar (Var v) = [v]
freeVar (Const c) = []
freeVar (Lambda s e) = ((freeVar e) \\ [s])
freeVar (Let x m n) = ((freeVar m) ++ (freeVar n)) \\ ((freeVar x) ++ (boundVar m) ++ (boundVar n))
freeVar (App t1 t2)
    | ((freeVar t1) == (freeVar t2)) = (freeVar t1)
    | otherwise = (freeVar t1) ++ (freeVar t2)

-- Implementation for variable substitution.

sub :: Expr e -> Expr e -> Char -> Expr e
sub (Const c) (_) _ = Const c
sub (Var v) (l) s
    | (not (capture (Var v) (l))) =
    if (v == s) then l
    else (Var v)
    | otherwise = error "Cannot perform substitution with variable capture!"
sub (Lambda v e) (l) s
    | (not (capture (Lambda v e) (l))) =
    if (v == s) then (Lambda v e)
    else (Lambda v (sub e l s))
    | otherwise = error "Cannot perform substitution with variable capture!"
sub (Let (Var v) n m) (l) s
    | (not (capture (n) (l)) && not (capture (m) (l))) =
    if (v == s) then (Let (Var v) n m)
    else (Let (Var v) (sub n l s) (sub m l s))
    | otherwise = error "Cannot perform substitution with variable capture!"
sub (App t1 t2) (l) s = (App (sub t1 l s) (sub t2 l s))

-- ASK: Can "eager" normalization be done in terms to ensure "freshness" of variables? A: yes.
-- ASK: In the Variable rule, how to proceed if no bindings are found? Simply return the variable with the queue we had as the evaluation result? A: yes.
-- ASK: Is substitution supposed to be implemented inside (let x = ... in ...) constructs? A: find it in the notes teacher gave you.

-- Function to normalize' lambda terms.

normalize :: Expr e -> Expr e
normalize e = fst (normalize' e [])

normalize' :: Expr e -> [Char] -> (Expr e,[Char])
normalize' (Var x) l = ((Var x),[])
normalize' (Const c) l = ((Const c),[])
normalize' (Lambda x m) l = ((Lambda x (fst (normalize' m l))),l)
normalize' (Let x n m) l = ((Let x (fst (normalize' n l)) (fst (normalize' m l))), l)
normalize' (App m n) l
  | (isVar n) = ((App (fst m') (n)),l++(snd m'))
  | otherwise = ((Let (Var fresh) (fst n') (App (fst m') (Var fresh))),fresh:(l++(snd m')))
  where fresh = freshVar l (App (fst m') (fst n'))
        n' = (normalize' n l)
        m' = (normalize' m (l++(snd n')))

-- Given a variable and stack, find and retrieve the first expression bound to it in suck stack.

getBinding :: [(Char, (Expr e))] -> Char -> [(Char, (Expr e))]
getBinding [] _ = []
getBinding (x:xs) c
  | ((fst x) == c) = [x]
  | otherwise = (getBinding xs c)

-- Function to check if variable capture happens, refer to sub's cases of "unsafe" substitutions...
    
capture :: Expr e -> Expr e -> Bool
capture m n = ((boundVar(m) `intersect` freeVar(n)) /= [])

-- Check whether a term has a variable-bound context, useful in the pattern guards on the (V) axiom.

hasContext :: Expr e -> Expr e -> Bool
hasContext (Var x) (Const c) = False
hasContext (Var x) (Var v) = (x == v)
hasContext (Var x) (Lambda v m) = hasContext (Var x) (m)
hasContext (Var x) (App m n) = (hasContext (Var x) m) || (hasContext (Var x) n)

-- Check if variable occurs in the body of an abstraction...

occurs :: Expr e -> Expr e -> Bool
occurs (Var v) (Var x) = (v == x)
occurs (Var v) (Lambda x e)
  | (v == x) = True
  | otherwise = (occurs (Var v) (e))
occurs (Var v) (App (m) (n)) = occurs (Var v) (m)

-- FillContext: Given a variable and an expression in which the variable is supposed to appear, replace it by the "new" expression z

fillContext :: Expr e -> Expr e -> Expr e -> Expr e
fillContext (Var v) (Var w) (z)
  | (hasContext (Var v) (Var w)) = z
fillContext (Var v) (Lambda w e) (z)
  | (hasContext (Var v) (Lambda w e)) = Lambda w (fillContext (Var v) (e) (z))
fillContext (Var v) (App m n) (z)
  | (hasContext (Var v) (m)) = App (fillContext (Var v) (m) (z)) (n)
  | (hasContext (Var v) (n)) = App m (fillContext (Var v) (n) (z))
    
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
getVar _ = error "Variable not in scope!"

getConst :: Expr e -> Int
getConst (Const c) = c
getConst _ = error "Constant not in scope!"

getExpr :: Expr e -> Expr e
getExpr (Lambda v e) = e
getExpr _ = error "Expression not in scope!"