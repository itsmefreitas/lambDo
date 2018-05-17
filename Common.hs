module Common where

import Data.List

data Expr e = Var Char
              | Const Int
              | T
              | F
              | Nil
              | Lambda Char (Expr e)
              | App (Expr e) (Expr e)
              | Let (Expr e) (Expr e) (Expr e)
              | Constr (Expr e) (Expr e)
              | Prim (Expr e) Op (Expr e)
              | If (Expr e) (Expr e) (Expr e)
              | Case (Expr e) ((Expr e),(Expr e)) ((Expr e),(Expr e))

-- ASK: what boolean/unary operations is this supposed to support?

data Op = Plus | Minus | Times | Div | Eql | Lt | Gt

-- Helper function to get a fresh var (used in normalization).

freshVar :: [Char] -> Expr e -> Char
freshVar l m = head (((['z','y'..'a'] ++ ['Z','Y'..'A']) \\ (freeVar(m) `union` boundVar(m) `union` l)))

-- ASK: Should freeVar and boundVar be implemented for if-statements, constr and prim?

-- Check which vars are bound in a lambda term.

boundVar :: Expr e -> [Char]
boundVar (T) = []
boundVar (F) = []
boundVar (Nil) = []
boundVar (Var v) = []
boundVar (Const c) = []
boundVar (Lambda s e) = [s] ++ (boundVar e)
boundVar (Let x n m) = (freeVar x) ++ (boundVar n) ++ (boundVar m)
boundVar (App t1 t2)
    | ((boundVar t1) == (boundVar t2)) = (boundVar t1)
    | otherwise = (boundVar t1) ++ (boundVar t2)
boundVar (Constr (m) (n)) = (boundVar m) ++ (boundVar n)
boundVar (Prim (x) op (y)) = (boundVar x) ++ (boundVar y)
boundVar (If (x) (m) (n)) = (boundVar x) ++ (boundVar m) ++ (boundVar n)
boundVar (Case (e) ((e1),(c1)) ((e2),(c2))) = (boundVar e) ++ (boundVar e1) ++ (boundVar c1) ++ (boundVar e2) ++ (boundVar c2)
    
-- Check which vars are free in a lambda term.

freeVar :: Expr e -> [Char]
freeVar (T) = []
freeVar (F) = []
freeVar (Nil) = []
freeVar (Var v) = [v]
freeVar (Const c) = []
freeVar (Lambda s e) = ((freeVar e) \\ [s])
freeVar (Let x m n) = ((freeVar m) ++ (freeVar n)) \\ ((freeVar x) ++ (boundVar m) ++ (boundVar n))
freeVar (App t1 t2)
    | ((freeVar t1) == (freeVar t2)) = (freeVar t1)
    | otherwise = (freeVar t1) ++ (freeVar t2)
freeVar (Constr (m) (n)) = (freeVar m) ++ (freeVar n)
freeVar (Prim (x) op (y)) = (freeVar x) ++ (freeVar y)
freeVar (If (x) (m) (n)) = (freeVar x) ++ (freeVar m) ++ (freeVar n)
freeVar (Case (e) ((e1),(c1)) ((e2),(c2))) = (freeVar e) ++ (freeVar e1) ++ (freeVar c1) ++ (freeVar e2) ++ (freeVar c2)

-- Implementation for variable substitution.
-- ASK: Sub for Prim, Const, If?

sub :: Expr e -> Expr e -> Char -> Expr e
sub (T) (_) _ = T
sub (F) (_) _ = F
sub (Nil) (_) _ = Nil
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
sub (Constr (m) (n)) (l) s = Constr (sub m l s) (sub n l s)
--    | ((not (capture m l)) && (not (capture n l))) = Constr (sub m l s) (sub n l s)
--    | otherwise = error "Cannot perform substitution with variable capture!"
sub (Prim (x) op (y)) (l) s = Prim (sub x l s) op (sub y l s)
--    | ((not (capture x l)) && (not (capture y l))) = (Prim (sub x l s) op (sub y l s))
--    | otherwise = error "Cannot perform substitution with variable capture!"
sub (If (x) (m) (n)) (l) s = If (sub x l s) (sub m l s) (sub n l s)
--    | ((not (capture x l)) && (not (capture m l)) && (not (capture n l))) = (If (sub x l s) (sub m l s) (sub n l s))
--    | otherwise = error "Cannot perform substitution with variable capture!"
sub (Case (e) ((e1),(c1)) ((e2),(c2))) (l) s = Case (sub e l s) ((sub e1 l s),(sub c1 l s)) ((sub e2 l s),(sub c2 l s))
--    | ((not (capture e l)) && (not (capture e1 l)) && (not (capture c1 l)) && (not (capture e2 l)) && (not (capture c2 l))) = (Case (sub e l s) ((sub e1 l s),(sub c1 l s)) ((sub e2 l s),(sub c2 l s)))
--    | otherwise = error "Cannot perform substitution with variable capture!"

-- Function to normalize lambda terms.
-- ASK: How should I treat normalization of If, Prim and Cons??

normalize :: Expr e -> Expr e
normalize e = fst (normalize' e (boundVar(e) `union` freeVar(e)))

normalize' :: Expr e -> [Char] -> (Expr e,[Char])
normalize' (T) l = (T,l)
normalize' (F) l = (F,l)
normalize' (Nil) l = (Nil,l)
normalize' (Var x) l = ((Var x),x:l)
normalize' (Const c) l = ((Const c),l)
normalize' (Lambda x m) l = ((Lambda x m'), (x:(l')++l))
  where mn = (normalize' m l)
        m' = fst mn
        l' = snd mn
normalize' (Let x n m) l = ((Let x (n') (m')), (lm))
  where nn = (normalize' n l)
        n' = fst nn
        l' = snd nn
        mn = (normalize' m (l'++l))
        m' = fst mn
        lm = snd mn
normalize' (App m n) l
  | (isVar n) = ((App (m') (n)), (l++(l')))
  | otherwise = ((Let (Var fresh) (n') (App (m') (Var fresh))), (fresh:(l++(ln))))
  where fresh = freshVar l (App (m') (n'))
        nn = (normalize' n l)
        n' = fst nn
        l' = snd nn
        mn = (normalize' m (l++(l')))
        m' = fst mn
        ln = snd mn
normalize' (Constr m n) l = ((Constr (m') (n')), (l++(ln)))
  where mn = (normalize' m l)
        m' = fst mn
        l' = snd mn
        nn = (normalize' n (l++(l')))
        n' = fst nn
        ln = snd nn
normalize' (Prim x op y) l = ((Prim (x') op (y')), (l++(ly)))
  where xn = (normalize' x l)
        x' = fst xn
        l' = snd xn
        yn = (normalize' y (l++(l')))
        y' = fst yn
        ly = snd yn
normalize' (If x m n) l = ((If (x') (m') (n')), (l++(ln)))
  where xn = (normalize' x l)
        x' = fst xn
        l' = snd xn
        mn = (normalize' m (l++(l')))
        m' = fst mn
        lm = snd mn
        nn = (normalize' n (l++(lm)))
        n' = fst nn
        ln = snd nn
normalize' (Case (e) ((e1),(c1)) ((e2),(c2))) l = ((Case (e') ((e1'),(c1')) ((e2'),(c2'))), (l++(lc2)))
  where en = (normalize' e l)
        e' = fst en
        l' = snd en
        e1n = (normalize' e1 (l++(l')))
        e1' = fst e1n
        le1 = snd e1n
        c1n = (normalize' c1 (l++(le1)))
        c1' = fst c1n
        lc1 = snd c1n
        e2n = (normalize' e2 (l++(lc1)))
        e2' = fst e2n
        le2 = snd e2n
        c2n = (normalize' c2 (l++(le2)))
        c2' = fst c2n
        lc2 = snd c2n

-- Given a variable and stack, find and retrieve the first expression bound to it in such stack.

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

isNil :: Expr e -> Bool
isNil (Nil) = True
isNil _ = False

isConstr :: Expr e -> Bool
isConstr (Constr (x) (xs)) = True
isConstr _ = False

getVar :: Expr e -> Char
getVar (Lambda v e) = v
getVar _ = error "Variable not in scope!"

getCVar :: Expr e -> Char
getCVar (Var v) = v
getCVar _ = error "Variable not in scope!"

getConst :: Expr e -> Int
getConst (Const c) = c
getConst _ = error "Constant not in scope!"

getExpr :: Expr e -> Expr e
getExpr (Lambda v e) = e
getExpr _ = error "Expression not in scope!"

getCFst :: Expr e -> Expr e
getCFst (Constr (x) (xs)) = x
getCFst _ = error "This expression isn't a constructor!"

getCSnd :: Expr e -> Expr e
getCSnd (Constr (x) (xs)) = xs
getCSnd _ = error "This expression isn't a constructor!"