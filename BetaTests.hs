module BetaTests where

import Launchbury
import Lambda
import Common
import Parser

-- Lambda terms definitions for testing

ident = Lambda 'x' (Var 'x')

t1 = Lambda 'x' (Lambda 'k' (Var 't'))
c1 = Lambda 'x' (Const 0)
c2 = Const 1

v1 = Var 'z'

a1 = App (Lambda 'x' (Var 'x')) (Lambda 'z' (App (Lambda 'y' (Var 'y')) (Var 'x')))

s1 = (Var 'x')
s2 = Lambda 'z' (App (Var 'z') (Var 'y'))
s3 = 'k'

s3' = 'x'

-- This test, when applied to sub function leads to variable capture!

s4 = Lambda 'y' (Var 'x')
s5 = Var 'y'
s6 = 'x'

-- Implementation of ordered pairs and binary operations

pairTestFst = (App (fst') (App (App (pair) (Const 3)) (Const 5)))
pairTestSnd = (App (snd') (App (App (pair) (Const 3)) (Const 5)))

true = Lambda 'x' (Lambda 'y' (Var 'x'))

false = Lambda 'x' (Lambda 'y' (Var 'y'))

fst' = Lambda 'p' (App (Var 'p') (true))

snd' = Lambda 'p' (App (Var 'p') (false))

pair = Lambda 'x' (Lambda 'y' (Lambda 'f' (App (App (Var 'f') (Var 'x')) (Var 'y'))))

-- Tests for termination: evalV vs. evalN

trmnt = (App (ycon) (omega))

omega = (App (xxop) (xxop))

xxop = Lambda 'x' (App (Var 'x') (Var 'x'))

ycon = Lambda 'x' (Var 'y')

-- Test cases for lexer

idnt = lexer "(\\x.x)"

omm = lexer "(\\x.xx) (\\x.xx)"

applvarlc = lexer "(\\z.z) x (\\y.yy) 124"

xxapp = lexer "(\\x.xx) y"

vapp = lexer "x (\\y.y)"

vapp1 = lexer "x y"

vapp2 = lexer "(x) (y)"

vapp3 = lexer "xy"

-- Test cases for single-step evalLaunch version.
-- FIXME: doesn't handle intermediate (App (Var _) (Var _)) very well...

stp1 = evalLaunch [] (normalize pairTestFst)
stp2 = evalLaunch (fst stp1) (snd stp1)
stp3 = evalLaunch (fst stp2) (snd stp2)
stp4 = evalLaunch (fst stp3) (snd stp3)