module Main where

import BetaTests
import Launchbury
import Lambda
import Common
import Parser
import Utils

evalMain :: String -> String -> Expr e
evalMain t l
  | (t == "N") = evalN (ins)
  | (t == "V") = evalV (ins)
  | (t == "L") = evalNeed (ins)
  | (t == "M") = snd (evalLaunch [] nins)
    where ins = lexData l
          nins = lexNorm l

-- TODO: module that'll interact with a web service (CGI-style) in order to show a visual representation of the interpreter
-- featuring evaluation mode selection, showing the reduction graph and intermediate evaluation steps.