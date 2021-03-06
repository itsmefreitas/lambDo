{-# OPTIONS_GHC -w #-}
module Parser where
import Data.Char
import Common
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.19.5

data HappyAbsSyn t4 t5 t6
	= HappyTerminal (Token)
	| HappyErrorToken Int
	| HappyAbsSyn4 t4
	| HappyAbsSyn5 t5
	| HappyAbsSyn6 t6

action_0 (7) = happyShift action_2
action_0 (10) = happyShift action_6
action_0 (11) = happyShift action_7
action_0 (12) = happyShift action_8
action_0 (14) = happyShift action_9
action_0 (4) = happyGoto action_3
action_0 (5) = happyGoto action_4
action_0 (6) = happyGoto action_5
action_0 _ = happyFail

action_1 (7) = happyShift action_2
action_1 _ = happyFail

action_2 (7) = happyShift action_2
action_2 (10) = happyShift action_6
action_2 (11) = happyShift action_7
action_2 (12) = happyShift action_8
action_2 (14) = happyShift action_9
action_2 (4) = happyGoto action_13
action_2 (5) = happyGoto action_4
action_2 (6) = happyGoto action_5
action_2 _ = happyFail

action_3 (16) = happyAccept
action_3 _ = happyFail

action_4 (10) = happyShift action_6
action_4 (11) = happyShift action_7
action_4 (14) = happyShift action_9
action_4 (6) = happyGoto action_12
action_4 _ = happyReduce_3

action_5 _ = happyReduce_5

action_6 _ = happyReduce_8

action_7 _ = happyReduce_7

action_8 (13) = happyShift action_11
action_8 _ = happyFail

action_9 (7) = happyShift action_2
action_9 (10) = happyShift action_6
action_9 (11) = happyShift action_7
action_9 (12) = happyShift action_8
action_9 (14) = happyShift action_9
action_9 (4) = happyGoto action_10
action_9 (5) = happyGoto action_4
action_9 (6) = happyGoto action_5
action_9 _ = happyFail

action_10 (15) = happyShift action_16
action_10 _ = happyFail

action_11 (7) = happyShift action_2
action_11 (10) = happyShift action_6
action_11 (11) = happyShift action_7
action_11 (12) = happyShift action_8
action_11 (14) = happyShift action_9
action_11 (4) = happyGoto action_15
action_11 (5) = happyGoto action_4
action_11 (6) = happyGoto action_5
action_11 _ = happyFail

action_12 _ = happyReduce_4

action_13 (9) = happyShift action_14
action_13 _ = happyFail

action_14 (7) = happyShift action_2
action_14 (10) = happyShift action_6
action_14 (11) = happyShift action_7
action_14 (12) = happyShift action_8
action_14 (14) = happyShift action_9
action_14 (4) = happyGoto action_17
action_14 (5) = happyGoto action_4
action_14 (6) = happyGoto action_5
action_14 _ = happyFail

action_15 _ = happyReduce_2

action_16 _ = happyReduce_6

action_17 (8) = happyShift action_18
action_17 _ = happyFail

action_18 (7) = happyShift action_2
action_18 (10) = happyShift action_6
action_18 (11) = happyShift action_7
action_18 (12) = happyShift action_8
action_18 (14) = happyShift action_9
action_18 (4) = happyGoto action_19
action_18 (5) = happyGoto action_4
action_18 (6) = happyGoto action_5
action_18 _ = happyFail

action_19 _ = happyReduce_1

happyReduce_1 = happyReduce 6 4 happyReduction_1
happyReduction_1 ((HappyAbsSyn4  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn4  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn4  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn4
		 (Let (happy_var_2) (happy_var_4) (happy_var_6)
	) `HappyStk` happyRest

happyReduce_2 = happySpecReduce_3  4 happyReduction_2
happyReduction_2 (HappyAbsSyn4  happy_var_3)
	_
	(HappyTerminal (TokenLambda happy_var_1))
	 =  HappyAbsSyn4
		 (Lambda happy_var_1 happy_var_3
	)
happyReduction_2 _ _ _  = notHappyAtAll 

happyReduce_3 = happySpecReduce_1  4 happyReduction_3
happyReduction_3 (HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn4
		 (happy_var_1
	)
happyReduction_3 _  = notHappyAtAll 

happyReduce_4 = happySpecReduce_2  5 happyReduction_4
happyReduction_4 (HappyAbsSyn6  happy_var_2)
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn5
		 (App (happy_var_1) (happy_var_2)
	)
happyReduction_4 _ _  = notHappyAtAll 

happyReduce_5 = happySpecReduce_1  5 happyReduction_5
happyReduction_5 (HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn5
		 (happy_var_1
	)
happyReduction_5 _  = notHappyAtAll 

happyReduce_6 = happySpecReduce_3  6 happyReduction_6
happyReduction_6 _
	(HappyAbsSyn4  happy_var_2)
	_
	 =  HappyAbsSyn6
		 (happy_var_2
	)
happyReduction_6 _ _ _  = notHappyAtAll 

happyReduce_7 = happySpecReduce_1  6 happyReduction_7
happyReduction_7 (HappyTerminal (TokenVar happy_var_1))
	 =  HappyAbsSyn6
		 (Var happy_var_1
	)
happyReduction_7 _  = notHappyAtAll 

happyReduce_8 = happySpecReduce_1  6 happyReduction_8
happyReduction_8 (HappyTerminal (TokenConst happy_var_1))
	 =  HappyAbsSyn6
		 (Const happy_var_1
	)
happyReduction_8 _  = notHappyAtAll 

happyNewToken action sts stk [] =
	action 16 16 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	TokenLet -> cont 7;
	TokenIn -> cont 8;
	TokenEq -> cont 9;
	TokenConst happy_dollar_dollar -> cont 10;
	TokenVar happy_dollar_dollar -> cont 11;
	TokenLambda happy_dollar_dollar -> cont 12;
	TokenDot -> cont 13;
	TokenOP -> cont 14;
	TokenCP -> cont 15;
	_ -> happyError' (tk:tks)
	}

happyError_ 16 tk tks = happyError' tks
happyError_ _ tk tks = happyError' (tk:tks)

newtype HappyIdentity a = HappyIdentity a
happyIdentity = HappyIdentity
happyRunIdentity (HappyIdentity a) = a

instance Functor HappyIdentity where
    fmap f (HappyIdentity a) = HappyIdentity (f a)

instance Applicative HappyIdentity where
    pure  = return
    (<*>) = ap
instance Monad HappyIdentity where
    return = HappyIdentity
    (HappyIdentity p) >>= q = q p

happyThen :: () => HappyIdentity a -> (a -> HappyIdentity b) -> HappyIdentity b
happyThen = (>>=)
happyReturn :: () => a -> HappyIdentity a
happyReturn = (return)
happyThen1 m k tks = (>>=) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> HappyIdentity a
happyReturn1 = \a tks -> (return) a
happyError' :: () => [(Token)] -> HappyIdentity a
happyError' = HappyIdentity . parseError

expr tks = happyRunIdentity happySomeParser where
  happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn4 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


parseError :: [Token] -> a
parseError _ = error "Parse error!"

data Token = TokenVar Char | TokenConst Int | TokenLambda Char | TokenDot | TokenOP | TokenCP | TokenLet | TokenEq | TokenIn deriving Show

-- TODO: FIX lexer function processing "x" as [TokenLambda 'x', TokenDot]
-- ASK: Should I pass the current [Token] to see if its head is or isn't a TokenLambda and then decide where to direct my parser?

-- TODO: Implement parsing of Const Int
-- ASK: Const Int not properly parsed with digitToInt, is there anything for the correct purpose in the Prelude?

lexer :: [Char] -> [Token]
lexer [] = []
lexer (x:xs)
  | (isSpace x) = (lexer xs)
  | (x == '\\') = (lexerHead (x:xs))
  | (x == '(') = TokenOP : (lexer xs)
  | (x == ')') = TokenCP : (lexer xs)
  | (isLet (x:xs)) = TokenLet : (lexerLet (drop 3 (x:xs)))
  | (isAlpha x) = (lexerVar (x:xs))
  | (isDigit x) = (lexerConst (x:xs))
  | otherwise = (lexer [])

lexerLet :: [Char] -> [Token]
lexerLet [] = (lexer [])
lexerLet (x:xs)
  | (isSpace x) = (lexerLet xs)
  | (isAlpha x) = TokenVar x : TokenEq : (lexer eqxs) ++ (TokenIn : (lexer inxs))
  | otherwise = (lexerLet [])
    where eqxs = trim (length inxs) (tail (dropWhile (/= '=') (xs)))
          inxs = (getLastIn (words xs))

trim :: Int -> [Char] -> [Char]
trim n l = reverse (drop (n+4) (reverse l))

getLastIn :: [[Char]] -> [Char]
getLastIn [] = []
getLastIn (x:xs)
  | (x == "in" && not ("in" `elem` (xs))) = unwords (xs)
  | otherwise = getLastIn (xs)

lexerHead :: [Char] -> [Token]
lexerHead [] = (lexer [])
lexerHead (x:xs)
  | (isSpace x || x == '\\') = (lexerHead xs)
  | (isAlpha x) = TokenLambda x : TokenDot : (lexerHead xs)
  | (x == '.') = (lexerBody xs)
  | otherwise = (lexer (x:xs))
  
lexerBody :: [Char] -> [Token]
lexerBody [] = (lexer [])
lexerBody (x:xs)
  | (isSpace x) = (lexerBody xs)
  | (isAlpha x) = TokenOP : TokenVar x : TokenCP : (lexerBody xs)
  | otherwise = (lexer (x:xs))

lexerVar :: [Char] -> [Token]
lexerVar [] = (lexer [])
lexerVar (x:xs)
  | (isSpace x) = (lexerVar xs)
  | (isAlpha x) = TokenOP : TokenVar x : TokenCP : (lexerVar xs)
  | otherwise = (lexer (x:xs))
  
lexerConst :: [Char] -> [Token]
lexerConst [] = (lexer [])
lexerConst (x:xs)
  | (isSpace x) = (lexerConst xs)
  | (isDigit x) = TokenOP : TokenConst cns : TokenCP : (lexerConst rst)
  | otherwise = (lexer (x:xs))
    where cns = toInt (x:xs)
          rst = dropInt (x:xs)
    
isLet :: [Char] -> Bool
isLet l = (takeWhile (`elem` "let") l) /= []
    
isIn :: [Char] -> Bool
isIn l = (takeWhile (`elem` "in") l) /= []
    
toInt :: [Char] -> Int
toInt l = read (takeWhile (isDigit) l) :: Int

dropInt :: [Char] -> [Char]
dropInt l = (dropWhile (isDigit) l)

toData :: [Token] -> (Expr e)
toData t = expr t
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "<built-in>" #-}
{-# LINE 1 "<command-line>" #-}
{-# LINE 8 "<command-line>" #-}
# 1 "/usr/include/stdc-predef.h" 1 3 4

# 17 "/usr/include/stdc-predef.h" 3 4










































{-# LINE 8 "<command-line>" #-}
{-# LINE 1 "/usr/lib/ghc/include/ghcversion.h" #-}

















{-# LINE 8 "<command-line>" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp 

{-# LINE 13 "templates/GenericTemplate.hs" #-}

{-# LINE 46 "templates/GenericTemplate.hs" #-}








{-# LINE 67 "templates/GenericTemplate.hs" #-}

{-# LINE 77 "templates/GenericTemplate.hs" #-}

{-# LINE 86 "templates/GenericTemplate.hs" #-}

infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is (1), it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept (1) tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
         (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action

{-# LINE 155 "templates/GenericTemplate.hs" #-}

-----------------------------------------------------------------------------
-- HappyState data type (not arrays)



newtype HappyState b c = HappyState
        (Int ->                    -- token number
         Int ->                    -- token number (yes, again)
         b ->                           -- token semantic value
         HappyState b c ->              -- current state
         [HappyState b c] ->            -- state stack
         c)



-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state (1) tk st sts stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--     trace "shifting the error token" $
     new_state i i tk (HappyState (new_state)) ((st):(sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state ((st):(sts)) ((HappyTerminal (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_0 nt fn j tk st@((HappyState (action))) sts stk
     = action nt j tk st ((st):(sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@(((st@(HappyState (action))):(_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_2 nt fn j tk _ ((_):(sts@(((st@(HappyState (action))):(_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_3 nt fn j tk _ ((_):(((_):(sts@(((st@(HappyState (action))):(_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k - ((1) :: Int)) sts of
         sts1@(((st1@(HappyState (action))):(_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (action nt j tk st1 sts1 r)

happyMonadReduce k nt fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> action nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
         let drop_stk = happyDropStk k stk





             new_state = action

          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop (0) l = l
happyDrop n ((_):(t)) = happyDrop (n - ((1) :: Int)) t

happyDropStk (0) l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n - ((1)::Int)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction

{-# LINE 256 "templates/GenericTemplate.hs" #-}
happyGoto action j tk st = action j j tk (HappyState action)


-----------------------------------------------------------------------------
-- Error recovery ((1) is the error token)

-- parse error if we are in recovery and we fail again
happyFail (1) tk old_st _ stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--      trace "failing" $ 
        happyError_ i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  (1) tk old_st (((HappyState (action))):(sts)) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        action (1) (1) tk (HappyState (action)) sts ((saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail  i tk (HappyState (action)) sts stk =
--      trace "entering error recovery" $
        action (1) (1) tk (HappyState (action)) sts ( (HappyErrorToken (i)) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions







-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.

{-# LINE 322 "templates/GenericTemplate.hs" #-}
{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
