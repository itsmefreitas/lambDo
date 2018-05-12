{
module Parser where
import Data.Char
import Common
}

%name expr
%tokentype { Token }
%error { parseError }

%token
  let   { TokenLet }
  in    { TokenIn }
  '='   { TokenEq }
  const { TokenConst $$ }
  var   { TokenVar $$ }
  '\\'  { TokenLambda $$ }
  '.'   { TokenDot }
  '('   { TokenOP }
  ')'   { TokenCP }
%%

Expr     : let Expr '=' Expr in Expr  { Let ($2) ($4) ($6) }
        | '\\' '.' Expr               { Lambda $1 $3 }
        | Exp1                        { $1 }

Exp1    : Exp1 Atom                   { App ($1) ($2) }
        | Atom                        { $1 }
        
Atom    : '(' Expr ')'                { $2 }
        | var                         { Var $1 }
        | const                       { Const $1 }

{

parseError :: [Token] -> a
parseError _ = error "Parse error!"

data Token = TokenVar Char | TokenConst Int | TokenLambda Char | TokenDot | TokenOP | TokenCP | TokenLet | TokenEq | TokenIn deriving Show

-- TODO: parser/lexer dark magic to account for the parsing of (expr op expr) constructs as well as if and case statements

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

}