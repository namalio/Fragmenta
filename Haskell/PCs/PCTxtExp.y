{
module PCs.ParsingTxtExp where
import Data.Char 
     (isAlpha
     , isSpace
     , isDigit
     )
import PCs.TxtExpAST
import PCs.Common(Id)
}

%name toAST
%tokentype { Token }
%error { parseError }

%token
      true            { TokenT }
      false           { TokenF }
      int             { TokenInt $$ }
      id              { TokenId $$ }
      '('             { TokenOP }
      ')'             { TokenCP }
      '.'             { TokenDot }
      '<'             { TokenLT }
      '>'             { TokenGT }
      '≥'             { TokenGEQ }
      '≤'             { TokenLEQ }
      '='             { TokenEQ }
      '≠'             { TokenNEQ }
      '+'             { TokenPlus }
      '-'             { TokenMinus }
      '*'             { TokenTimes }
      '/'             { TokenDiv }
      '%'             { TokenRemainder }
      '⋀'             { TokenAnd }
      '⋁'             { TokenOr }
      '¬'             { TokenNot }
      '{'             { TokenOB }
      '}'             { TokenCB }
      ','             { TokenComma }
      '∪'             { TokenCup }
      '∩'             { TokenCap }
      '∊'             { TokenIn }

%left '⋀' '⋁'
%left '¬'
%nonassoc '>' '<' '≤' '≥' '=' '≠' '∊'
%left '+' '-' '∪'
%left '*' '/' '%' '∩'
%right '.'
%left NEG

%%
Exp   : Exp '⋀' Exp            { ExpBin And $1 $3 }
      | Exp '⋁' Exp            { ExpBin Or $1 $3 }
      | Exp '=' Exp            { ExpRel OEQ $1 $3 }
      | Exp '≠' Exp            { ExpRel ONEQ $1 $3 }
      | Exp '<' Exp            { ExpRel OLT $1 $3 }
      | Exp '>' Exp            { ExpRel OGT $1 $3 } 
      | Exp '≥' Exp            { ExpRel OGEQ $1 $3 } 
      | Exp '≤' Exp            { ExpRel OLEQ $1 $3 } 
      | Exp '∊' Exp            { ExpRel OIN $1 $3 } 
      | '¬' Exp                { ExpUn UNot $2 }
      | Exp '+' Exp            { ExpBin Plus $1 $3 }
      | Exp '-' Exp            { ExpBin Minus $1 $3 }
      | Exp '.' Exp            { ExpDot $1 $3}     
      | '-' Exp   %prec NEG    { ExpUn UMinus $2 }
      | Exp '*' Exp            { ExpBin Prod $1 $3 }
      | Exp '/' Exp            { ExpBin Div $1 $3 }
      | Exp '%' Exp            { ExpBin Remainder $1 $3 }
      | true                   { ExpB TrueT }
      | false                  { ExpB FalseT }
      | id                     { ExpId $1 }
      | int                    { ExpInt $1 }
      | '(' Exp ')'            { ExpPar $2 }
      | '{' Exps '}'           { ExpSet $2 }
      | Exp '∪' Exp            { ExpBin Cup $1 $3 }
      | Exp '∩' Exp            { ExpBin Cap $1 $3 }

Exps  :: {[ Exp ] }
Exps  : Exp ',' Exps           { $1:$3 }
      | Exp                    { [$1] }
      | {- empty -}            { [] } 

{
parseError :: [Token] -> a
parseError tokens = error $ "Parse error with tokens:" ++ show tokens

data Token
      = TokenT
      | TokenF
      | TokenInt Int
      | TokenId Id
      | TokenOP 
      | TokenCP 
      | TokenDot
      | TokenLT
      | TokenGT
      | TokenLEQ
      | TokenGEQ
      | TokenEQ
      | TokenNEQ
      | TokenPlus
      | TokenMinus
      | TokenTimes
      | TokenDiv
      | TokenRemainder
      | TokenAnd
      | TokenOr
      | TokenNot
      | TokenOB
      | TokenCB
      | TokenComma
      | TokenCup
      | TokenCap
      | TokenIn
     deriving Show

--instance Show Token where
--    show::Token->String
--    show TokenT = "True"
--    show TokenF = "False"
--    show (TokenInt n)  = show n
--    show (TokenId id) = id
--    show TokenOP = "("
--    show TokenCP  = ")"
--    show TokenDot = "."
--    show TokenLT = "<"
--    show TokenGT = ">"
--    show TokenLEQ = "≤"
--    show TokenGEQ = "≥"
--    show TokenEQ = "="
--    show TokenNEQ = "≠"
--    show TokenPlus = "+"
--    show TokenMinus = "-"
--    show TokenTimes = "*"
--    show TokenDiv = "/"
--    show TokenRemainder = "%"
--    show TokenAnd = "⋀"
--    show TokenOr = "⋁"
--    show TokenNot = "¬"
--    show TokenOB = "{"
--    show TokenCB = "}"
--    show TokenComma = ","

tokenChars::[Char]
tokenChars = ['(', ')', '.', '<', '>', '≤', '≥', '=', '≠', '+', '-', '*', '/',
      '%', '⋀', '⋁', '¬', '{', '}', ',', '∪', '∩', '∊']

isToken::Char->Bool
isToken c = c `elem` tokenChars

toToken::Char->Token
toToken '(' = TokenOP
toToken ')' = TokenCP
toToken '.' = TokenDot
toToken '<' = TokenLT
toToken '>' = TokenGT
toToken '≤' = TokenLEQ
toToken '≥' = TokenGEQ
toToken '=' = TokenEQ 
toToken '≠' = TokenNEQ
toToken '+' = TokenPlus
toToken '-' = TokenMinus
toToken '*' = TokenTimes
toToken '/' = TokenDiv
toToken '%' = TokenRemainder
toToken '⋀' = TokenAnd
toToken '⋁' = TokenOr
toToken '¬' = TokenNot
toToken '{' = TokenOB
toToken '}' = TokenCB
toToken ',' = TokenComma
toToken '∪' = TokenCup
toToken '∩' = TokenCap
toToken '∊' = TokenIn

lexer :: String -> [Token]
lexer [] = []
lexer (c:cs)
      | isSpace c = lexer cs
      | isAlpha c = lexId (c:cs)
      | isDigit c = lexNum (c:cs)
      | isToken c = lexToken(c:cs) 
      | otherwise = error $ "Urecognised char '" ++ [c] ++ "'"
--      | otherwise = failE $ "Urecognised char '" ++ [c] ++ "'"
--lexer ('(':cs) = returnE $ TokenOP : lexer cs
--lexer (')':cs) = returnE $ TokenCP : lexer cs
--lexer ('.':cs) = returnE $ TokenDot : lexer cs
--lexer ('<':cs) = returnE $ TokenLT : lexer cs
--lexer ('>':cs) = returnE $ TokenGT : lexer cs
--lexer ('≤':cs) = returnE $ TokenLEQ : lexer cs
--lexer ('≥':cs) = returnE $ TokenGEQ : lexer cs
--lexer ('=':cs) = returnE $ TokenEQ : lexer cs
--lexer ('≠':cs) = returnE $ TokenNEQ : lexer cs
--lexer ('+':cs) = returnE $ TokenPlus : lexer cs
--lexer ('-':cs) = returnE $ TokenMinus : lexer cs
--lexer ('*':cs) = returnE $ TokenTimes : lexer cs
--lexer ('/':cs) = returnE $ TokenDiv : lexer cs
--lexer ('%':cs) = returnE $ TokenRemainder : lexer cs
--lexer ('⋀':cs) = returnE $ TokenAnd : lexer cs
--lexer ('⋁':cs) = returnE $ TokenOr : lexer cs 
--lexer ('¬':cs) = returnE $ TokenNot : lexer cs
--lexer ('{':cs) = returnE $ TokenOB : lexer cs
--lexer ('}':cs) = returnE $ TokenCB : lexer cs
--lexer (',':cs) = returnE $ TokenComma : lexer cs
--lexer ('∪':cs) = returnE $ TokenCup : lexer cs
--lexer ('∩':cs) = returnE $ TokenCap : lexer cs
--lexer ('∊':cs) = returnE $ TokenIn : lexer cs
lexToken::String->[Token]
lexToken (c:cs) = (toToken c):lexer cs
--   let t = toToken c
--   ts<-lexer cs
--   returnE (t:ts)

lexNum::String ->[Token]
lexNum cs = TokenInt (read num):lexer rest
   where (num,rest) = span isDigit cs

lexId::String ->[Token]
lexId cs = do
   case span (\c->isAlpha c || isDigit c) cs of
      ("True",rest)  -> TokenT : lexer rest
      ("False",rest) -> TokenF : lexer rest
      (id,rest)      -> TokenId id  : lexer rest
--   let t =  gToken s  
--   ts<-lexer rest
--   returnE (t:ts)
--   where 
--      (s, rest) = span isAlpha cs
--      gToken  = TokenT 
--      gToken  = TokenF 
--      gToken id = TokenId id 


parse::String->Exp
parse = toAST . lexer 

main :: IO ()
main = getContents >>= print . show_parsed . parse

--show_results::E Exp->String
--show_results (Left e) = show_parsed e
--show_results (Right err) = err

show_test_exp::String->IO()
show_test_exp e = do
   putStrLn . show . parse $ e
   putStrLn . show_parsed . parse $ e

test1::IO()
test1 = show_test_exp "123"

test2::IO()
test2 = show_test_exp "2 + 5*2"

test3::IO()
test3 = show_test_exp "¬t<5"

test4::IO()
test4 = show_test_exp "(n≥0) ⋀ (n≤m)"

test5::IO()
test5 = show_test_exp "n≥0 ⋀ n≤m"

test6::IO()
test6 = show_test_exp "a≠b ⋁ c=d"

test7a::IO()
test7a = show_test_exp "¬A ⋀ B"

test7b::IO()
test7b = show_test_exp "¬(A ⋀ B)"

test7c::IO()
test7c = show_test_exp "3>2 ⋀ 2<3"

test7d::IO()
test7d = show_test_exp "¬3>2 ⋀ 2<3"

test8::IO()
test8 = show_test_exp "5+6 > 5+5"

test9::IO()
test9 = show_test_exp "-5*2"

test10a::IO()
test10a = show_test_exp "take.a.b"

test10b::IO()
test10b = show_test_exp "-2.-3"

test11a::IO()
test11a = show_test_exp "{}"

test11b::IO()
test11b = show_test_exp "{1,2,3}"

test12a::IO()
test12a = show_test_exp "{a} ∪ {b}"

test12b::IO()
test12b = show_test_exp "{a, b} ∩ {b, c}"

test12c::IO()
test12c = show_test_exp "{a+1, b-2} ∩ {b*4, c/4}"

test13a::IO()
test13a = show_test_exp "1 ∊ {1, 2, 3}"

test13b::IO()
test13b = show_test_exp "¬10 ∊ {5, 6, 7, 8}"
}