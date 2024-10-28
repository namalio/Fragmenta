module PCs.ParsingPCTxtExp 
    (parsePCExp
    , parsePCExpAtom)
where

import Text.ParserCombinators.ReadP
import PCs.PCTrees_Exp
import ParsingCommon
import Control.Applicative ( Alternative((<|>)) )
import MyMaybe
import Prelude hiding (GT, LT, EQ)
import TheNil

parseIdExp::ReadP PCEAtom
parseIdExp = skipSpaces >> parseId >>= return . IdExp

parseTrue::ReadP PCEAtom
parseTrue = string "true" >> return TrueExp

parseFalse::ReadP PCEAtom
parseFalse = string "false" >> return FalseExp

parseNumExp::ReadP PCEAtom
parseNumExp = do
    sn<-parseNumber
    let n = read sn::Int
    return (NumExp n)

parseParExp::ReadP PCEAtom
parseParExp = do
    skipSpaces
    char '(' 
    skipSpaces
    e<-parsePCExp_
    skipSpaces
    char ')' 
    skipSpaces
    return $ ParExp e

parseDotExp::ReadP PCEAtom
parseDotExp = do
    skipSpaces
    id <- parseId
    char '.' 
    e<-parsePCExpA
    skipSpaces
    return $ DotExp id e

parsePCExpA::ReadP PCEAtom
parsePCExpA = parseTrue <|> parseFalse <|> parseIdExp <|> parseNumExp 
    <|> parseParExp <|> parseDotExp

parseBinOpGT::ReadP PCERelOp
parseBinOpGT = char '>' >> return OGT

parseBinOpLT::ReadP PCERelOp
parseBinOpLT = char '<' >> return OLT

parseBinOpGEQ::ReadP PCERelOp
parseBinOpGEQ = char '≥' >> return OGEQ

parseBinOpLEQ::ReadP PCERelOp
parseBinOpLEQ = char '≤' >> return OLEQ

parseBinOpEQ::ReadP PCERelOp
parseBinOpEQ = char '=' >> return OEQ

parseBinOpNEQ::ReadP PCERelOp
parseBinOpNEQ = char '≠' >> return ONEQ

parseRelOp::ReadP PCERelOp
parseRelOp = parseBinOpGT 
    <|> parseBinOpLT 
    <|> parseBinOpGEQ 
    <|> parseBinOpLEQ 
    <|> parseBinOpEQ  
    <|> parseBinOpNEQ

parseRelOpExp::ReadP PCE
parseRelOpExp = do
    skipSpaces
    e1<-parsePCExpA
    skipSpaces
    op<-parseRelOp
    skipSpaces
    e2<-parsePCExp_
    skipSpaces
    return $ RelOpExp op e1 e2



--parsePCExpC::ReadP PCExpC
--parsePCExpC =  parseDotExp 

parsePCExp_Atom::ReadP PCE
parsePCExp_Atom = parsePCExpA >>= return . ExpAtom 

--parsePCExp_C::ReadP PCExp
--parsePCExp_C = parsePCExpC >>= return . ExpC

parseBinOpPlus::ReadP PCEBinOp
parseBinOpPlus = char '+' >> return Plus

parseBinOpMinus::ReadP PCEBinOp
parseBinOpMinus = char '-' >> return Minus

parseBinOpProd::ReadP PCEBinOp
parseBinOpProd = char '*' >> return Prod

parseBinOpDiv::ReadP PCEBinOp
parseBinOpDiv = char '/' >> return Prod

parseBinOpRemainder::ReadP PCEBinOp
parseBinOpRemainder = char '%' >> return Remainder

parseBinOpAnd::ReadP PCEBinOp
parseBinOpAnd = char '⋀' >> return And

parseBinOpOr::ReadP PCEBinOp
parseBinOpOr = char '⋁' >> return Or

parseBinOp::ReadP PCEBinOp
parseBinOp = parseBinOpPlus <|> parseBinOpMinus <|> parseBinOpProd 
    <|> parseBinOpDiv <|> parseBinOpRemainder
    <|> parseBinOpAnd <|> parseBinOpOr

parseUnaryOpMinus::ReadP PCEUnOp
parseUnaryOpMinus = char '-' >> return UMinus

parseUnaryOpNot::ReadP PCEUnOp
parseUnaryOpNot = char '¬' >> return UNot

parseUnaryOp::ReadP PCEUnOp
parseUnaryOp = parseUnaryOpMinus <|> parseUnaryOpNot

parseBinaryExp::ReadP PCE
parseBinaryExp = do
    e1<-parsePCExpA
    skipSpaces
    op<-parseBinOp
    skipSpaces
    e2<-parsePCExp_
    skipSpaces
    return (BinExp op e1 e2 )

parseUnaryExp::ReadP PCE
parseUnaryExp = do
    op<-parseUnaryOp
    skipSpaces
    e<-parsePCExp_
    skipSpaces
    return (UnExp op e)

parseSetE::ReadP PCE
parseSetE = do
    char '{'
    skipSpaces
    es<-parseTokens "," parsePCExp_
    skipSpaces
    char '}'
    return (SetE es)

parsePCExp_::ReadP PCE
parsePCExp_ = parsePCExp_Atom <|> parseBinaryExp <|> parseUnaryExp 
    <|> parseSetE <|> parseRelOpExp 

parsePCExp::String->Maybe PCE
parsePCExp = parseMaybe parsePCExp_

parsePCExpAtom::String->Maybe PCEAtom
parsePCExpAtom = parseMaybe parsePCExpA

test1 :: [(PCERelOp, String)]
test1 = readP_to_S parseRelOp "≥"
test2a :: [(PCEAtom, String)]
test2a = readP_to_S parsePCExpA "t"
test2b :: [(PCEAtom, String)]
test2b = readP_to_S parsePCExpA "0"
test2c :: [(PCEAtom, String)]
test2c= readP_to_S parseParExp "(t≥0)"
test3a :: [(PCE, String)]
test3a = readP_to_S parsePCExp_ "t≥0"
test3c :: [(PCE, String)]
test3c = readP_to_S parsePCExp_ "(n≥0) ⋀ (n≤m)"