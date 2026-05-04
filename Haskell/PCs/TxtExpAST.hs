module PCs.TxtExpAST 
    ( Exp(..)
    , BoolTerm(..)
    , UnOp(..)
    , BinOp(..)
    , RelOp(..)
    , isExpId  
    , gIdFrExp
    , show_parsed
    , showExp
    , leadingId
    , toTerms
    )
    where

import PCs.Common(Id)
import ShowUtils (showElems')

data BoolTerm
    = TrueT
    | FalseT
    deriving (Show, Eq)

data UnOp 
    = UMinus 
    | UNot
    deriving (Show, Eq)

data BinOp 
    = Plus 
    | Minus 
    | Prod 
    | Div 
    | Remainder 
    | And 
    | Or 
    | Cup
    | Cap
    deriving (Show, Eq)

data RelOp 
    = OGT 
    | OLT 
    | OLEQ 
    | OGEQ 
    | OEQ 
    | ONEQ 
    | OIN
    deriving (Show, Eq)

data Exp
      = ExpBin BinOp Exp Exp
      | ExpRel RelOp Exp Exp
      | ExpUn UnOp Exp
      | ExpDot Exp Exp
      | ExpB BoolTerm
      | ExpId Id
      | ExpInt Int
      | ExpPar Exp
      | ExpSet [Exp]
      deriving (Show, Eq)

isAtom::Exp->Bool
isAtom (ExpB _)   = True
isAtom (ExpId _)  = True
isAtom (ExpInt _) = True
isAtom (ExpPar _)  = True
isAtom (ExpSet _)  = True
isAtom (ExpUn _ e) = isAtom e
isAtom _           = False

leadingId::Exp->String
leadingId (ExpBin _ _ _)   = ""
leadingId (ExpRel _ _ _)   = ""
leadingId (ExpUn _ _)   = ""
leadingId (ExpDot e _)   = leadingId e
leadingId (ExpB _)   = ""
leadingId (ExpId id) = id
leadingId (ExpInt _) = ""
leadingId (ExpPar e) = leadingId e
leadingId (ExpSet _) = ""

toTerms0::Exp->[String]->[String]
toTerms0 (ExpId id) ts = id:ts
toTerms0 (ExpDot e1 e2) ts = toTerms0 e1 (toTerms0 e2 ts) 
toTerms0 _ ts = ts

toTerms::Exp->[String]
toTerms e = toTerms0 e []

--instance Show BoolTerm where
showBT::BoolTerm->String
showBT TrueT  = "True"
showBT FalseT = "False"

showRO::RelOp->String
showRO OGT  = ">"
showRO OLT  = "<"
showRO OLEQ = "≤"
showRO OGEQ = "≥"
showRO OEQ  = "="
showRO ONEQ = "≠"
showRO OIN   = "∊"

--instance Show BinOp where
showBO::BinOp->String
showBO Plus      = "+"
showBO Minus     = "-"
showBO Prod      = "*"
showBO Div       = "/"
showBO Remainder = "%"
showBO And       = "⋀"
showBO Or        = "⋁"
showBO Cup       = "∪"
showBO Cap       = "∩"
    

showUO::UnOp->String
showUO UMinus = "-"
showUO UNot   = "¬"

showExp_::Exp->String
showExp_ e = if isAtom e then show_parsed e else "(" ++ show_parsed e ++ ")"

showExps::[Exp]->(Exp->String)->String
showExps es sf = foldr(\e s->sf e ++ if null s then s else (',':s)) [] es

show_parsed::Exp->String
show_parsed (ExpBin op e1 e2) = (showExp_ e1) ++ " " ++ showBO op ++ " " ++ (showExp_ e2)
show_parsed (ExpRel op e1 e2) = (showExp_ e1) ++ " " ++ showRO op ++ " " ++ (showExp_ e2)
show_parsed (ExpUn op e)      = showUO op ++ showExp_ e
show_parsed (ExpDot e1 e2)    = (showExp_ e1) ++ "." ++ (showExp_ e2)
show_parsed (ExpB t)          = showBT t
show_parsed (ExpId id)        = id
show_parsed (ExpInt n)        = show n
show_parsed (ExpPar e)        = "(" ++ showExp e ++ ")"
show_parsed (ExpSet es)       = "{" ++ showExps es showExp_ ++ "}" 
--foldr(\e s->show e ++ if null s then s else (',':s)) [] es ++ "}"


showExp::Exp->String
showExp (ExpBin op e1 e2) = (showExp e1) ++ " " ++ showBO op ++ " " ++ (showExp e2)
showExp (ExpRel op e1 e2) = (showExp e1) ++ " " ++ showRO op ++ " " ++ (showExp e2)
showExp (ExpUn op e)      = showUO op ++ (showExp e)
showExp (ExpDot e1 e2)    = (showExp e1) ++ "." ++ (showExp e2)
showExp (ExpB t) = showBT t
showExp (ExpId id) = id
showExp (ExpInt n) = show n
showExp (ExpPar e) = "(" ++ showExp e ++ ")"
showExp (ExpSet es) =  "{" ++ showExps es showExp ++ "}" 

isExpId::Exp->Bool
isExpId (ExpId _) = True
isExpId _ = False

gIdFrExp::Exp->String
gIdFrExp (ExpId id) = id