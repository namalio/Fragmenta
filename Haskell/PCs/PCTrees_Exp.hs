--------------------------------
-- Project: PCs
-- Module: 'PCTress_Exp'
-- Description: Module responsible for PCT expresions 
-- Author: Nuno Amálio
--------------------------------
module PCs.PCTrees_Exp 
    (PCERelOp(..)
    , pcteOps
    , PCEBinOp(..)
    , PCE(..)
    , PCEUnOp(..)
    , PCELitBool(..)
    , PCEAtom(..)
    , cIdExp)
where

import PCs.PCsCommon(Id)
import ShowUtils
import SGrs (SGVCEOP(Neq))

data PCERelOp 
    =  OGT 
    | OLT 
    | OLEQ 
    | OGEQ 
    | OEQ 
    | ONEQ 
    deriving Eq

pcteOps::[PCERelOp]
pcteOps = [OGT, OLT, OLEQ, OGEQ, OEQ, ONEQ]

data PCEBinOp 
    = Plus 
    | Minus 
    | Prod 
    | Div 
    | Remainder 
    | And 
    | Or 
    deriving Eq

data PCEUnOp 
    = UMinus 
    | UNot
    deriving Eq

data PCELitBool
    = TrueL
    | FalseL
    deriving Eq

-- A PCTEAtom 
data PCEAtom 
    = IdExp Id 
    | BLit PCELitBool
    | NumExp Int 
    | ParExp PCE 
    | DotExp Id PCEAtom
    deriving Eq

-- A PC expression
data PCE 
   = ExpAtom PCEAtom
   | RelOpExp PCERelOp PCEAtom PCE
   | BinExp PCEBinOp PCEAtom PCE 
   | UnExp PCEUnOp PCE 
   | SetE [PCE]
   deriving Eq

instance Show PCERelOp where
    show::PCERelOp->String
    show OGT  = ">"
    show OLT  = "<"
    show OLEQ = "≤"
    show OGEQ = "≥"
    show OEQ  = "="
    show ONEQ = "≠"

instance Show PCEBinOp where
    show::PCEBinOp->String
    show Plus  = "+"
    show Minus = "-"
    show Prod  = "*"
    show Div   = "/"
    show Remainder = "%"
    show And = "⋀"
    show Or = "⋁"

instance Show PCEUnOp where
    show UMinus = "-"
    show UNot = "¬"

--instance Show PCExpC where
    --show::PCExpAtom->String

instance Show PCELitBool where
    show TrueL = "True"
    show FalseL = "False"

instance Show PCEAtom where
    show (IdExp id) = id
    show (BLit lb) = show lb
    show (NumExp k) = show k
    show (ParExp e) = ('(':show e)++")"
    show (DotExp id e) = id ++ ('.':show e)

--showBinaryExp::PCExp->PCExp->String->String
--showBinaryExp e1 e2 op = show e1 ++ " " ++ op ++ " " ++ show e2
cIdExp::Id->PCE
cIdExp = ExpAtom . IdExp

instance Show PCE where
    show (ExpAtom e) = show e 
    show (BinExp op e1 e2) = show e1 ++ " " ++ show op ++ " " ++ show e2
    show (UnExp op e) = show op ++ show e
    show (SetE es) = '{':showStrs (fmap show es) "," ++"}"
    show (RelOpExp op e1 e2) = show e1 ++ show op ++ show e2 

