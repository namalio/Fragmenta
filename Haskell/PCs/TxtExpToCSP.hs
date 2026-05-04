module PCs.TxtExpToCSP 
    (toCSPExp
    ) where

import qualified CSP.CSP_AST as CSP
--import qualified PCs.PCTrees_Exp as PCTsExp
import qualified PCs.TxtExpAST as PCTsExp
--import PCs.PCTrees_Exp (PCEBinOp(Prod), PCELitBool(..))

toCSPBOp::PCTsExp.BinOp->CSP.BOp
toCSPBOp PCTsExp.Plus = CSP.Plus
toCSPBOp PCTsExp.Minus = CSP.Minus
toCSPBOp PCTsExp.Div = CSP.Div
toCSPBOp PCTsExp.Prod = CSP.Product
toCSPBOp PCTsExp.Remainder = CSP.Remainder
toCSPBOp PCTsExp.And = CSP.And
toCSPBOp PCTsExp.Or = CSP.Or
toCSPBOp PCTsExp.Cup = CSP.Union
toCSPBOp PCTsExp.Cap = CSP.Intersection

toCSPRelOp::PCTsExp.RelOp->CSP.BOp
toCSPRelOp PCTsExp.OGT = CSP.GT
toCSPRelOp PCTsExp.OLT = CSP.LT
toCSPRelOp PCTsExp.OLEQ = CSP.LEQ
toCSPRelOp PCTsExp.OGEQ = CSP.GEQ
toCSPRelOp PCTsExp.OEQ = CSP.EQ
toCSPRelOp PCTsExp.ONEQ = CSP.NEQ
toCSPRelOp PCTsExp.OIN = CSP.Member

toCSPUOp::PCTsExp.UnOp->CSP.UOp
toCSPUOp PCTsExp.UMinus = CSP.UMinus
toCSPUOp PCTsExp.UNot = CSP.UNot

toCSPExp::PCTsExp.Exp->CSP.Exp
toCSPExp (PCTsExp.ExpBin op e1 e2) = CSP.ExpBOp (toCSPExp e1) (toCSPBOp op) (toCSPExp e2)
toCSPExp (PCTsExp.ExpRel op e1 e2) = CSP.ExpBOp (toCSPExp e1) (toCSPRelOp op) (toCSPExp e2)
toCSPExp (PCTsExp.ExpUn op e) = CSP.ExpUOp (toCSPUOp op) (toCSPExp e)
toCSPExp (PCTsExp.ExpSet es) = CSP.ExpSetE (map toCSPExp es)
toCSPExp (PCTsExp.ExpId id) = CSP.ExpId id
toCSPExp (PCTsExp.ExpInt k) = CSP.ExpToken (CSP.TokenInt k)
toCSPExp (PCTsExp.ExpDot e1 e2) = CSP.ExpChannel (toCSPExp e1) (toCSPExp e2)
toCSPExp (PCTsExp.ExpB bt) = if bt == PCTsExp.TrueT then CSP.ExpToken CSP.TokenT else CSP.ExpToken CSP.TokenF
toCSPExp (PCTsExp.ExpPar e) = CSP.ExpPar (toCSPExp e)

