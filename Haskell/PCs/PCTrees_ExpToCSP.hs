module PCs.PCTrees_ExpToCSP (
    toCSPExp
    , toCSPExpA) where

import qualified CSP.CSP_AST as CSP
import qualified PCs.PCTrees_Exp as PCTsExp
import PCs.PCTrees_Exp (PCEBinOp(Prod), PCELitBool(..))

toCSPBOp::PCTsExp.PCEBinOp->CSP.BOp
toCSPBOp PCTsExp.Plus = CSP.Plus
toCSPBOp PCTsExp.Minus = CSP.Minus
toCSPBOp PCTsExp.Div = CSP.Div
toCSPBOp PCTsExp.Prod = CSP.Product
toCSPBOp PCTsExp.Remainder = CSP.Remainder
toCSPBOp PCTsExp.And = CSP.And
toCSPBOp PCTsExp.Or = CSP.Or

toCSPRelOp::PCTsExp.PCERelOp->CSP.BOp
toCSPRelOp PCTsExp.OGT = CSP.GT
toCSPRelOp PCTsExp.OLT = CSP.LT
toCSPRelOp PCTsExp.OLEQ = CSP.LEQ
toCSPRelOp PCTsExp.OGEQ = CSP.GEQ
toCSPRelOp PCTsExp.OEQ = CSP.EQ
toCSPRelOp PCTsExp.ONEQ = CSP.NEQ

toCSPUOp::PCTsExp.PCEUnOp->CSP.UOp
toCSPUOp PCTsExp.UMinus = CSP.UMinus
toCSPUOp PCTsExp.UNot = CSP.UNot

toCSPExpA::PCTsExp.PCEAtom->CSP.Exp
toCSPExpA (PCTsExp.IdExp id) = CSP.ExpId id
toCSPExpA (PCTsExp.NumExp k) = CSP.ExpToken (CSP.TokenInt k)
toCSPExpA (PCTsExp.DotExp id e) = CSP.ExpChannel id $ toCSPExpA e
toCSPExpA (PCTsExp.BLit bl) = if bl == TrueL then CSP.ExpToken CSP.TokenT else CSP.ExpToken CSP.TokenF
-- toCSPExpA PCTsExp.FalseExp = 
toCSPExpA (PCTsExp.ParExp e) = CSP.ExpPar (toCSPExp e)

toCSPExp::PCTsExp.PCE->CSP.Exp
toCSPExp (PCTsExp.ExpAtom ea) = toCSPExpA ea
toCSPExp (PCTsExp.BinExp op ea e) = CSP.ExpBOp (toCSPExpA ea) (toCSPBOp op) (toCSPExp e)
toCSPExp (PCTsExp.UnExp op e) = CSP.ExpUOp (toCSPUOp op) (toCSPExp e)
toCSPExp (PCTsExp.SetE es) = CSP.ExpSetE (map toCSPExp es)