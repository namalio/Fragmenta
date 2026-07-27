
------------------
-- Project: PCs/Fragmenta
-- Module: 'ToCSP'
-- Description: Module responsible for transforming PCTs into CSP
-- Author: Nuno Amálio
-----------------
module PCs.ToCSP
   ( findAfterAtom
   , toCSP
   ) where

import PCs.PCs
import qualified CSP.CSP_AST as CSP
import Relations
import Sets
import Grs
import Gr_Cls
import SGrs
import CSP.CSPPrint
import PCs.PCTrees
import TheNil
import MyMaybe
import PCs.MM_Names
import GrswT
import SimpleFuns
import MMI
import qualified PCs.TxtExpAST as PCTsExp
import PCs.PCTreesAST
   ( ROp(..)
   , ROpT(..)
   , DTDef(..)
   , VTerm(..)
   , gPTs
   , gDTDs
   )
import PCs.Common 
   ( gParamId
   , PCTypeD(..)
   , PCTypeE(..))
import PCs.TxtExpToCSP(toCSPExp)
--import PCs.PCTrees_Exp
import PCs.PCTrees_Types
import PCs.SymbMap 

genAfterC :: MMI String String -> PC String String -> String -> CSP.Exp
genAfterC mmi pc n
   | tyOfN n pc == show_cmm_n CMM_Reference = CSP.ExpId (nmOfRef pc n)
   | tyOfN n pc == show_cmm_n CMM_Atom = genAtom mmi pc n
   | tyOfN n pc == show_cmm_n CMM_Process = genProcessDef mmi pc n
   | otherwise = CSP.SKIP

genAfterAtom :: MMI String String -> GrwT String String -> String -> Set String -> CSP.Exp
genAfterAtom _ _ _ EmptyS = CSP.SKIP
genAfterAtom mmi pc n (Set n2 EmptyS) 
   | n2 `elem` img (inv $ fV pc) [show_cmm_n CMM_AfterC] = genAfterC mmi pc (the $ successorsOf mmi pc n2)
   | otherwise = CSP.SKIP

genAtom :: MMI String String -> PC String String -> CSP.Id -> CSP.Exp
genAtom mmi pc n = CSP.Prfx (CSP.ExpId n) $ genAfterAtom mmi pc n (successorsOf mmi pc n)

genChoices :: MMI String String -> PC String String -> Set String -> CSP.Exp
genChoices mmi pc EmptyS = CSP.SKIP
genChoices mmi pc (Set ch chs) 
   | null chs = genAfterC mmi pc (the $ successorsOf mmi pc ch)
   | otherwise = CSP.Choice CSP.Int (genAfterC mmi pc (the $ successorsOf mmi pc ch)) (genChoices mmi pc chs)

--genDeclsForCompounds pc m cns = (map (\cn->genCompound pc m cn) cns)
--genRelevantForAtomic pc m n cns = if (not $ null cns) 
--   then LetW (genDeclsForCompounds pc m cns) (genAtomic pc m n) 
--   else (genAtomic pc m n)

genCompoundSeqComp :: MMI String String -> PC String String -> String -> CSP.Exp
genCompoundSeqComp mmi pc n =
   let e = first $ (successorsOf mmi pc n) `intersec` (ntyNsPC (gCRSG mmi) pc CMM_AfterC) in
   let next_n = the $ successorsOf mmi pc e in
   CSP.SeqComp (CSP.ExpId n) (genAfterC mmi pc next_n) 

genProcessDef :: MMI String String -> PC String String -> String -> CSP.Exp
genProcessDef mmi pc n 
   | tyOfN n pc == show_cmm_n CMM_Atom = genAtom mmi pc n
   -- Either a process reference or sequential composition
   | tyOfN n pc == show_cmm_n CMM_Process = if (show_cmm_n CMM_AfterC) `elem` (img (fV pc) (successorsOf mmi pc n)) 
      then (genCompoundSeqComp mmi pc n) else CSP.ExpId n 
   -- something combined with an operator
   | tyOfN n pc == show_cmm_n CMM_Operator && (opCombinable (gCRSG mmi) pc n) == show_cmm_n CMM_VOpExtChoice = genChoices mmi pc (successorsOf mmi pc n)  
   | otherwise = CSP.SKIP -- INCOMPLETE
   

findAfterAtom :: (Foldable t, GR g, GRM gm, Eq a, Eq b) => g String a -> gm String b -> t String -> Set String
findAfterAtom pc m n = (predecessors pc n) `intersec` (ran_of $ rres (src pc) $ img (inv $ fV m) [show_cmm_n CMM_AfterC])

cspChannels :: Env->[CSP.Decl]
cspChannels env = 
   --let as = (atomsOfPD pdt) `union` ias in
   --let r = filterS (isEvTy . snd) env in
   canali (reduce . ran_of $ env)
   --foldl (\ds t->if isEvTy t then (CSP.Channel  (img (inv env) $ singles t) (cspOfTy t)):ds else ds) [] (reduce . ran_of $ env)
   where -- Dot types associate to the left unlike Dot expressions (which associate to the right)
      canali EmptyS = []
      canali (t `Set` ts) = 
         (if isEvTy t then [CSP.Channel (img (inv env) $ singles t) (cspOfTy t)] else []) ++ canali ts
      cspOfTy TEvent = Nothing 
      cspOfTy t = Just . cspTy $ t 
      cspTy (TDot t1 TEvent) = cspTy t1
      cspTy (TDot t1 t2) = CSP.TyDot (cspTy t1) (cspTy t2)
      cspTy (TSet t) = CSP.TySet $ cspTy t
      cspTy TInt = CSP.TyInt
      cspTy TBool = CSP.TyBool
      cspTy (TId id) = CSP.TyId id
      --cspTy t = error $ "Unexpected type " ++ (show t) ++ " " ++ (show env)
      --doTy1 t = if isAtomic t then cspTy t else the . cspOfTy $ t
      --cspTy TInt = "Int"
      --cspTy TBool = "Bool"
      --cspTy (TId id) = id
      --isAtomic TInt = True
      --isAtomic TBool = True
      --isAtomic (TId _) = True
      --isAtomic _ = False

--Channel $ foldl(\ns n-> let n' = nmOfNamed pc m n in if n' `elem` ias then ns else insert n' ns) [] (getAtoms m)

--cspPImports sg_mm pc = Include $ map (\mn->mn ++ "P") (importsOf sg_mm pc)

cspImports :: Set String -> CSP.Decl
cspImports is = CSP.Include $ is

cspDTD::DTDef->CSP.Decl
cspDTD (DTDef id vts) = CSP.DataTy id (fmap cspVT vts)
   where cspVT (VTerm id ts) = CSP.DTyTerm id (fmap cspTD ts)

--cspDecl (ts@(TSeq _ _)) = snd $ cspExp ts
--cspDecl (c@(Compound n ps t)) = 
--   let (e, cds) = cspExp c in
--   [LetW cds e] 
--cspDecl (OpB _ t1 t2) = cspDecl t1 ++ cspDecl t2
cspDecl :: [PT] -> [CSP.Decl]
cspDecl [] = []
cspDecl (pt:pts) = (snd . cspExp $ pt) ++ (cspDecl pts)

--cspDecls ts = foldr (\t ts'-> (cspDecl t)++ts') [] ts

--data BothOpt = Both (PCT->Bool) (PCT->Bool) | Fst (PCT->Bool) | Snd (PCT->Bool) | None 
data BothOpt 
   = Both (CSP.Exp->Bool) (CSP.Exp->Bool) 
   | Fst (CSP.Exp->Bool) | Snd (CSP.Exp->Bool) 
   | None

oparExp :: CSP.Exp -> (CSP.Exp -> Bool) -> CSP.Exp
oparExp e f = if f e then CSP.ExpPar e else e
calcExp1 :: CSP.Exp -> BothOpt -> CSP.Exp
calcExp1 e (Both f _) = oparExp e f
calcExp1 e (Fst f) = oparExp e f
calcExp1 e (Snd _) = e
calcExp1 e None = e
calcExp2 :: CSP.Exp -> BothOpt -> CSP.Exp
calcExp2 e (Both _ f) = oparExp e f
calcExp2 e (Fst f) = e 
calcExp2 e (Snd f) = oparExp e f
calcExp2 e None = e
-- cspExpsFor t1 t2 (Both f f') = 
--     let (e1, e2, cds) = cspExpsFor0 t1 t2 in
--     let e1' = if f t1 then ExpPar e1 else e1 in
--     let e2' = if f' t2 then ExpPar e2 else e2 in
--     (e1', e2', cds)

-- cspExpsFor t1 t2 (Fst f) = 
--     let (e1, e2, cds) = cspExpsFor0 t1 t2 in
--     let e1' = if f t1 then ExpPar e1 else e1 in
--     (e1', e2, cds)

-- cspExpsFor t1 t2 (Snd f) = 
--     let (e1, e2, cds) = cspExpsFor0 t1 t2 in
--     let e2' = if f t2 then ExpPar e2 else e2 in
--     (e1, e2', cds)

-- cspExpsFor t1 t2 None = cspExpsFor0 t1 t2

--cspExpsFor0 :: PT -> PT -> (CSP.Exp, CSP.Exp, [CSP.Decl])
--cspExpsFor0 t1 t2 = 
--    let (e1, ds1) = cspExp t1 
--        (e2, ds2) = cspExp t2 in
--    (e1, e2, ds1++ds2)

cspExpsFor :: PT -> PT -> BothOpt -> (CSP.Exp, CSP.Exp, [CSP.Decl])
cspExpsFor t1 t2 pfs = 
    let (e1, e2, cds) = combine (cspExp t1) (cspExp t2) in
    (calcExp1 e1 pfs, calcExp2 e2 pfs, cds)
    where combine (e1, ds1) (e2, ds2) =  (e1, e2, ds1++ds2)

cspPRef ::CSP.Id->Maybe PCTsExp.Exp->[PCTsExp.Exp]->Rel CSP.Id CSP.Id->CSP.Exp
cspPRef n g bs rs = 
   let e1 = if null bs then CSP.ExpId n else CSP.ExpApp n (map toCSPExp bs) in
   let e2 = if null rs then e1 else CSP.ExpRen e1 (toList rs) in
   if isNil g then e2 else CSP.GExp (toCSPExp $ the g) e2 

cspPDef :: PT -> CSP.Exp
cspPDef t =
   let (e, ds) = cspExp t in
   if null ds then e else CSP.LetW ds e

--cspPDefW n t =
--   let (e, ds) = cspExp t in
--   let e1 = cspPRef (n ++ "0") [] in
--   let d = EqDecl (ExpId $ n++ "0") e in
--   if null ds then LetW [d] e1 else LetW (d:ds) e1

cspExpPrfx :: PT -> PT -> (CSP.Exp, [CSP.Decl])
cspExpPrfx t1 t2 = 
    let (e1, e2, cds) = cspExpsFor t1 t2 (Snd CSP.isComposite) in
    (CSP.Prfx e1 e2, cds)

cspExpSeq :: PT -> PT -> (CSP.Exp, [CSP.Decl])
cspExpSeq t1 t2 = 
    let (e1, e2, cds) = cspExpsFor t1 t2 (Snd CSP.isComposite) in
    (CSP.SeqComp e1 e2, cds)

consLetW :: [CSP.Decl] -> CSP.Exp -> CSP.Exp
consLetW ds (CSP.LetW ds' e) = CSP.LetW (ds++ds') e
consLetW ds e = CSP.LetW ds e


--cspExpREC :: PCT -> PCT -> (Exp, [Decl])
--cspExpREC (Atom _ og) t2 = 
--  let (e1, ds) = cspExp t2 in
--  --let e2 = ExpPar $ RExtChoice atv ats $ Prfx (ExpId atv) e1 in
--  if isNil og then (e2, ds) else (GExp (ExpId $ the og) e2, ds) 

cspTD::PCTypeD->CSP.Ty
cspTD Int = CSP.TyInt 
cspTD Bool = CSP.TyBool
cspTD Event = CSP.TyEvent
cspTD (Dt id) = CSP.TyId id
cspTD (SetT td) = CSP.TySet (cspTD td)

cspTE::PCTypeE->CSP.TyE
cspTE (TyD td) = CSP.Ty $ cspTD td
cspTE (TIdE id) = CSP.Ty $ CSP.TyId id
cspTE (SetE ids) = CSP.Sete ids 

cspExp :: PT -> (CSP.Exp, [CSP.Decl])
cspExp NilT = (CSP.SKIP, [])
cspExp StopT = (CSP.STOP, [])
cspExp SkipT = (CSP.SKIP, [])
cspExp (Atom e og) = 
    --let e = if isNil oe then ExpId a else ExpChannel a (ExpId $ the oe) in
    (if isNil og then toCSPExp e else CSP.GExp (toCSPExp $ the og) (toCSPExp e), []) 
cspExp (OpKappa (ROp op v te) t)  = 
   let e = cspPDef t in
   (CSP.RChoice (toCSPOp op) v (cspTE te) e, [])
   where toCSPOp OpRExtChoice = CSP.Ext
         toCSPOp OpRIntChoice = CSP.Int
cspExp (Kappa n ps cts t)  = 
   let e1 = cspPRef n Nothing (map (PCTsExp.ExpId . gParamId) ps) nil
       e2 = cspPDef t
       e2' = if isSomething cts then consLetW (cspDecl cts) e2 else e2 in
   (e1, [CSP.EqDecl e1 e2'])
cspExp (Rho n g bs rs) = (cspPRef n g bs rs, [])
cspExp (OpB (OpIf g) t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 None in
   (CSP.IfExp (toCSPExp g) e1 e2, cds) 
cspExp (OpB OpSeq t1 t2) = if isAtom t1 then cspExpPrfx t1 t2 else cspExpSeq t1 t2 
cspExp (OpB OpExtChoice t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 (Both CSP.isComposite (not . f)) in
   (CSP.Choice CSP.Ext e1 e2, cds)
   where f e = CSP.isAtomicExp e || CSP.isExtChoice e
cspExp (OpB OpIntChoice t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 (Both CSP.isComposite CSP.isComposite) in
   (CSP.Choice CSP.Int e1 e2, cds)
cspExp (OpB (OpParallel evs) t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 (Both CSP.isComposite CSP.isComposite) in
   (CSP.Parallel (map toCSPExp evs) e1 e2, cds)
--genCSPExp (Op (OpSyncInterrupt evs) t1 t2) = 
--   let (e1, e2, rts) = genExpsForOps t1 t2 in
--   let e1' = if (isOperator t1) then ExpPar e1 else e1 in
--   let e2' = if (isOperator t2) then ExpPar e2 else e2 in
--   (SyncInterrupt evs e1' e2', rts)
cspExp (OpB (OpThrow evs) t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 (Both CSP.isComposite CSP.isComposite) in
   (CSP.Throw (map toCSPExp evs) e1 e2, cds)
cspExp (OpB OpInterleave t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 (Both CSP.isComposite CSP.isComposite) in
   (CSP.Interleave e1 e2, cds)

toCSP::MMI String String->PC String String->[PC String String]->Env->(CSP.Spec, CSP.Spec)
toCSP mmi pc pcs env = 
   let pctd1 = consPCTD mmi pc [] 
       pctd2 = consPCTD mmi pc pcs
       cs = cspChannels env
       dts = fmap cspDTD (gDTDs pctd2)
       is0 = foldr (\pc is->(getPCDefN pc) `intoSet` is) nil pcs
       is = cspImports (fmap (++"P") ((getPCDefN pc) `intoSet` is0 )) in
   (CSP.CSP ([is] ++ dts ++ cs ), CSP.CSP $ cspDecl (gPTs pctd1))