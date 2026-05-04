
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
   (ROp(..)
   , gParamId
   , DTDef(..)
   , VTerm(..)
   )
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
   | otherwise = CSP.ExtChoice (genAfterC mmi pc (the $ successorsOf mmi pc ch)) (genChoices mmi pc chs)

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
   | tyOfN n pc == show_cmm_n CMM_Operator && (opValOfOp (gCRSG mmi) pc n) == show_cmm_n CMM_VOpExtChoice = genChoices mmi pc (successorsOf mmi pc n)  
   | otherwise = CSP.SKIP -- INCOMPLETE
   

findAfterAtom :: (Foldable t, GR g, GRM gm, Eq a, Eq b) => g String a -> gm String b -> t String -> Set String
findAfterAtom pc m n = (predecessors pc n) `intersec` (ran_of $ rres (src pc) $ img (inv $ fV m) [show_cmm_n CMM_AfterC])

cspAtoms :: Env->[CSP.Decl]
cspAtoms env = 
   --let as = (atomsOfPD pdt) `union` ias in
   let r = filterS (\(_, t)->isEventTy t) (rel env) in
      foldl (\ds t->(CSP.Channel  (img (inv r) $ singles t) (cspOfTy t)):ds) [] (reduce . ran_of $ r)
   where -- Dot types associate to the left unlike Dot expressions (which associate to the right)
      cspOfTy (TDot t1 TEvent) = Just (doTy1 t1)
      cspOfTy (TDot t1 t2) = Just $ (doTy1 t1) ++ "."  ++ (cspTy t2)
      cspOfTy TEvent = Nothing
      --cspOfTy t = error $ "Unexpected type " ++ (show t)
      doTy1 t = if isAtomic t then cspTy t else the . cspOfTy $ t
      cspTy (TInt) = "Int"
      cspTy (TBool) = "Bool"
      cspTy (TId id) = id
      isAtomic (TInt) = True
      isAtomic (TBool) = True
      isAtomic (TId _) = True
      isAtomic _ = False

--Channel $ foldl(\ns n-> let n' = nmOfNamed pc m n in if n' `elem` ias then ns else insert n' ns) [] (getAtoms m)

--cspPImports sg_mm pc = Include $ map (\mn->mn ++ "P") (importsOf sg_mm pc)

cspImports :: Set String -> CSP.Decl
cspImports is = CSP.Include $ is

cspDataType::DTDef->CSP.Decl
cspDataType (DTDef id vts) = CSP.DataTy id (transform vts)
   where transform [vt] = [transform_t vt]
         transform (vt:vts) = (transform_t vt):(transform vts)
         transform_t (VTerm id ts) = CSP.DTyTerm id (fmap cspTD ts)

--cspDecl (ts@(TSeq _ _)) = snd $ cspExp ts
--cspDecl (c@(Compound n ps t)) = 
--   let (e, cds) = cspExp c in
--   [LetW cds e] 
--cspDecl (OpB _ t1 t2) = cspDecl t1 ++ cspDecl t2
cspDecl :: Foldable t => t PT -> [CSP.Decl]
cspDecl pds = foldr (\pd scts->(snd $ cspExp pd) ++ scts) [] pds

--cspDecls ts = foldr (\t ts'-> (cspDecl t)++ts') [] ts

--data BothOpt = Both (PCT->Bool) (PCT->Bool) | Fst (PCT->Bool) | Snd (PCT->Bool) | None 
data BothOpt 
   = Both (CSP.Exp->Bool) (CSP.Exp->Bool) 
   | Fst (CSP.Exp->Bool) | Snd (CSP.Exp->Bool) 
   | None

cspExpsFor0 :: PT -> PT -> (CSP.Exp, CSP.Exp, [CSP.Decl])
cspExpsFor0 t1 t2 = 
    let (e1, cds1) = cspExp t1 
        (e2, cds2) = cspExp t2 in
    (e1, e2, cds1++cds2)

oparExp :: CSP.Exp -> (CSP.Exp -> Bool) -> CSP.Exp
oparExp e f = if f e then CSP.ExpPar e else e
calcExp1 :: CSP.Exp -> BothOpt -> CSP.Exp
calcExp1 e (Both f _) = oparExp e f
calcExp1 e (Fst f) = oparExp e f
calcExp1 e (Snd f) = e
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

cspExpsFor :: PT -> PT -> BothOpt -> (CSP.Exp, CSP.Exp, [CSP.Decl])
cspExpsFor t1 t2 pfs = 
    let (e1, e2, cds) = cspExpsFor0 t1 t2 in
    (calcExp1 e1 pfs, calcExp2 e2 pfs, cds)

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

cspTD::PCTTypeD->String
cspTD Int = "Int" 
cspTD Bool = "Bool"
cspTD (DT id) = id

cspExp :: PT -> (CSP.Exp, [CSP.Decl])
cspExp NilT = (CSP.SKIP, [])
cspExp StopT = (CSP.STOP, [])
cspExp SkipT = (CSP.SKIP, [])
cspExp (Atom e og) = 
    --let e = if isNil oe then ExpId a else ExpChannel a (ExpId $ the oe) in
    pairUp (if isNil og then toCSPExp e else CSP.GExp (toCSPExp $ the og) (toCSPExp e)) [] 
cspExp (OpKappa n op t)  =
   let e1 = cspPDef t in
   (rOpOf op e1, [])
   where rOpOf (OpRExtChoice v td) e1 = CSP.RExtChoice v (cspTD td) e1
         rOpOf (OpRIntChoice v td) e1 = CSP.RIntChoice v (cspTD td)  e1
cspExp (Kappa n ps cpds t)  = 
   let e1 = cspPRef n Nothing (map (PCTsExp.ExpId . gParamId) ps) nil
       e2 = cspPDef t
       e2' = if isSomething cpds then consLetW (cspDecl cpds) e2 else e2 in
   (e1, [CSP.EqDecl e1 e2'])
cspExp (Rho n g bs rs) = (cspPRef n g bs rs, [])
cspExp (OpB (OpIf g) t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 None in
   (CSP.IfExp (toCSPExp g) e1 e2, cds) 
cspExp (OpB (OpSeq o) t1 t2) = if isAtom t1 then cspExpPrfx t1 t2 else cspExpSeq t1 t2 
   -- | isAtomAny t1 && (o || t2 == NilT) = cspExpREC t1 t2 
   -- | isAtomAny t1 && not o = let (e1, ds1) = cspExpREC t1 NilT in let (e2, ds2) = cspExp t2 in (SeqComp e1 e2, ds1++ds2)
   -- | otherwise    = if isAtom t1 then cspExpPrfx t1 t2 else cspExpSeq t1 t2 
cspExp (OpB OpExtChoice t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 (Both CSP.isComposite (not . f)) in
   (CSP.ExtChoice e1 e2, cds)
   where f e = CSP.isAtomicExp e || CSP.isExtChoice e
cspExp (OpB OpIntChoice t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 (Both CSP.isComposite CSP.isComposite) in
   (CSP.IntChoice e1 e2, cds)
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

toCSP::MMI String String->PC String String->Set String->Env->(CSP.Spec, CSP.Spec)
toCSP mmi pc is env = 
   let PCTD _ dts cpds = consPCTD mmi pc [] 
       ads = cspAtoms env
       dts' = foldl (\dts' dt->(cspDataType dt):dts') [] dts
       is0 = fmap (namePCOfImport pc) is
       is' = cspImports (fmap (++"P") ((getPCDefN pc) `intoSet` is0 )) in
   (CSP.CSP ([is'] ++ dts' ++ ads ), CSP.CSP $ cspDecl cpds)