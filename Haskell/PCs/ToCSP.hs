
------------------
-- Project: PCs/Fragmenta
-- Module: 'PCsCSP'
-- Description: Module responsible for transforming PCTs into CSP
-- Author: Nuno Amálio
-----------------
module PCs.ToCSP(findAfterAtom, toCSP) where

import PCs.PCs
import CSP.CSP_AST
import Relations
import Sets
import Grs
import Gr_Cls
import SGrs
import CSP.CSPPrint
import PCs.PCTrees
import TheNil
import MyMaybe
import PCs.PCs_MM_Names
import GrswT
import SimpleFuns
import MMI
import PCs.PCTrees_AST(ROp(..), gParamId, PCE)
import PCs.PCTrees_ExpToCSP(toCSPExp, toCSPExpA)
import PCs.PCTrees_Exp

genAfterC :: MMI String String -> PC String String -> String -> Exp
genAfterC mmi pc n
   | tyOfN n pc == show_cmm_n CMM_Reference = ExpId (nmOfRef pc n)
   | tyOfN n pc == show_cmm_n CMM_Atom = genAtom mmi pc n
   | tyOfN n pc == show_cmm_n CMM_Compound = genCompoundDef mmi pc n
   | otherwise = SKIP

genAfterAtom :: MMI String String -> GrwT String String -> String -> Set String -> Exp
genAfterAtom _ _ _ EmptyS = SKIP
genAfterAtom mmi pc n (Set n2 EmptyS) 
   | n2 `elem` img (inv $ fV pc) [show_cmm_n CMM_AfterC] = genAfterC mmi pc (the $ successorsOf mmi pc n2)
   | otherwise = SKIP

genAtom :: MMI String String -> PC String String -> Id -> Exp
genAtom mmi pc n = Prfx (ExpId n) $ genAfterAtom mmi pc n (successorsOf mmi pc n)

genChoices :: MMI String String -> PC String String -> Set String -> Exp
genChoices mmi pc EmptyS = SKIP
genChoices mmi pc (Set ch chs) 
   | null chs = genAfterC mmi pc (the $ successorsOf mmi pc ch)
   | otherwise = ExtChoice (genAfterC mmi pc (the $ successorsOf mmi pc ch)) (genChoices mmi pc chs)

--genDeclsForCompounds pc m cns = (map (\cn->genCompound pc m cn) cns)
--genRelevantForAtomic pc m n cns = if (not $ null cns) 
--   then LetW (genDeclsForCompounds pc m cns) (genAtomic pc m n) 
--   else (genAtomic pc m n)

genCompoundSeqComp :: MMI String String -> PC String String -> String -> Exp
genCompoundSeqComp mmi pc n =
   let e = first $ (successorsOf mmi pc n) `intersec` (ntyNsPC (gCRSG mmi) pc CMM_AfterC) in
   let next_n = the $ successorsOf mmi pc e in
   SeqComp (ExpId n) (genAfterC mmi pc next_n) 

genCompoundDef :: MMI String String -> PC String String -> String -> Exp
genCompoundDef mmi pc n 
   | tyOfN n pc == show_cmm_n CMM_Atom = genAtom mmi pc n
   -- Either a process reference or sequential composition
   | tyOfN n pc == show_cmm_n CMM_Compound = if (show_cmm_n CMM_AfterC) `elem` (img (fV pc) (successorsOf mmi pc n)) 
      then (genCompoundSeqComp mmi pc n) else ExpId n 
   -- something combined with an operator
   | tyOfN n pc == show_cmm_n CMM_Operator && (opValOfOp (gCRSG mmi) pc n) == show_cmm_n CMM_VOpChoice = genChoices mmi pc (successorsOf mmi pc n)  
   | otherwise = SKIP -- INCOMPLETE
   

findAfterAtom :: (Foldable t, GR g, GRM gm, Eq a, Eq b) => g String a -> gm String b -> t String -> Set String
findAfterAtom pc m n = (predecessors pc n) `intersec` (ran_of $ rres (src pc) $ img (inv $ fV m) [show_cmm_n CMM_AfterC])

--genCompound pc m n = 
--   let cns = withinCompounds pc m n in
--   let buildExp e = if (not $ null $ cns) then LetW (genDeclsForCompounds pc m cns) e else e in 
--   EqDecl (ExpId n) $ buildExp (genCompoundDef pc m (findCompoundStart pc m n))

cspAtoms :: Foldable t=>t PDT -> Set Id -> Set Id
cspAtoms pdt ias = (atomsOfPDT pdt) `union` ias
   --Channel $ foldl(\ns n-> let n' = nmOfNamed pc m n in if n' `elem` ias then ns else insert n' ns) [] (getAtoms m)

--cspPImports sg_mm pc = Include $ map (\mn->mn ++ "P") (importsOf sg_mm pc)

cspImports :: Set String -> Decl
cspImports is = Include $ is

--cspMainImports :: Eq b=>PC String b -> Decl
--cspMainImports pc = Include $ set [(getPCDef pc) ++ "P", (getPCDef pc) ++ "_base"]

--isOperator (OpB OpChoice _ _) = True
--isOperator (OpB (OpParallel  _) _ _) = True
--isOperator (OpB OpInterleave _ _) = True
--isOperator(Op (OpSyncInterrupt  _) _ _) = True
--isOperator (OpB (OpThrow  _) _ _) = True
--isOperator _ = False

--cspDecl (ts@(TSeq _ _)) = snd $ cspExp ts
--cspDecl (c@(Compound n ps t)) = 
--   let (e, cds) = cspExp c in
--   [LetW cds e] 
--cspDecl (OpB _ t1 t2) = cspDecl t1 ++ cspDecl t2
cspDecl :: Foldable t => t PDT -> [Decl]
cspDecl cts = foldr (\ct scts->(snd $ cspExp  (Kappa ct)) ++ scts) [] cts

--cspDecls ts = foldr (\t ts'-> (cspDecl t)++ts') [] ts

--data BothOpt = Both (PCT->Bool) (PCT->Bool) | Fst (PCT->Bool) | Snd (PCT->Bool) | None 
data BothOpt = Both (Exp->Bool) (Exp->Bool) | Fst (Exp->Bool) | Snd (Exp->Bool) | None

cspExpsFor0 :: PT -> PT -> (Exp, Exp, [Decl])
cspExpsFor0 t1 t2 = 
    let (e1, cds1) = cspExp t1 in
    let (e2, cds2) = cspExp t2 in
    (e1, e2, cds1++cds2)

oparExp :: Exp -> (Exp -> Bool) -> Exp
oparExp e f = if f e then ExpPar e else e
calcExp1 :: Exp -> BothOpt -> Exp
calcExp1 e (Both f _) = oparExp e f
calcExp1 e (Fst f) = oparExp e f
calcExp1 e (Snd f) = e
calcExp1 e None = e
calcExp2 :: Exp -> BothOpt -> Exp
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

cspExpsFor :: PT -> PT -> BothOpt -> (Exp, Exp, [Decl])
cspExpsFor t1 t2 pfs = 
    let (e1, e2, cds) = cspExpsFor0 t1 t2 in
    (calcExp1 e1 pfs, calcExp2 e2 pfs, cds)

cspPRef ::Id->Maybe PCE->[PCE]->Rel Id Id->Exp
cspPRef n g bs rs = 
   let e1 = if null bs then ExpId n else ExpApp n (map toCSPExp bs) in
   let e2 = if null rs then e1 else ExpRen e1 (toList rs) in
   if isNil g then e2 else GExp (toCSPExp $ the g) e2 

cspPDef :: PT -> Exp
cspPDef t =
   let (e, ds) = cspExp t in
   if null ds then e else LetW ds e

--cspPDefW n t =
--   let (e, ds) = cspExp t in
--   let e1 = cspPRef (n ++ "0") [] in
--   let d = EqDecl (ExpId $ n++ "0") e in
--   if null ds then LetW [d] e1 else LetW (d:ds) e1

cspExpPrfx :: PT -> PT -> (Exp, [Decl])
cspExpPrfx t1 t2 = 
    let (e1, e2, cds) = cspExpsFor t1 t2 (Snd isComposite) in
    (Prfx e1 e2, cds)

cspExpSeq :: PT -> PT -> (Exp, [Decl])
cspExpSeq t1 t2 = 
    let (e1, e2, cds) = cspExpsFor t1 t2 (Snd isComposite) in
    (SeqComp e1 e2, cds)

consLetW :: [Decl] -> Exp -> Exp
consLetW ds (LetW ds' e) = LetW (ds++ds') e
consLetW ds e = LetW ds e


--cspExpREC :: PCT -> PCT -> (Exp, [Decl])
--cspExpREC (Atom _ og) t2 = 
--  let (e1, ds) = cspExp t2 in
--  --let e2 = ExpPar $ RExtChoice atv ats $ Prfx (ExpId atv) e1 in
--  if isNil og then (e2, ds) else (GExp (ExpId $ the og) e2, ds) 

cspExp :: PT -> (Exp, [Decl])
cspExp NilT = (SKIP, [])
cspExp StopT = (STOP, [])
cspExp SkipT = (SKIP, [])
cspExp (Atom e og) = 
    --let e = if isNil oe then ExpId a else ExpChannel a (ExpId $ the oe) in
    pairUp (if isNil og then toCSPExpA e else GExp (toCSPExp $ the og) (toCSPExpA e)) [] 
cspExp (Kappa (PDT n ps cts t))  = 
   let e1 = cspPRef n Nothing (map (cIdExp . gParamId) ps) nil
       e2 = cspPDef t
       e2' = if isSomething cts then consLetW (cspDecl cts) e2 else e2 in
   (e1, [EqDecl e1 e2'])
cspExp (OpKappa n op t)  =
   let e1 = cspPDef t in
   (rOpOf op e1, [])
   where rOpOf (OpRExtChoice v id) e1 = RExtChoice v id e1
         rOpOf (OpRIntChoice v id) e1 = RIntChoice v id e1

cspExp (Rho n g bs rs) = (cspPRef n g bs rs, [])
cspExp (OpB (OpIf g) t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 None in
   (IfExp (toCSPExp g) e1 e2, cds) 
cspExp (OpB (OpSeq o) t1 t2) = if isAtom t1 then cspExpPrfx t1 t2 else cspExpSeq t1 t2 
   -- | isAtomAny t1 && (o || t2 == NilT) = cspExpREC t1 t2 
   -- | isAtomAny t1 && not o = let (e1, ds1) = cspExpREC t1 NilT in let (e2, ds2) = cspExp t2 in (SeqComp e1 e2, ds1++ds2)
   -- | otherwise    = if isAtom t1 then cspExpPrfx t1 t2 else cspExpSeq t1 t2 
cspExp (OpB OpExtChoice t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 (Both isComposite (not . f)) in
   (ExtChoice e1 e2, cds)
   where f e = isAtomicExp e || isExtChoice e
cspExp (OpB OpIntChoice t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 (Both isComposite isComposite) in
   (IntChoice e1 e2, cds)
cspExp (OpB (OpParallel evs) t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 (Both isComposite isComposite) in
   (Parallel (map toCSPExp evs) e1 e2, cds)
--genCSPExp (Op (OpSyncInterrupt evs) t1 t2) = 
--   let (e1, e2, rts) = genExpsForOps t1 t2 in
--   let e1' = if (isOperator t1) then ExpPar e1 else e1 in
--   let e2' = if (isOperator t2) then ExpPar e2 else e2 in
--   (SyncInterrupt evs e1' e2', rts)
cspExp (OpB (OpThrow evs) t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 (Both isComposite isComposite) in
   (Throw (map toCSPExp evs) e1 e2, cds)
cspExp (OpB OpInterleave t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 (Both isComposite isComposite) in
   (Interleave e1 e2, cds)

toCSP::MMI String String->PC String String->Set String->Set String->(Set Id, CSPSpec, CSPSpec)
toCSP mmi pc ias is = 
   let (PCTD _ _ cts) = consPCTD mmi pc 
       as = cspAtoms cts ias
       is' = cspImports (fmap (++"P") ((getPCDef pc) `intoSet` is )) in
   (as, CSP [is', Channel as], CSP $ cspDecl cts)