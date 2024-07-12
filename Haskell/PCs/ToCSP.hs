
------------------
-- Project: PCs/Fragmenta
-- Module: 'PCsCSP'
-- Description: Module responsible for transforming PCTs into CSP
-- Author: Nuno Amálio
-----------------
module PCs.ToCSP(findAfterAtom, toCSP) where

import PCs.PCs
import CSP_AST
import Relations
import Sets
import Grs
import Gr_Cls
import SGrs
import CSPPrint
import PCs.PCTrees
import TheNil
import MyMaybe
import PCs.PCs_MM_Names
import GrswT
import SimpleFuns

genAfterC :: MMInfo String String -> PC String String -> String -> Exp
genAfterC mmi pc n
   | tyOfN n pc == show_cmm_n CMM_Reference = ExpId (nmOfRef pc n)
   | tyOfN n pc == show_cmm_n CMM_Atom = genAtom mmi pc n
   | tyOfN n pc == show_cmm_n CMM_Compound = genCompoundDef mmi pc n
   | otherwise = SKIP

genAfterAtom :: MMInfo String String -> GrwT String String -> String -> Set String -> Exp
genAfterAtom _ _ _ EmptyS = SKIP
genAfterAtom mmi pc n (Set n2 EmptyS) 
   | n2 `elem` img (inv $ fV pc) [show_cmm_n CMM_AfterC] = genAfterC mmi pc (the $ successorsOf mmi pc n2)
   | otherwise = SKIP

genAtom :: MMInfo String String -> PC String String -> Id -> Exp
genAtom mmi pc n = Prfx (ExpId n) $ genAfterAtom mmi pc n (successorsOf mmi pc n)

genChoices :: MMInfo String String -> PC String String -> Set String -> Exp
genChoices mmi pc EmptyS = SKIP
genChoices mmi pc (Set ch chs) 
   | null chs = genAfterC mmi pc (the $ successorsOf mmi pc ch)
   | otherwise = ExtChoice (genAfterC mmi pc (the $ successorsOf mmi pc ch)) (genChoices mmi pc chs)

--genDeclsForCompounds pc m cns = (map (\cn->genCompound pc m cn) cns)
--genRelevantForAtomic pc m n cns = if (not $ null cns) 
--   then LetW (genDeclsForCompounds pc m cns) (genAtomic pc m n) 
--   else (genAtomic pc m n)

genCompoundSeqComp :: MMInfo String String -> PC String String -> String -> Exp
genCompoundSeqComp mmi pc n =
   let e = first $ (successorsOf mmi pc n) `intersec` (pc_ns_of_nty (pc_sg_cmm mmi) pc CMM_AfterC) in
   let next_n = the $ successorsOf mmi pc e in
   SeqComp (ExpId n) (genAfterC mmi pc next_n) 

genCompoundDef :: MMInfo String String -> PC String String -> String -> Exp
genCompoundDef mmi pc n 
   | tyOfN n pc == show_cmm_n CMM_Atom = genAtom mmi pc n
   -- Either a process reference or sequential composition
   | tyOfN n pc == show_cmm_n CMM_Compound = if (show_cmm_n CMM_AfterC) `elem` (img (fV pc) (successorsOf mmi pc n)) 
      then (genCompoundSeqComp mmi pc n) else ExpId n 
   -- something combined with an operator
   | tyOfN n pc == show_cmm_n CMM_Operator && (opValOfOp (pc_sg_cmm mmi) pc n) == show_cmm_n CMM_VOpChoice = genChoices mmi pc (successorsOf mmi pc n)  
   | otherwise = SKIP -- INCOMPLETE
   

findAfterAtom pc m n = (predecessors pc n) `intersec` (ran_of $ rres (src pc) $ img (inv $ fV m) [show_cmm_n CMM_AfterC])

--genCompound pc m n = 
--   let cns = withinCompounds pc m n in
--   let buildExp e = if (not $ null $ cns) then LetW (genDeclsForCompounds pc m cns) e else e in 
--   EqDecl (ExpId n) $ buildExp (genCompoundDef pc m (findCompoundStart pc m n))

cspChannels :: Foldable t=>t CT -> Set Id -> Decl
cspChannels pct ias = Channel $ ias `union` (atomsOfPCTD pct)
   --Channel $ foldl(\ns n-> let n' = nmOfNamed pc m n in if n' `elem` ias then ns else insert n' ns) [] (getAtoms m)

--cspPImports sg_mm pc = Include $ map (\mn->mn ++ "P") (importsOf sg_mm pc)

cspImports :: Set String -> Decl
cspImports is = Include $ fmap (\mn->mn ++ "P") is

cspMainImports :: Eq b=>PC String b -> Decl
cspMainImports pc = Include $ set [(getPCDef pc) ++ "P", (getPCDef pc) ++ "_base"]

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
cspDecl :: Foldable t => t CT -> [Decl]
cspDecl cts = foldr (\ct scts->(snd $ cspExp  (Kappa ct)) ++ scts) [] cts

--cspDecls ts = foldr (\t ts'-> (cspDecl t)++ts') [] ts

--data BothOpt = Both (PCT->Bool) (PCT->Bool) | Fst (PCT->Bool) | Snd (PCT->Bool) | None 
data BothOpt = Both (Exp->Bool) (Exp->Bool) | Fst (Exp->Bool) | Snd (Exp->Bool) | None

cspExpsFor0 :: PCT -> PCT -> (Exp, Exp, [Decl])
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

cspExpsFor :: PCT -> PCT -> BothOpt -> (Exp, Exp, [Decl])
cspExpsFor t1 t2 pfs = 
    let (e1, e2, cds) = cspExpsFor0 t1 t2 in
    (calcExp1 e1 pfs, calcExp2 e2 pfs, cds)

cspPRef :: (Nil f, The f) => String -> f Id -> [Id] -> Rel Id Id -> Exp
cspPRef n g ps rs = let e1 = if null ps then ExpId n else ExpApp n ps in
   let e2 = if null rs then e1 else ExpRen e1 (toList rs) in
   if isNil g then e2 else GExp (ExpId $ the g) e2 

cspPDef :: PCT -> Exp
cspPDef t =
   let (e, ds) = cspExp t in
   if null ds then e else LetW ds e

--cspPDefW n t =
--   let (e, ds) = cspExp t in
--   let e1 = cspPRef (n ++ "0") [] in
--   let d = EqDecl (ExpId $ n++ "0") e in
--   if null ds then LetW [d] e1 else LetW (d:ds) e1

cspExpPrfx :: PCT -> PCT -> (Exp, [Decl])
cspExpPrfx t1 t2 = 
    let (e1, e2, cds) = cspExpsFor t1 t2 (Snd isComposite) in
    (Prfx e1 e2, cds)

cspExpSeq :: PCT -> PCT -> (Exp, [Decl])
cspExpSeq t1 t2 = 
    let (e1, e2, cds) = cspExpsFor t1 t2 (Snd isComposite) in
    (SeqComp e1 e2, cds)

consLetW :: [Decl] -> Exp -> Exp
consLetW ds (LetW ds' e) = LetW (ds++ds') e
consLetW ds e = LetW ds e


cspExpREC :: PCT -> PCT -> (Exp, [Decl])
cspExpREC (Atom _ og (Just (atv, ats))) t2 = 
  let (e1, ds) = cspExp t2 in
  let e2 = ExpPar $ RExtChoice atv ats $ Prfx (ExpId atv) e1 in
  if isNil og then (e2, ds) else (GExp (ExpId $ the og) e2, ds) 

cspExp :: PCT -> (Exp, [Decl])
cspExp NilT = (SKIP, [])
cspExp StopT = (STOP, [])
cspExp SkipT = (SKIP, [])
cspExp (Atom a og Nothing) = 
    let e =  ExpId a in
    pairUp (if isNil og then e else GExp (ExpId $ the og) e) [] 
cspExp (Kappa (CT n ps cts t))  = let e1 = cspPRef n Nothing ps nil in
   let e2 = cspPDef t in
   let e2' = if isSomething cts then consLetW (cspDecl cts) e2 else e2 in
   (e1, [EqDecl e1 e2'])
cspExp (Ref r g ps rs) = (cspPRef r g ps rs, [])
cspExp (OpB (OpIf g) t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 None in
   (IfExp (ExpId g) e1 e2, cds) 
cspExp (OpB (OpSeq o) t1 t2) 
    | isAtomAny t1 && (o || t2 == NilT) = cspExpREC t1 t2 
    | isAtomAny t1 && (not o) = let (e1, ds1) = cspExpREC t1 NilT in let (e2, ds2) = cspExp t2 in (SeqComp e1 e2, ds1++ds2)
    | otherwise    = if (isAtom t1) then cspExpPrfx t1 t2 else cspExpSeq t1 t2 
cspExp (OpB OpExtChoice t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 (Both isComposite (not . f)) in
   (ExtChoice e1 e2, cds)
   where f e = isAtomicExp e || isExtChoice e
cspExp (OpB OpIntChoice t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 (Both isComposite isComposite) in
   (IntChoice e1 e2, cds)
cspExp (OpB (OpParallel evs) t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 (Both isComposite isComposite) in
   (Parallel evs e1 e2, cds)
--genCSPExp (Op (OpSyncInterrupt evs) t1 t2) = 
--   let (e1, e2, rts) = genExpsForOps t1 t2 in
--   let e1' = if (isOperator t1) then ExpPar e1 else e1 in
--   let e2' = if (isOperator t2) then ExpPar e2 else e2 in
--   (SyncInterrupt evs e1' e2', rts)
cspExp (OpB (OpThrow evs) t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 (Both isComposite isComposite) in
   (Throw evs e1 e2, cds)
cspExp (OpB OpInterleave t1 t2) = 
   let (e1, e2, cds) = cspExpsFor t1 t2 (Both isComposite isComposite) in
   (Interleave e1 e2, cds)

toCSP::MMInfo String String->PC String String->Set String->Set String->(CSPSpec, CSPSpec, CSPSpec)
toCSP mmi pc ias is = 
   let (PCTD _ cts) = consPCTD mmi pc in
   (CSP [cspChannels cts ias], CSP $ cspDecl cts, CSP $ [cspMainImports pc] ++ [cspImports is])