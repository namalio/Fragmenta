-----------------------
-- Project: PCs/Fragmenta
-- Module: PCTrees
-- Description: Handles representation of PCs as PCTs, a recursive datatype representation of abstract syntax
-- Author: Nuno Amálio
-----------------------
module PCs.PCTrees(PT(..)
  , TOp(..)
  , PDT(..)
  , PCTD(..)
  , withinRel
  , consPCTD
  , atomsOfPDT
  , atomsOfPCTs
  , show_pctd
  , isOperator
  , isAtom
  , isSole
  , seqCTs)
  where

import PCs.PCs
import Gr_Cls
import Grs
import GrswT
import Sets
import Relations
import TheNil
import MyMaybe
import PCs.PCs_MM_Names
import ShowUtils
import ParseUtils
import PCs.PCTrees_AST
import MMI
import SimpleFuns (butLast, pairUp)
import PCs.PCsCommon(Id)
import PCs.PCTrees_Exp
import PCs.ParsingPCTxtExp

opseqC :: TOp
opseqC = OpSeq False
opseqO :: TOp
opseqO = OpSeq True

rearrangeT :: PT -> PD
rearrangeT (OpB opseqC (Kappa (PDT k ps cts t1)) t2) = PDT k ps nil (OpB opseqC (Kappa (PDT (k++"0") nil cts t1)) t2)
rearrangeT (Kappa pdt) = pdt

show_top :: TOp -> String
show_top OpExtChoice = "◻︎"
show_top OpIntChoice = "⊓"
show_top (OpSeq o) = (if o then "O" else "") ++  "⇥"
show_top (OpParallel ps) = "∥" ++ (show ps)
show_top (OpInterleave) = "⦀"
show_top (OpThrow ps) = "𝛩" ++ (show ps)
show_top (OpIf g) = "𝜄" ++ (show g)

show_pdts :: Foldable t => t PDT -> String
show_pdts pdts = if null pdts then "" else "{" ++ foldr (\ct scts->(show_pt $ Kappa ct) ++ "∙" ++  scts) "" pdts ++ "}"

show_params :: (Foldable t, Functor t) => t Param -> String
show_params ps = 
  if null ps then "" else "(" ++ (showStrs (fmap show ps) ",") ++ ")"

--show_binding :: Foldable t => (t String) -> String
--show_binding bs = if null bs then "" else "(" ++ (showStrs bs ",") ++ ")"

showPCExps::(Foldable t, Functor t) => t PCE -> String
showPCExps es = if null es then "" else "(" ++ showStrs (fmap show es) "," ++ ")"

--show_bindings :: Foldable t => (t PCExp) -> String
--show_bindings bss = if null bss then "" else "(" ++ showStrs bss "," ++ ")"

--if null bss then "" else "(" ++ foldr (\bs s-> (show_binding bs) ++ s) nil bss ++ ")"

show_renamings :: Foldable t => t (String, String) -> String
show_renamings rs = if null rs then "" else "⟦" ++ (showStrs (foldr (\(fr, to) rps->(fr ++ "/" ++ to):rps) [] rs) ",") ++ "⟧"

show_guard :: Maybe PCE -> String
show_guard oe = if isNil oe then "" else " {" ++ (show $ the oe) ++ "}"
--show_atparams :: (Nil f, The f) => f (String, String) -> String
--show_atparams op = if isNil op then "" else " (" ++ (fst . the $ op) ++ "," ++ (snd . the $ op) ++ ")"

--show_atomTExp::Maybe String->String
--show_atomTExp Nothing = ""
--show_atomTExp (Just e) = "." ++ e

show_bop0::String->String->String
show_bop0 id e = id ++ ":" ++ e 

show_bop::ROp->String
show_bop (OpRExtChoice v id) = "◻︎" ++ (show_bop0 v id)
show_bop (OpRIntChoice v id) = "⊓" ++ (show_bop0 v id)

--show_ref::Ref->String
--show_ref (Ref id og es rs) = "𝜌" ++ id ++ (showPCExps es) ++ (show_renamings rs) ++ (show_guard og)

show_pt :: PT -> String
show_pt (Atom e og) = "𝛼" ++ show e ++ (show_guard og)
show_pt (Kappa (PDT id ps pdts pct)) = "𝜅 " ++ id ++ (show_params ps) ++ (show_pdts pdts)++ " @ " ++ (show_pt pct)
show_pt (OpKappa id bop pct) = "𝛾𝜅 " ++ id ++ (show_bop bop) ++ " @ " ++ (show_pt pct)
show_pt (OpB op pct1 pct2) = "[𝛾 " ++ show_top op ++ "]" ++ (show_pt pct1) ++ " [" ++ (show_pt pct2) ++ "]"
show_pt (Rho id og es rs) = "𝜌" ++ id ++ (showPCExps es) ++ (show_renamings rs) ++ (show_guard og)
show_pt NilT = "𝜑"
show_pt StopT = "𝛉"
show_pt SkipT = "𝜉"

show_pctd :: PCTD -> String
show_pctd (PCTD id ds pts) = "PC " ++ id ++ (show_pdts pts)

andThenO :: (Eq a1, Eq a2) => (PT, Set a1, Set a2) -> (PT, Set a1, Set a2) -> (PT, Set a1, Set a2)
andThenO (t, rs, gcs) (t', rs', gcs') = (OpB opseqO t t', rs `union` rs', gcs `union` gcs')
andThenC :: (Eq a1, Eq a2) => (PT, Set a1, Set a2) -> (PT, Set a1, Set a2) -> (PT, Set a1, Set a2)
andThenC (t, rs, gcs) (t', rs', gcs') = (OpB opseqC t t', rs `union` rs', gcs `union` gcs')

undThen :: (Eq a1, Eq a2) => (PT, Set a1, Set a2) -> (PT, Set a1, Set a2) -> (PT, Set a1, Set a2)
undThen (t, rs, gcs) (t', rs', gcs') = if t' == NilT then (t, rs, gcs) else (t, rs, gcs) `andThenC` (t', rs', gcs')

withOp :: (Eq a1, Eq a2) => (PT, Set a1, Set a2) -> (TOp, (PT, Set a1, Set a2)) -> (PT, Set a1, Set a2)
withOp (t, rs, gcs) (op, (t', rs', gcs')) = if t' == NilT then (t, rs, gcs) else (OpB op t t', rs `union` rs', gcs `union` gcs')

toTOp :: The f => PCs_CMM_Ns -> f PCE -> [PCE] -> TOp
toTOp CMM_VOpChoice _ _= OpExtChoice
toTOp CMM_VOpIntChoice _ _= OpIntChoice
toTOp CMM_VOpParallel _ bs = OpParallel bs
toTOp CMM_VOpInterleave _ _ = OpInterleave
toTOp CMM_VOpThrow _ ps = OpThrow ps
toTOp CMM_VOpIf og _ = OpIf (the og)

--fillAnyExp :: Maybe (String, Either String [String]) -> Maybe (Id, PCExp)
--fillAnyExp Nothing = Nothing
--fillAnyExp (Just (v, b)) = let v' = if null v then "e" else butLast v in 
--  Just (v', strOfBinding b)

atLeaf::PC String String->Id->(PT, Set Id, Set Id)
atLeaf pc n = 
    let oe = parsePCExpAtom . toStr $ expOfAtom pc n
        og = parsePCExp . str_of_ostr $ guardOf pc n in
    if isSomething oe then (Atom (the oe) og, nil, nil) else (Atom (IdExp n) og, nil, nil)
    where toStr Nothing = ""
          toStr (Just s) = butLast . tail $ s

--atPLeaf::PC String String->Id->(PCT, Set Id, Set Id)
--atPLeaf pc n = (Atom (strOfBinding $ expBOfAtomPack pc n) Nothing, nil, nil)

openACOf :: MMI String String -> GrwT String String -> String -> Bool
openACOf mmi pc n = 
  let ac = nextAfterC mmi pc n in
  isSomething ac && openAC pc (the ac)

atomBranch::MMI String String->PC String String->Rel Id Id->Id->Set Id->(PT, Set Id, Set Id)
atomBranch mmi pc r n gcs = 
    let t1 = atLeaf pc n 
        t2 = consOptBranch mmi pc r (nextNodeAfter mmi pc n) gcs in
    if openACOf mmi pc n then t1 `andThenO` t2 else t1 `andThenC` t2

--atomPBranch::MMI String String->PC String String->Rel Id Id->Id->Set Id->(PCT, Set Id, Set Id)
--atomPBranch mmi pc r n gcs = 
--    let t1 = atPLeaf pc n 
--        t2 = consOptBranch mmi pc r (nextNodeAfter mmi pc n) gcs in
--    if openACOf mmi pc n then t1 `andThenO` t2 else t1 `andThenC` t2

--startOf::MMI String String->PC String String->Id->Id
--startOf mmi pc n 
--   | isNodeOfTys n [CMM_AtomPack] (gCRSG mmi) pc = n ++ "_Op"
--   | otherwise = compoundStart mmi pc n

bOpOf::String->String->String->ROp
bOpOf op v e = opOf op v e
  where opOf "VOpChoice" = OpRExtChoice
        opOf "VOpIntChoice" = OpRIntChoice

compoundBoundedOp::MMI String String->PC String String->Rel Id Id->Id->Set Id->(PT, Set Id, Set Id)
compoundBoundedOp mmi pc r n gcs =
  let (t, rs, gcs2) = consBranch mmi pc r (quantifiedOpStart mmi pc n) (gunion [singles n, gcs]) 
      sg_mm = gCRSG mmi 
      (v, e) = varBQuantifiedOp pc n in 
  (OpKappa  n (bOpOf (opQuantifiedOp sg_mm  pc n) (butLast v) (strOfTxtExp e)) t, rs, gunion [singles n, gcs, gcs2])

compound::MMI String String->PC String String->Rel Id Id->Id->Set Id->(PT, Set Id, Set Id)
compound mmi pc r n gcs = 
  let ns = img r [n] `intersec` img ( trancl $ r `rcomp`  r) [n]
      (pts, rs1, gcs1) = seqCTs mmi pc r (ns `union` innerRefKs mmi pc n) (n `intoSet` gcs) 
      --(cts, rs1, gcs1) = seqCTs mmi pc ((innerRefKs mmi pc n) `union` (commonInnerKs mmi pc n)) (n `intoSet` gcs) 
      (t, rs2, gcs2) = consBranch mmi pc r (compoundStart mmi pc n) (gunion [singles n, gcs, gcs1]) in
  (Kappa  $ PDT n (fmap (\(id, t)->cParam id (read_opctty t)) $ paramsOf pc n) pts t, rs1 `union` rs2, gunion [singles n, gcs1, gcs2])

compoundAB::MMI String String->PC String String->Rel Id Id->Id->Set Id->(PT, Set Id, Set Id)
compoundAB mmi pc r n gcs = 
  (compound mmi pc r n gcs) `undThen` (consOptBranch mmi pc r (nextNodeAfter mmi pc n) (n `intoSet` gcs))

--   let on = nextNodeAfter mmi pc n in
--   let (t1, rs) = consCompound mmi pc n gcs in
--   let combine (t2, rs', z) = (OpB OpSeq t1 t2, rs++rs', [n, the on] `union` z) in
--   if isSomething on then combine $ consBranch mmi pc (the on) Nothing (n:gcs) else (t1, rs, [n])

--consCompoundOrAtom::MMInfo String->PC String->Id->Guard->[Id]->(PCT, [Id], [Id])
--consCompoundOrAtom mmi pc n g gcs 
--    | isNodeOfTy n CMM_Atom (pc_sg_cmm mmi) pc = atomLeaf pc n g
--    | isNodeOfTy n CMM_Compound (pc_sg_cmm mmi) pc = consCompound mmi pc n gcs

--consCompoundOrAtomBranch::MMInfo String->PC String->Id->Guard->[Id]->(PCT, [Id], [Id])
--consCompoundOrAtomBranch mmi pc n g gcs = 
--    (consCompoundOrAtom mmi pc n g gcs) `andThen` (consOptBranch mmi pc (nextNodeAfter mmi pc n) Nothing gcs)

consRefOrcompound::MMI String String->PC String String->Rel Id Id->Id->Set Id->(PT, Set Id, Set Id)
consRefOrcompound mmi pc r n gcs 
    | n `elem` gcs = (Rho n Nothing nil nil, nil, nil)
    | isNodeOfTys n [CMM_QuantifiedOp] (gCRSG mmi) pc = compoundBoundedOp mmi pc r n gcs
    | otherwise = compoundAB mmi pc r n gcs

refLeaf :: Foldable t => MMI String String -> GrwT String String -> String -> t String -> (PT, Set Id, Set a)
refLeaf mmi pc n gcs = 
  let rn = nmOfRefF mmi pc n 
      rs = if rn `elem` gcs || not (isNodeOfTys rn [CMM_Compound] (gCRSG mmi) pc) then nil else singles rn in
  (Rho rn (parsePCExp . str_of_ostr $ guardOf pc n) (fmap (the . parsePCExp) (strOfTxtExps $ expsOfRef mmi pc n)) (renamingsOf pc n), rs , nil)

refBranch :: MMI String String -> GrwT String String -> Rel Id Id->Id -> Set Id -> (PT, Set Id, Set Id)
refBranch mmi pc r n gcs =
    --let ir = inner_Ref pc n in
    --let rn = nmOfRefF mmi pc n in -- Work here
    --if ir && (not $ rn `elem` gcs) then compoundAB mmi pc rn gcs else 
    (refLeaf mmi pc n gcs) `undThen` consOptBranch mmi pc r (nextNodeAfter mmi pc n) gcs
    --here combine rs (t, rs', gcs) = (t, rs `union` rs', gcs)
   --if isNil after then (t, rs, []) else combine rs $ generateOpTreeFor mmi pc t [the after] rs gcs

--opBGuard::MMInfo String->PC String->Id->Maybe Guard
--opBGuard mmi pc n = 
--  let cs = (successorsOf mmi pc n) `intersec` (img (inv $ fV pc) [show_cmm_n CMM_BranchC]) in
--  if isNil cs then Nothing else predMaybe (not . null) $ guardOf pc (the cs)

opTree::MMI String String->PC String String->Rel Id Id->Id->Set Id->(PT, Set Id, Set Id)
opTree mmi pc r n gcs = 
   let og = parsePCExp . str_of_ostr $ guardOfOp mmi pc n 
       es = fmap (the . parsePCExp) (strOfTxtExps $ expsOf pc n) in
   opBranches mmi pc r (toTOp (read_cmm $ opValOfOp (gCRSG mmi) pc n) og es) (branchesOfOp mmi pc n) gcs
-- let (tcs, rs, cs) = consOpBranches mmi pc (read_cmm $ opValOfOp (pc_sg_cmm mmi) pc n) (bs++bs'++bs'') gcs
--generatePCTsForBranches mmi pc (bs++bs'++bs'') gcs in
--(consOpTreeLs tcs (toTreeOp (read_cmm $ opValOfOp (pc_sg_cmm mmi) pc n) g (paramsOf pc n)), rs, cs)


--rOpTree::MMI String String->PC String String->Rel Id Id->Id->Set Id->(PCT, Set Id, Set Id)
--rOpTree mmi pc r n gcs = 
--  let (x, b) = varQuantifiedOp pc n 
--      toRTOp CMM_VOpChoice = OpRExtChoice (butLast x) (strOfBinding b)
--      toRTOp CMM_VOpIntChoice = OpRIntChoice (butLast x) (strOfBinding b) in
--  rOpAtom mmi pc r n (toRTOp . read_cmm $ opQuantifiedOp (gCRSG mmi) pc n) nil


--rOpAtom::MMI String String->PC String String->Rel Id Id->Id->TOp->Set Id->(PCT, Set Id, Set Id)
--rOpAtom mmi pc r n op cs = 
--  let n' = n ++ "_Atom" 
--      (tc, rs, cs') = consBranch mmi pc r n' cs in
--  (OpB op tc NilT, rs, cs' `union` cs)
  

consOptBranch::MMI String String->PC String String->Rel Id Id->Maybe Id->Set Id->(PT, Set Id, Set Id)
consOptBranch mmi pc r on gcs
   | isNil on = (NilT, nil, nil) 
   | otherwise = consBranch mmi pc r (the on) gcs

consBranch::MMI String String->PC String String->Rel Id Id->Id->Set Id->(PT, Set Id, Set Id)
consBranch mmi pc r n gcs 
    | isNodeOfTys n [CMM_Atom] (gCRSG mmi) pc = atomBranch mmi pc r n gcs
    | isNodeOfTys n [CMM_Compound] (gCRSG mmi) pc = consRefOrcompound mmi pc r n gcs
    | isNodeOfTys n [CMM_Reference] (gCRSG mmi) pc = refBranch mmi pc r n gcs
    | isNodeOfTys n [CMM_Combination] (gCRSG mmi) pc = opTree mmi pc r n gcs 
    | isNodeOfTys n [CMM_Stop] (gCRSG mmi) pc = (StopT, nil, nil)
    | isNodeOfTys n [CMM_Skip] (gCRSG mmi) pc = (SkipT, nil, nil)
    | isNodeOfTys n [CMM_QuantifiedOp] (gCRSG mmi) pc = consRefOrcompound mmi pc r n gcs
    -- | not . null $ nOp n = rOpTree mmi pc r (nOp n) gcs
    -- | not . null $ nAtom n  = atomPBranch mmi pc r (nAtom n) gcs
    -- where nOp n = fst $ splitAtStr "_Op" n
    --      nAtom n = fst $ splitAtStr "_Atom" n


opBranches::MMI String String->PC String String->Rel Id Id->TOp->Set Id->Set Id->(PT, Set Id, Set Id)
opBranches _ _ _ _ EmptyS _ = (NilT, nil, nil)
opBranches mmi pc r op (Set b bs) cs = 
   let n = the $ nextNode mmi pc b
       (tc, rs, cs') = consBranch mmi pc r n cs in
   --let combine (tc, rs, cs) (tcs, rs', cs') = (tc:tcs, rs++rs', cs++cs') in
   (tc, rs, cs') `withOp`  (op, opBranches mmi pc r op bs $ cs' `union` cs)

--followedBy t ts = if t' == NilT then t else TSeq t t'
seqCTs::MMI String String->PC String String->Rel Id Id->Set Id->Set Id->([PDT], Set Id, Set Id)
seqCTs _ _ _ EmptyS gks = (nil, nil, gks)
seqCTs mmi pc r (Set n ns) gks = 
    let (t, rns1, gks1)  = compoundAB mmi pc r n gks in
    let (pdts, rns2, gks2) = seqCTs mmi pc r ((ns `union` rns1) `sminus` gks1) (gks `union` gks1) in 
    (rearrangeT t:pdts, gunion [ns, rns1, rns2], gunion [gks, gks1, gks2])
--where modify_t (OpB opseqC (Kappa (CT k ps cts t1)) t2) = CT k ps [] (OpB opseqC (Kappa (CT (k++"0") [] cts t1)) t2)

consDef::PC String String->String->DTDef
consDef pc n = DTDef n $ enumValsOf pc n

consPCTD::MMI String String->PC String String->PCTD
consPCTD mmi pc = 
  let r = relKs mmi pc
      ds = foldr (\d ds'->consDef pc d:ds') [] (ntyNsPC (gCRSG mmi) pc CMM_Definition)
      (pdts, _, _) = seqCTs mmi pc r (singles $ startCompound mmi pc) nil in 
  PCTD (getPCDef pc) ds pdts

-- Need to make more general here in the future
revname :: PCEAtom -> Id -> Id -> PCEAtom
revname e@(IdExp id) k p = if id == k then IdExp p else e
revname e@(DotExp id e') k p = if id == k then DotExp p e' else e
revname e _ _ = e


rename :: PT -> Id -> Id -> PT
rename (Atom e og) k p = Atom (revname e k p) og
rename (OpB op t1 t2) k p = OpB op (rename t1 k p) (rename t2 k p)
rename (Kappa (PDT nm ps cts t)) k p = 
  Kappa (PDT nm ps (map thePDT $ foldr (\t' ts->(rename t' k p):ts) [] (fmap Kappa cts)) (rename t k p))
rename pct _ _ = pct
--rename NilT _ _ = NilT
--rename StopT _ _ = StopT
--rename SkipT _ _ = SkipT

within :: PT -> Set Id
within (Atom e _) = atomsOfPCExpA e
within (OpB _ t1 t2) = (within t1) `union` (within t2)
within (Kappa (PDT nm _ cts t)) = (foldr (\ct wcts->(within $ Kappa ct) `union` wcts) nil cts) `union` (singles nm) `union` (within t)
within (Rho _ _ _ _) = nil
within NilT = nil
within StopT = nil
within SkipT = nil

relWithinRel_pdts :: [PDT] -> Rel Id Id
relWithinRel_pdts = foldr (\pdt rct->(relWithin $ Kappa pdt) `union` rct) nil

relWithinRel :: Id -> PT -> Rel Id Id
relWithinRel nc (Atom e _) = foldr (\a r-> pairUp nc a `intoSet` r) nil (atomsOfPCExpA e)
relWithinRel nc (OpB _ t1 t2) =  (relWithinRel nc t1) `union` (relWithinRel nc t2)
relWithinRel nc (Kappa (PDT nm _ pdts t)) = singles (nc, nm) `union` (relWithinRel_pdts pdts) `union` (relWithin t)
relWithinRel _ (Rho _ _ _ _) = nil
relWithinRel _ NilT = nil
relWithinRel _ StopT = nil
relWithinRel _ SkipT = nil

relWithin :: PT -> Rel Id Id
relWithin (Kappa (PDT nm _ pdts t)) = (relWithinRel_pdts pdts) `union` relWithinRel nm t
--relWithin (TSeq t1 t2) = relWithin t1 ++ relWithin t2
relWithin _ = nil

atomsPCTD :: PCTD ->Set Id
atomsPCTD (PCTD _ _ pdts) = atomsOfPDT pdts

--unionp::(Eq a, Eq b)=>(Set a, Set b)->(Set a, Set b)->(Set a, Set b)
--unionp (sx1, sy1) (sx2, sy2) = (sx1 `union` sx2, sy1 `union` sy2)

--nilp :: (Set a1, Set a2)
--nilp = (EmptyS, EmptyS)

atomsOfPDT :: Foldable t=>t PDT ->Set Id
atomsOfPDT = 
  foldr (\ct p_as_rs ->atomsOfPCT (Kappa ct) `union` p_as_rs) nil

atomsOfPCTs :: PT -> PT ->Set Id
atomsOfPCTs t1 t2 = atomsOfPCT t1 `union` atomsOfPCT t2

atomsOfPCExpA::PCEAtom->Set Id
atomsOfPCExpA (IdExp id) = singles id
atomsOfPCExpA (DotExp id _) = singles id

atomsOfPCExp::PCE->Set Id
atomsOfPCExp (ExpAtom ea) = atomsOfPCExpA ea
atomsOfPCExp _ = nil

--atomsOfRef :: Ref ->Set Id
--atomsOfRef (Ref _ _ _ rs) = foldr (\(_, to) ps->(singles to) `union` ps) nil rs

atomsOfPCT :: PT ->Set Id
atomsOfPCT (Atom e _) = atomsOfPCExpA e
--atomsOfPCT (Atom _ _ (Just (_, ats))) = 
--  if head ats == '{' && last ats == '}' then set $ words' (== ',') (drop 1 (take ((length ats) - 1) ats)) else nil
atomsOfPCT (OpB (OpThrow as) t1 t2) = gunion (fmap atomsOfPCExp as) `union` atomsOfPCTs t1 t2
atomsOfPCT (OpB _ t1 t2) = atomsOfPCTs t1 t2
atomsOfPCT (Kappa (PDT _ _ cts t)) = foldr (\ct ps->(atomsOfPCT $ Kappa ct) `union` ps) nil cts `union` (atomsOfPCT t)
atomsOfPCT (Rho _ _ _ rs) = foldr (\(_, to) ps->(singles to) `union` ps) nil rs
atomsOfPCT NilT = nil
--atomsOfPCT (TSeq t1 t2) = (atomsOfPCT t1) `union` (atomsOfPCT t2)
atomsOfPCT  StopT = nil
atomsOfPCT  SkipT = nil

isOperator :: PT -> Bool
isOperator (OpB _ _ _) = True
isOperator _ = False

isAtomic :: PT -> Bool
isAtomic (Atom _ _) = True
isAtomic (Kappa _) = True
isAtomic (NilT) = True
isAtomic (StopT) = True
isAtomic (SkipT) = True
isAtomic (Rho _ _ _ _) = True
isAtomic (OpB (OpSeq _) t NilT) = isAtom t
isAtomic _ = False

isSole :: PT -> Bool
isSole (Atom _ _) = True
isSole (Kappa _) = True
isSole (OpB _ t1 _) = isAtomic t1 
isSole (NilT) = True
isSole (StopT) = True
isSole (SkipT) = True
isSole (Rho _ _ _ _) = True


--isAtomAny :: PCT -> Bool
--isAtomAny (Atom _ _) = isSomething as
--isAtomAny _ = False

isAtom :: PT -> Bool
isAtom (Atom _ _) = True
isAtom _ = False

