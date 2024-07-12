-----------------------
-- Project: PCs/Fragmenta
-- Module: PCTrees
-- Description: Handles representation of PCs as PCTs, a recursive datatype representation of abstract syntax
-- Author: Nuno Amálio
-----------------------
module PCs.PCTrees(PCT(..), TOp(..), CT(..), PCTD(..), withinRel, consPCTD, atomsOfPCTD, 
  show_pctd, isOperator, isAtom, isAtomAny, isAtomic
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

type Id = String 
type PCExp = String 
type Guard = String
type Param = String 

data TOp = OpExtChoice | OpIntChoice | OpSeq Bool | OpParallel [Param] | OpInterleave | OpThrow [Param]
  | OpIf Guard deriving(Eq, Show)  
data PCT = Atom Id (Maybe Guard) (Maybe (Id, PCExp)) | OpB TOp PCT PCT 
  | Kappa CT 
  | Ref Id (Maybe Guard) [Param] (Rel Id Id)
  | NilT | StopT | SkipT deriving(Eq, Show)
data CT = CT Id [Param] [CT] PCT 
  deriving(Eq, Show)

data PCTD = PCTD Id [CT] 
  deriving(Eq, Show)

theCt :: PCT -> CT
theCt (Kappa ct) = ct 

opseqC :: TOp
opseqC = OpSeq False
opseqO :: TOp
opseqO = OpSeq True

rearrangeT :: PCT -> CT
rearrangeT (OpB opseqC (Kappa (CT k ps cts t1)) t2) = CT k ps nil (OpB opseqC (Kappa (CT (k++"0") nil cts t1)) t2)
rearrangeT (Kappa ct) = ct

show_top :: TOp -> String
show_top OpExtChoice = "◻︎"
show_top OpIntChoice = "⊓"
show_top (OpSeq o) = (if o then "O" else "") ++  "⇥"
show_top (OpParallel ps) = "∥" ++ (show ps)
show_top (OpInterleave) = "⦀"
show_top (OpThrow ps) = "𝛩" ++ (show ps)
show_top (OpIf g) = "𝜄" ++ (show g)

show_cts :: Foldable t => t CT -> String
show_cts cts = if null cts then "" else "{" ++ foldr (\ct scts->(show_pct $ Kappa ct) ++ "∙" ++  scts) "" cts ++ "}"
show_params :: Foldable t => t String -> String
show_params ps = if null ps then "" else "(" ++ (showStrs ps ",") ++ ")"
show_renamings :: Foldable t => t (String, String) -> String
show_renamings rs = if null rs then "" else "⟦" ++ (showStrs (foldr (\(fr, to) rps->(fr ++ "/" ++ to):rps) [] rs) ",") ++ "⟧"
show_guard :: Maybe String -> String
show_guard og = if isNil og then "" else " {" ++ (str_of_ostr og) ++ "}"
show_atparams :: (Nil f, The f) => f (String, String) -> String
show_atparams op = if isNil op then "" else " (" ++ (fst . the $ op) ++ "," ++ (snd . the $ op) ++ ")"
show_pct :: PCT -> String
show_pct (Atom id og op) = "𝛼" ++ id ++ (show_atparams op) ++ (show_guard og)
show_pct (Kappa (CT id ps cts pct)) = "𝜅 " ++ id ++ (show_params ps) ++ (show_cts cts)++ " @ " ++ (show_pct pct)
show_pct (OpB op pct1 pct2) = "[𝛾 " ++ show_top op ++ "]" ++ (show_pct pct1) ++ " [" ++ (show_pct pct2) ++ "]"
show_pct (Ref id og ps rs) = "𝜌" ++ id ++ (show_params ps) ++ (show_renamings rs) ++ (show_guard og)
show_pct (NilT) = "𝜑"
show_pct (StopT) = "𝛉"
show_pct (SkipT) = "𝜉"

show_pctd :: PCTD -> String
show_pctd (PCTD id cts) = "PC " ++ id ++ (show_cts cts)

andThenO :: (Eq a1, Eq a2) => (PCT, Set a1, Set a2) -> (PCT, Set a1, Set a2) -> (PCT, Set a1, Set a2)
andThenO (t, rs, gcs) (t', rs', gcs') = (OpB opseqO t t', rs `union` rs', gcs `union` gcs')
andThenC :: (Eq a1, Eq a2) => (PCT, Set a1, Set a2) -> (PCT, Set a1, Set a2) -> (PCT, Set a1, Set a2)
andThenC (t, rs, gcs) (t', rs', gcs') = (OpB opseqC t t', rs `union` rs', gcs `union` gcs')

undThen :: (Eq a1, Eq a2) => (PCT, Set a1, Set a2) -> (PCT, Set a1, Set a2) -> (PCT, Set a1, Set a2)
undThen (t, rs, gcs) (t', rs', gcs') = if t' == NilT then (t, rs, gcs) else (t, rs, gcs) `andThenC` (t', rs', gcs')

withOp :: (Eq a1, Eq a2) => (PCT, Set a1, Set a2) -> (TOp, (PCT, Set a1, Set a2)) -> (PCT, Set a1, Set a2)
withOp (t, rs, gcs) (op, (t', rs', gcs')) = if t' == NilT then (t, rs, gcs) else (OpB op t t', rs `union` rs', gcs `union` gcs')

toTOp :: The f => PCs_CMM_Ns -> f Guard -> [Param] -> TOp
toTOp CMM_VOpChoice _ _= OpExtChoice
toTOp CMM_VOpIntChoice _ _= OpIntChoice
toTOp CMM_VOpParallel _ ps = OpParallel ps
--toTreeOp CMM_OpWaitFor _ _= OpWaitFor
toTOp CMM_VOpInterleave _ _ = OpInterleave
--toTreeOp CMM_OpSyncInterrupt _ ps = OpSyncInterrupt ps
toTOp CMM_VOpThrow _ ps = OpThrow ps
toTOp CMM_VOpIf og _ = OpIf (the og)

fillAnyExp :: Maybe (String, b) -> Maybe (String, b)
fillAnyExp (Just ("", ats)) = Just ("e", ats)
fillAnyExp p = p

atLeaf::PC String String->Id->(PCT, Set Id, Set Id)
atLeaf pc n = (Atom (nmOfNamed pc n) (guardOf pc n) (fillAnyExp $ anyExpOfAt pc n), nil, nil)

openACOf :: MMInfo String String -> GrwT String String -> String -> Bool
openACOf mmi pc n = 
  let ac = nextAfterC mmi pc n in
  isSomething ac && openAC pc (the ac)

atomBranch::MMInfo String String->PC String String->Rel Id Id->Id->Set Id->(PCT, Set Id, Set Id)
atomBranch mmi pc r n gcs = 
    let t1 = atLeaf pc n in
    let t2 = consOptBranch mmi pc r (nextNodeAfter mmi pc n) gcs in
    if openACOf mmi pc n then t1 `andThenO` t2 else t1 `andThenC` t2
    
compound::MMInfo String String->PC String String->Rel Id Id->Id->Set Id->(PCT, Set Id, Set Id)
compound mmi pc r n gcs = 
  let ns = img r [n] `intersec` img ( trancl $ r `rcomp`  r) [n]
      (cts, rs1, gcs1) = seqCTs mmi pc r (ns `union` innerRefKs mmi pc n) (n `intoSet` gcs) 
      --(cts, rs1, gcs1) = seqCTs mmi pc ((innerRefKs mmi pc n) `union` (commonInnerKs mmi pc n)) (n `intoSet` gcs) 
      (t, rs2, gcs2) = consBranch mmi pc r (compoundStart mmi pc n) (gunion [singles n, gcs, gcs1]) in
  (Kappa  $ CT n (paramsOf pc n) cts t, rs1 `union` rs2, gunion [singles n, gcs1, gcs2])

compoundAB::MMInfo String String->PC String String->Rel Id Id->Id->Set Id->(PCT, Set Id, Set Id)
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

consRefOrcompound::MMInfo String String->PC String String->Rel Id Id->Id->Set Id->(PCT, Set Id, Set Id)
consRefOrcompound mmi pc r n gcs 
    | n `elem` gcs = (Ref n Nothing nil nil, nil, nil)
    | otherwise = compoundAB mmi pc r n gcs

refLeaf :: Foldable t => MMInfo String String -> GrwT String String -> String -> t String -> (PCT, Set Id, Set a)
refLeaf mmi pc n gcs = 
  let rn = nmOfRefF mmi pc n in 
  let rs = if rn `elem` gcs || not (isNodeOfTys rn [CMM_Compound] (pc_sg_cmm mmi) pc) then nil else singles rn in
  (Ref rn (guardOf pc n) (paramsOfRef mmi pc n) (renamingsOf pc n), rs , nil)

refBranch :: MMInfo String String -> GrwT String String -> Rel Id Id->Id -> Set Id -> (PCT, Set Id, Set Id)
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

opTree::MMInfo String String->PC String String->Rel Id Id->Id->Set Id->(PCT, Set Id, Set Id)
opTree mmi pc r n gcs = 
   opBranches mmi pc r (toTOp (read_cmm $ opValOfOp (pc_sg_cmm mmi) pc n) (guardOfOp mmi pc n) (paramsOf pc n)) (branchesOfOp mmi pc n) gcs
-- let (tcs, rs, cs) = consOpBranches mmi pc (read_cmm $ opValOfOp (pc_sg_cmm mmi) pc n) (bs++bs'++bs'') gcs
--generatePCTsForBranches mmi pc (bs++bs'++bs'') gcs in
--(consOpTreeLs tcs (toTreeOp (read_cmm $ opValOfOp (pc_sg_cmm mmi) pc n) g (paramsOf pc n)), rs, cs)

consOptBranch::MMInfo String String->PC String String->Rel Id Id->Maybe Id->Set Id->(PCT, Set Id, Set Id)
consOptBranch mmi pc r on gcs
   | isNil on = (NilT, nil, nil) 
   | otherwise = consBranch mmi pc r (the on) gcs

consBranch::MMInfo String String->PC String String->Rel Id Id->Id->Set Id->(PCT, Set Id, Set Id)
consBranch mmi pc r n gcs 
    | isNodeOfTys n [CMM_Atom] (pc_sg_cmm mmi) pc = atomBranch mmi pc r n gcs
    | isNodeOfTys n [CMM_Compound] (pc_sg_cmm mmi) pc = consRefOrcompound mmi pc r n gcs
    | isNodeOfTys n [CMM_Reference] (pc_sg_cmm mmi) pc = refBranch mmi pc r n gcs
    | isNodeOfTys n [CMM_Combination] (pc_sg_cmm mmi) pc = opTree mmi pc r n gcs 
    | isNodeOfTys n [CMM_Stop] (pc_sg_cmm mmi) pc = (StopT, nil, nil)
    | isNodeOfTys n [CMM_Skip] (pc_sg_cmm mmi) pc = (SkipT, nil, nil)


opBranches::MMInfo String String->PC String String->Rel Id Id->TOp->Set Id->Set Id->(PCT, Set Id, Set Id)
opBranches _ _ _ _ EmptyS _ = (NilT, nil, nil)
opBranches mmi pc r op (Set b bs) cs = 
   let n = the $ nextNode mmi pc b in
   let (tc, rs, cs') = consBranch mmi pc r n cs in
   --let combine (tc, rs, cs) (tcs, rs', cs') = (tc:tcs, rs++rs', cs++cs') in
   (tc, rs, cs') `withOp`  (op, opBranches mmi pc r op bs $ cs' `union` cs)

--followedBy t ts = if t' == NilT then t else TSeq t t'
seqCTs::MMInfo String String->PC String String->Rel Id Id->Set Id->Set Id->([CT], Set Id, Set Id)
seqCTs _ _ _ EmptyS gks = (nil, nil, gks)
seqCTs mmi pc r (Set n ns) gks = 
    let (t, rns1, gks1)  = compoundAB mmi pc r n gks in
    let (cts, rns2, gks2) = seqCTs mmi pc r ((ns `union` rns1) `sminus` gks1) (gks `union` gks1) in 
    (rearrangeT t:cts, gunion [ns, rns1, rns2], gunion [gks, gks1, gks2])
--where modify_t (OpB opseqC (Kappa (CT k ps cts t1)) t2) = CT k ps [] (OpB opseqC (Kappa (CT (k++"0") [] cts t1)) t2)

consPCTD::MMInfo String String->PC String String->PCTD
consPCTD mmi pc = 
  let r = relKs mmi pc
      (cts, _, _) = seqCTs mmi pc r (singles $ startCompound mmi pc) nil in 
  PCTD (getPCDef pc) cts

revname :: Eq p => p -> p -> p -> p
revname nm k p = if nm == k then p else nm
rename :: PCT -> Id -> Id -> PCT
rename (Atom nm og oats) k p = Atom (revname nm k p) og oats
rename (OpB op t1 t2) k p = OpB op (rename t1 k p) (rename t2 k p)
rename (Kappa (CT nm ps cts t)) k p = 
  Kappa (CT (revname nm k p) ps (map theCt $ foldr (\t' ts->(rename t' k p):ts) [] (fmap Kappa cts)) (rename t k p))
rename (Ref nm g ps rs) k p = Ref (revname nm k p) g ps rs 
rename NilT _ _ = NilT
rename StopT _ _ = StopT
rename SkipT _ _ = SkipT

within :: PCT -> Set Id
within (Atom nm _ _) = singles nm
within (OpB _ t1 t2) = (within t1) `union` (within t2)
within (Kappa (CT nm _ cts t)) = (foldr (\ct wcts->(within $ Kappa ct) `union` wcts) nil cts) `union` (singles nm) `union` (within t)
within (Ref _ _ _ _) = nil
within NilT = nil
within StopT = nil
within SkipT = nil

relWithinRel_cts :: [CT] -> Rel Id Id
relWithinRel_cts cts = (foldr (\ct rct->(relWithin $ Kappa ct) `union` rct) nil cts)
relWithinRel :: Id -> PCT -> Rel Id Id
relWithinRel nc (Atom na _ _) = singles (nc, na)
relWithinRel nc (OpB _ t1 t2) =  (relWithinRel nc t1) `union` (relWithinRel nc t2)
relWithinRel nc (Kappa (CT nm _ cts t)) = singles (nc, nm) `union` (relWithinRel_cts cts) `union` (relWithin t)
relWithinRel _ (Ref _ _ _ _) = nil
relWithinRel _ NilT = nil
relWithinRel _ StopT = nil
relWithinRel _ SkipT = nil

relWithin :: PCT -> Rel Id Id
relWithin (Kappa (CT nm _ cts t)) = (relWithinRel_cts cts) `union` relWithinRel nm t
--relWithin (TSeq t1 t2) = relWithin t1 ++ relWithin t2
relWithin _ = nil

atomsOfPCTD :: Foldable t=>t CT ->Set String
atomsOfPCTD = foldr (\ct ats->(atomsOfPCT (Kappa ct)) `union` ats) EmptyS

atomsOfPCTs :: PCT -> PCT -> Set String
atomsOfPCTs t1 t2 = (atomsOfPCT t1) `union` atomsOfPCT t2
atomsOfPCT :: PCT -> Set String
atomsOfPCT (Atom na _ Nothing) = singles na
atomsOfPCT (Atom _ _ (Just (_, ats))) = 
  if head ats == '{' && last ats == '}' then set $ words' (== ',') (drop 1 (take ((length ats) - 1) ats)) else nil
atomsOfPCT (OpB (OpThrow as) t1 t2) = (set as) `union` atomsOfPCTs t1 t2
atomsOfPCT (OpB _ t1 t2) = atomsOfPCTs t1 t2
atomsOfPCT (Kappa (CT _ _ cts t)) = foldr (\ct rct->(atomsOfPCT $ Kappa ct) `union` rct) nil cts `union` (atomsOfPCT t)
atomsOfPCT (Ref _ _ _ rs) = foldr (\(_, to) as->to `intoSet` as) nil rs
atomsOfPCT NilT = EmptyS
--atomsOfPCT (TSeq t1 t2) = (atomsOfPCT t1) `union` (atomsOfPCT t2)
atomsOfPCT  StopT = EmptyS
atomsOfPCT  SkipT = EmptyS

isOperator :: PCT -> Bool
isOperator (OpB _ _ _) = True
isOperator _ = False

isAtomic :: PCT -> Bool
isAtomic at@(Atom _ _ _) = isAtom at
isAtomic (Kappa _) = True
isAtomic (NilT) = True
isAtomic (StopT) = True
isAtomic (SkipT) = True
isAtomic (Ref _ _ _ _) = True
isAtomic (OpB (OpSeq _) t NilT) = isAtom t
isAtomic _ = False

isSole :: PCT -> Bool
isSole (Atom _ _ _) = True
isSole (Kappa _) = True
isSole (OpB _ t1 _) = isAtomic t1 
isSole (NilT) = True
isSole (StopT) = True
isSole (SkipT) = True
isSole (Ref _ _ _ _) = True


isAtomAny :: PCT -> Bool
isAtomAny (Atom _ _ as) = isSomething as
isAtomAny _ = False

isAtom :: PCT -> Bool
isAtom (Atom _ _ as) = isNil as
isAtom _ = False

