
------------------------
-- Project: PCs
-- Module: 'PCs'
-- Description: Module that retrieves information from the Fragmenta-based representation of PCs
-- Author: Nuno Amálio
------------------------

module PCs.PCs(PC
    , isNodeOfTys
    , getAtoms
    , getPCStart
    , load_mm_info
    , startCompound
    , getPCDef
    , srcOf
    , tgtOf
    , afterCRel
    , paramsOf
    , expsOf
    , expOfAtom
    , enumValsOf
    , nmOfNamed
    , guardOf
    , ntyNsPC
    , nmOfRef
    , nmOfRefF
    , expsOfRef
    , renamingsOf
    , opValOfOp
    , opQuantifiedOp
    , varBQuantifiedOp
    , quantifiedOpStart
    , nextNode
    , nextNodes
    , successorsOf
    , compoundStart
    , withinRel
    , importsOf
    , nextAfterC
    , nextNodesAfter
    , nextNodeAfter
    , branchesOfOp
    , innerKs
    , relKs
    , innerRefKs
    , refKs
    , commonInnerKs
    , hidden_RC
    , inner_Ref
    , openAC
    , guardOfOp) 
where

import Gr_Cls
import Grs
import GrswT
import Mdls 
import LoadCheckDraw
import Relations
import Sets
import SGrs
import Frs
import TheNil
import MyMaybe
import ParseUtils
import SimpleFuns
import PCs.PCs_MM_Names
import Control.Monad(when)
import MMI

type PC a b = GrwT a b

load_pcs_amm :: String -> IO (Mdl String String)
load_pcs_amm def_path = do
  (_, mdl)<-loadMdl def_path "PCs_AMM"
  return mdl

load_pcs_cmm :: String -> IO (Mdl String String)
load_pcs_cmm def_path = do
  (_, mdl) <- loadMdl def_path "PCs_MM"
  return mdl

load_pcs_rm :: String -> IO (GrM String String)
load_pcs_rm def_path = do
    rm<-load_rm_cmdl_def def_path "PCs_MM"
    return rm

load_mm_info :: String -> IO (MMI String String)
load_mm_info def_path = do
  amm<-load_pcs_amm def_path
  cmm<-load_pcs_cmm def_path
  rm<-load_pcs_rm def_path
  return (consMMI cmm amm rm (fsg . reso_m $ cmm))

--isNodeOfTy n ty sg_mm pc = 
--    let t = str_of_ostr $ tyOfNM n pc in
--    t `elem` img (inv $ inhst sg_mm) [show_cmm_n sty]

isNodeOfTys :: (Eq b) => String -> [PCs_CMM_Ns] -> SGr String b -> PC String b -> Bool
isNodeOfTys n tys sg_mm pc = 
    let t = str_of_ostr $ tyOfNM n pc in
    t `elem`  (img (inv $ inhst sg_mm) [show_cmm_n sty | sty<-tys])

ntyNsPC::SGr String String->PC String String->PCs_CMM_Ns->Set String
ntyNsPC sg_mm pc nt = ns_of_ntys pc sg_mm [show_cmm_n nt]

getAtoms::SGr String String->PC String String-> Set String
getAtoms sg_mm pc = 
   foldr (\a as->(nmOfNamed pc a) `intoSet` as) nil (ntyNsPC sg_mm pc CMM_Atom)
   --where extAtoms nm Nothing = singles nm
   --      extAtoms _ (Just (_, Left _)) = nil
   --      extAtoms _ (Just (_, Right ats)) = set ats

-- Gets starting node of  PC 
getPCStart :: SGr String String ->PC String String -> String
getPCStart sg_mm pc = the $ ntyNsPC sg_mm pc CMM_StartN

-- Get's PCs starting compound
startCompound :: MMI String String -> PC String String -> String
startCompound mmi pc = the $ (nextNodes mmi pc $ getPCStart (gCRSG mmi) pc) `intersec`  (ntyNsPC (gCRSG mmi) pc CMM_Compound)


--Gets start node of a compound, the target of a defined connector
compoundStart :: MMI String String -> PC String String ->String-> String
compoundStart mmi pc n = 
   let defC = successorsOf mmi pc n `intersec` img (inv $ fV pc) [show_cmm_n CMM_DefinesC] in
   the $ successorsOf mmi pc (the defC)

-- Obtains the two level morphism from PCs to the abstract layer 
twolm :: (Eq a, Eq b, GRM gm2) => MMI a b -> gm2 a b -> GrM a b
twolm mmi pc =  (gRM mmi) `ogm` pc  

-- Successors of a connector node
successorsOfC::Eq a=>MMI a String ->PC a String->a ->Set a
successorsOfC mmi pc nc = 
    img (tgt pc) $ img (inv . fE $ twolm mmi pc) [show_amm_e AMM_EConnector_tgt] `intersec` dom_of (rres (src pc) [nc])

-- Successors of any node
successorsOf :: MMI String String -> PC String String ->String-> Set String
successorsOf mmi pc n =
   let succsOfN = img (src pc) $ img (inv . fE $ twolm mmi pc) [show_amm_e AMM_EConnector_src]  `intersec` dom_of (rres (tgt pc) [n]) in
   if (isNodeOfTys n [CMM_Node] (gCRSG mmi) pc) then succsOfN else if (isNodeOfTys n [CMM_Connector] (gCRSG mmi) pc) then successorsOfC mmi pc n else nil


-- Gets the predecessors of a connector
predecessorsOfC :: (Eq b, GR g, GRM g) => MMI b String -> g b String -> b -> Set b
predecessorsOfC mmi pc nc = 
    img (tgt pc) $ img (inv . fE $ twolm mmi pc) [show_amm_e AMM_EConnector_src] `intersec` dom_of (rres (src pc) [nc])

nextNode :: MMI String String -> PC String String -> String -> Maybe String
nextNode mmi pc n = 
  let n' = maybeFrSet $ successorsOf mmi pc n in
  let next' = n' /= Nothing && (not $ isNodeOfTys (the n') [CMM_Node] (gCRSG mmi) pc) in
  if not next' then n' else maybeFrSet $ successorsOf mmi pc (the n')

nextNodes :: MMI String String -> PC String String -> String -> Set String
nextNodes mmi pc n = 
  let ns' = successorsOf mmi pc n in
  let next' = (not . null $ ns') && (not $ isNodeOfTys (the ns') [CMM_Node] (gCRSG mmi) pc) in
  if not next' then ns' else foldr (\x xs-> (successorsOf mmi pc x) `union` xs) nil ns'


nextAfterC :: MMI String String -> PC String String -> String -> Set String
nextAfterC mmi pc n = (successorsOf mmi pc n) `intersec` (ntyNsPC (gCRSG mmi) pc CMM_AfterC)

branchesOfOp :: MMI String String -> PC String String -> String -> Set String
branchesOfOp mmi pc n = 
    let ns = successorsOf mmi pc n in
    filterS (\n->the (tyOfNM n pc) == show_cmm_n CMM_BranchC) ns
    `union` filterS (\n->the (tyOfNM n pc) == show_cmm_n CMM_BMainIfC) ns
    `union` filterS (\n->the (tyOfNM n pc) == show_cmm_n CMM_BElseC) ns
    `union` filterS (\n->the (tyOfNM n pc) == show_cmm_n CMM_BJumpC) ns

nextNodesAfter :: MMI String String -> PC String String -> String -> Set String
nextNodesAfter mmi pc n = let after = nextAfterC mmi pc n in 
    if isNil after then nil else successorsOf mmi pc (the after)

guardOfOp :: MMI String String -> PC String String -> String -> Maybe String
guardOfOp mmi pc n = 
    let ns = successorsOf mmi pc n in
    let n_if_b = filterS (\n->the (tyOfNM n pc) == show_cmm_n CMM_BMainIfC) ns in
    if isNil n_if_b then Nothing else guardOf pc (the n_if_b)

nextNodeAfter :: MMI String String -> PC String String -> String -> Maybe String
nextNodeAfter mmi pc n = maybeFrSet $ nextNodesAfter mmi pc n

-- Gets PC's definitional node 
getPCDef :: Eq b => PC String b -> String
getPCDef pc = appl (inv . fV $ pc) (show_cmm_n CMM_PCDef)

srcOf :: Eq a => MMI a String -> PC a String-> a -> a
srcOf mmi pc c = the $ predecessorsOfC mmi pc c

tgtOf :: MMI String String -> PC String String -> String -> String
tgtOf mmi pc c = the $ successorsOfC mmi pc c

-- Relation induced by 'AfterC' connector
afterCRel :: MMI String String -> PC String String -> Rel String String
afterCRel mmi pc = 
  let ns_e = ntyNsPC (gCRSG mmi) pc CMM_AfterC in
  fmap (\ne->(srcOf mmi pc ne, tgtOf mmi pc ne)) ns_e

expVals :: Foldable t => PC String String->t String ->[String]
expVals pc bvs = 
   let bvs' = foldr (\p ps'->getPair p:ps') nil bvs
       obvs = quicksortp (\(k1, _) (k2, _)->k1 <= k2) bvs' in
   map snd obvs
   where
      toIntSnd (b, ks) = let k = snd $ splitAtStr "_" ks in (read k::Int, b)
      getPair b = toIntSnd (splitAtStr "_" (snd $ splitAtStr "EV_" b))

expValsOf ::PC String String-> String -> Either String [String]
expValsOf pc n = 
   let vss = img (tgt pc) $ img (inv $ src pc) [n] `intersec` es_of_ety pc (show_cmm_e CMM_EvExps) 
       vs = img (tgt pc) $ img (inv $ src pc) [n] `intersec` es_of_ety pc (show_cmm_e CMM_EvExp) in
    if null vss then Left .the $ expVals pc vs else Right $ expVals pc vss 
    
pexps :: Foldable t => PC String String->t String ->[Either String [String]]
pexps pc bs = 
  let ips = foldl (\ps' p->if mkPair p `elem` ps' then ps' else mkPair p:ps') nil bs
      obs = quicksortp (\(k1, _) (k2, _)->k1 < k2) ips in
  foldr(\b bvs->(expValsOf pc b):bvs) nil (fmap snd obs)
  where
     toIntFst (k, s) = (read k::Int, s)
     mkPair p = toIntFst (snd (splitAtStr "_txtExp_" p), p)

pair_of_rename :: String -> (String, String)
pair_of_rename ren = 
  splitAtStr "_" (snd $ splitAtStr "_renaming_" ren)

prenamings :: Foldable t => t String -> Rel String String
prenamings = foldr (\r ps'->pair_of_rename r `intoSet` ps') nil

tyOfParam :: PC String String -> String -> Maybe String
tyOfParam pc n = 
  let ptys = img (inv . src $ pc) [n] `intersec`  es_of_ety pc (show_cmm_e CMM_Etype) in
  if null ptys then Nothing else applM (tgt pc) (the ptys)
  --applM (tgt pc) (the $ img (inv . src $ pc) [n] `intersec`  es_of_ety pc (show_cmm_e CMM_Etype))

pparams :: Foldable t => PC String String->t String ->[(String, Maybe String)]
pparams pc ps = 
  let ips = foldr (\p ps'->(getOrdering p, (nmOfNamed pc p, tyOfParam pc p)):ps') nil ps
      ops = quicksortp (\(k1, _) (k2, _)->k1 <= k2) ips in
      fmap snd ops
  where
     intOfFst (k, _) = read k::Int
     getOrdering p = intOfFst (splitAtStr "_" (snd (splitAtStr "_param_" p)))

paramsOf ::PC String String-> String -> [(String, Maybe String)]
paramsOf pc n = 
   let ps = img (tgt pc) $ img (inv $ src pc) [n] `intersec` es_of_ety pc (show_cmm_e CMM_Eparams) in
   pparams pc ps

expsOf ::PC String String-> String -> [Either String [String]]
expsOf pc n = 
   let bs = img (tgt pc) $ img (inv $ src pc) [n] `intersec` es_of_ety pc (show_cmm_e CMM_Eexps) in
   pexps pc bs

expOfAtom ::PC String String-> String -> Maybe String
expOfAtom pc n = 
  let es = expsOf pc n in 
  if null es then Nothing else takeFrE . head $ es
  where takeFrE (Left e) = Just e
        takeFrE (Right _) = Nothing

enumValsOf ::PC String String-> String -> Set String
enumValsOf pc n = 
   img (tgt pc) $ img (inv $ src pc) [n] `intersec` es_of_ety pc (show_cmm_e CMM_EenumVals)

--anyExpOfAt ::PC String String->String->Maybe (String, Either String [String])
--anyExpOfAt pc n = 
--   let ps = img (tgt pc) $ (img (inv $ src pc) [n ++ "_anyExp"]) `intersec`  (es_of_ety pc $ show_cmm_e CMM_Evar) in
--   let ps'= img (tgt pc) $ (img (inv $ src pc) [n ++ "_anyExp"]) `intersec`  (es_of_ety pc $ show_cmm_e CMM_Eof) in
--   if isNil ps' then Nothing else Just (if null ps then "" else the ps, the $ pbindings pc ps')

renamingsOf ::PC String String->String->Rel String String
renamingsOf pc n = 
   let rs = img (tgt pc) $ img (inv $ src pc) [n] `intersec`  (es_of_ety pc $ show_cmm_e CMM_ERenamings) in
   prenamings rs   

inner_Ref ::PC String String->String ->Bool
inner_Ref pc n = 
   let is = img (tgt pc) $ (img (inv $ src pc) [n]) `intersec`  (es_of_ety pc $ show_cmm_e CMM_EReference_inner) in
   if isSomething is then (the is) == "YesV" else False

hidden_RC :: PC String String-> String -> Bool
hidden_RC pc c = 
   let hs = img (tgt pc) $ (img (inv $ src pc) [c]) `intersec`  (es_of_ety pc $ show_cmm_e CMM_EReferenceC_hidden) in
   if isSomething hs then (the hs) == "YesV" else False

openAC ::PC String String->String->Bool
openAC pc c = 
   let os = img (tgt pc) $ (img (inv $ src pc) [c]) `intersec`  (es_of_ety pc $ show_cmm_e CMM_EAfterC_copen) in
   if isSomething os then (the os) == "YesV" else False

--nmOfNamed :: gm a String -> a -> b
nmOfNamed :: PC String String -> String -> String
nmOfNamed pc n = 
  butLast $ appl (tgt pc) (the $ img (inv . src $ pc) [n] `intersec`  es_of_ety pc (show_cmm_e CMM_Ename))

guardOf :: PC String String->String->Maybe String
guardOf pc n =
   let p = img (tgt pc) $ img (inv . src $ pc) [n]  `intersec`  es_of_ety pc (show_cmm_e CMM_Eguard) in
   if null p then Nothing else Just (snd $ splitAtStr "_guard_" (the p))

nmOfRef ::PC String String->String -> String
nmOfRef pc n = 
  let rn = img (tgt pc) $ img (inv . src $ pc) [n] `intersec`  es_of_ety pc (show_cmm_e CMM_EReference_name) in
  if null rn then "" else butLast . the $ rn

nmOfRefF :: MMI String String -> PC String String -> String -> String
nmOfRefF mmi pc n = 
  let rn = nmOfRef pc n in
  let rc = the $ (successorsOf mmi pc n) `intersec` (ntyNsPC (gCRSG mmi) pc CMM_ReferenceC) in
  if null rn then the $ successorsOf mmi pc rc else rn 

expsOfRef :: MMI String String->PC String String->String->[Either String [String]]
expsOfRef mmi pc n =
  let rn = nmOfRef pc n in
  let rc = the $ (successorsOf mmi pc n) `intersec` (ntyNsPC (gCRSG mmi) pc CMM_ReferenceC) in
  if null rn then expsOf pc rc else expsOf pc n

opValId :: SGr String String -> PC String String -> String -> String
opValId sg_mm pc n = 
   if isNodeOfTys n [CMM_Operator] sg_mm pc then appl (fV pc) n else ""

opValOfOp :: SGr String String -> PC String String -> String -> String
opValOfOp sg_mm pc n =
   let nOpVal = appl (tgt pc) (first $ img (inv $ src pc) [n] `intersec` es_of_ety pc (show_cmm_e CMM_ECombination_op)) in
   opValId sg_mm pc nOpVal

opQuantifiedOp :: SGr String String -> PC String String -> String -> String
opQuantifiedOp sg_mm pc n =
   let nOpVal = appl (tgt pc) (first $ img (inv $ src pc) [n] `intersec` es_of_ety pc (show_cmm_e CMM_EopOfQuantifiedOp)) in   
   opValId sg_mm pc nOpVal

varBQuantifiedOp ::PC String String->String->(String, Either String [String])
varBQuantifiedOp pc n = 
   let ps = img (tgt pc) $ (img (inv $ src pc) [n]) `intersec`  (es_of_ety pc . show_cmm_e $ CMM_Evar) 
       ps'= img (tgt pc) $ (img (inv $ src pc) [n]) `intersec`  (es_of_ety pc . show_cmm_e $ CMM_Eexps) in
   (if null ps then "" else the ps, the $ pexps pc ps')

quantifiedOpStart::MMI String String->PC String String->String->String
quantifiedOpStart mmi pc n = 
  let bC = successorsOf mmi pc n `intersec` img (inv $ fV pc) [show_cmm_n CMM_BranchC] in
   the $ successorsOf mmi pc (the bC)
   
--expQuantifiedOp ::PC String String->String->Either String [String]
--expQuantifiedOp pc n = 
--   let ps'= img (tgt pc) $ (img (inv $ src pc) [n]) `intersec` (es_of_ety pc $ show_cmm_e CMM_Eexps) in
--   the $ pexps pc ps'

combinePAsU::(Eq a1, Eq a2)=>(Set a1, Set a2) -> (Set a1, Set a2) -> (Set a1, Set a2)
combinePAsU (x, y) (x', y') = (x `union` x', y `union` y') 

withinRelWiths::Eq a=>MMI String String -> PC String String -> String -> Set String -> Set String -> (Rel String String, Set a)
withinRelWiths mmi pc n ns pcs = 
  let combine (x, y, z) (x', y', z') = (x `union` x', y `union` y', z `union` z') in
  let to_pair (x, y, _) = (x, y) in
  let as_triple (x, y) z = (x, y, z) in
  let upd_ks k = if isNodeOfTys k [CMM_Compound] (gCRSG mmi) pc then singles k else nil in
  to_pair $ foldl (\ks k->if k `elem` thdT ks then ks else as_triple (withinRelWithAux mmi pc n k $ thdT ks) (upd_ks k) `combine` ks) (nil, nil, pcs) ns

withinRelWithAux::Eq a=>MMI String String ->PC String String->String->String->Set String->(Rel String String, Set a)
withinRelWithAux mmi pc n n' pcs
   | isNodeOfTys n' [CMM_Atom] (gCRSG mmi) pc = (singles (n, n'), nil) `combinePAsU` withinRelWithOpt (nextNode mmi pc n')
   -- Here it depends on whether it is definitional or not
   | isNodeOfTys n' [CMM_Compound] (gCRSG mmi) pc = if n' `elem` (n `intoSet` pcs) then (nil, nil) else ((n, n') `intoSet` withinRelWith mmi pc n' (n `intoSet` pcs), nil) 
   | isNodeOfTys n' [CMM_Reference] (gCRSG mmi) pc = (nil, nil) 
   | isNodeOfTys n' [CMM_Combination] (gCRSG mmi) pc = let ns = nextNodes mmi pc n' in withinRelWiths mmi pc n ns pcs
   | isNodeOfTys n' [CMM_Stop,CMM_Skip] (gCRSG mmi) pc = (nil, nil) 
   | isNodeOfTys n' [CMM_QuantifiedOp] (gCRSG mmi) pc = (singles (n, n'), nil) `combinePAsU` withinRelWithOpt (nextNode mmi pc n')
   where withinRelWithOpt Nothing = (nil, nil) 
         withinRelWithOpt (Just k) = if k `elem` pcs then (nil, nil)  else withinRelWithAux mmi pc n k pcs
         --nilR = (nil, nil)

withinRelForNs :: MMI String String ->PC String String -> Set String-> Set String -> Set (String, String)
withinRelForNs _ _ EmptyS _ = EmptyS
withinRelForNs mmi pc (Set n ns) pcs = 
  let (r, rcs) = withinRelWith' mmi pc n pcs in
  r `union` withinRelForNs mmi pc (rcs `union` ns) (dom_of r `union` pcs)

withinRelWith' :: Eq a=>MMI String String ->PC String String->String ->Set String ->(Rel String String, Set a)
withinRelWith' mmi pc n pcs =
   let next_ns = nextNodes mmi pc n in
   withinRelWiths mmi pc n next_ns pcs

withinRelWith :: MMI String String -> PC String String -> String -> Set String -> Rel String String
withinRelWith mmi pc n pcs =
   let (r, rcs) = withinRelWith' mmi pc n pcs in
   let r' = withinRelForNs mmi pc rcs (dom_of r `union` pcs) in
   r `union` r'

withinRel :: MMI String String -> PC String String -> Rel String String
withinRel mmi pc = withinRelWith mmi pc (startCompound mmi pc) nil

innerKsOf :: MMI String String -> PC String String ->Set String->Set String-> Set String
innerKsOf mmi pc EmptyS _ = EmptyS
innerKsOf mmi pc (n `Set` ns) vns
    | isNodeOfTys n [CMM_Atom] (gCRSG mmi) pc = innerKsOf mmi pc ((nextNodesAfter mmi pc n) `union` ns) vns
    | isNodeOfTys n [CMM_Reference] (gCRSG mmi) pc && (not $ inner_Ref pc n) = innerKsOf mmi pc (nextNodesAfter mmi pc n `union` ns) vns
    | isNodeOfTys n [CMM_Reference] (gCRSG mmi) pc && (inner_Ref pc n) = 
        innerKsOf mmi pc (singles (nmOfRefF mmi pc n) `union` (nextNodesAfter mmi pc n) `union` ns) vns
    | isNodeOfTys n [CMM_Compound] (gCRSG mmi) pc = let nas = nextNodesAfter mmi pc n in
        if n `elem` vns then innerKsOf mmi pc ns vns else n `intoSet` (innerKsOf mmi pc ((compoundStart mmi pc n) `intoSet` (nas `union` ns)) $ n `intoSet` vns)
    | isNodeOfTys n [CMM_Combination] (gCRSG mmi) pc = innerKsOf mmi pc ((nextNodes mmi pc n) `union` ns) vns
    | isNodeOfTys n [CMM_Stop,CMM_Skip] (gCRSG mmi) pc = innerKsOf mmi pc ns vns 
    -- | otherwise = (the (tyOfNM n pc)):innerKsOf mmi pc ns

innerKs::MMI String String -> PC String String -> String -> Set String
innerKs mmi pc n = innerKsOf mmi pc (singles $ compoundStart mmi pc n) (singles n)

innerRefKsOf :: MMI String String -> PC String String ->Set String-> Set String -> Set String
innerRefKsOf _ _ EmptyS _ = nil
innerRefKsOf mmi pc (Set n ns) vns
  | isNodeOfTys n [CMM_Atom,CMM_Compound, CMM_QuantifiedOp] (gCRSG mmi) pc = 
      if n `elem` vns then innerRefKsOf mmi pc ns vns else  innerRefKsOf mmi pc ((nextNodesAfter mmi pc n) `union` ns) vns
  | isNodeOfTys n [CMM_Combination] (gCRSG mmi) pc = 
      innerRefKsOf mmi pc ((nextNodes mmi pc n) `union` ns) vns
  | isNodeOfTys n [CMM_Stop,CMM_Skip] (gCRSG mmi) pc = innerRefKsOf mmi pc ns vns 
  | isNodeOfTys n [CMM_Reference] (gCRSG mmi) pc && (not $ inner_Ref pc n) = innerRefKsOf mmi pc ((nextNodesAfter mmi pc n) `union` ns) vns 
  | isNodeOfTys n [CMM_Reference] (gCRSG mmi) pc && (inner_Ref pc n) = let rn = nmOfRefF mmi pc n in 
      if rn `elem` vns then innerRefKsOf mmi pc ns vns else rn `intoSet` (innerRefKsOf mmi pc ((nextNodesAfter mmi pc n) `union` ns)) (rn `intoSet` vns)

innerRefKs::MMI String String -> PC String String -> String -> Set String
innerRefKs mmi pc n = innerRefKsOf mmi pc (singles $ compoundStart mmi pc n) (singles n)

refKsOf::MMI String String -> PC String String -> Set String -> Set String-> Set String
refKsOf _ _ EmptyS _ = nil
refKsOf mmi pc (Set n ns) vns
   | isNodeOfTys n [CMM_Atom,CMM_Compound, CMM_QuantifiedOp] (gCRSG mmi) pc = 
      if n `elem` vns then refKsOf mmi pc ns vns else refKsOf mmi pc ((nextNodesAfter mmi pc n) `union` ns) vns
   | isNodeOfTys n [CMM_Combination] (gCRSG mmi) pc = 
      refKsOf mmi pc ((nextNodes mmi pc n) `union` ns) vns
   | isNodeOfTys n [CMM_Stop,CMM_Skip] (gCRSG mmi) pc = refKsOf mmi pc ns vns 
   | isNodeOfTys n [CMM_Reference] (gCRSG mmi) pc  = let rn = nmOfRefF mmi pc n in 
      if set [n, rn] `subseteq` vns then refKsOf mmi pc ns vns else rn `intoSet` (refKsOf mmi pc ((nextNodesAfter mmi pc n) `union` ns)) (set [n, rn] `union` vns)
   -- | isNodeOfTys n [CMM_Reference] (gCRSG mmi) pc && (inner_Ref pc n) = outerRefKsOf mmi pc ((nextNodesAfter mmi pc n) `union` ns) vns 

refKs::MMI String String -> PC String String -> String -> Set String
refKs mmi pc n = refKsOf mmi pc (singles $ compoundStart mmi pc n) (singles n)
--commonInnerKsOf mmi pc [] _ = []
--commonInnerKsOf mmi pc (n:ns) vns 
--    | isNodeOfTys n [CMM_Atom, CMM_Reference] (gCRSG mmi) pc = commonInnerKs mmi pc ((nextNodesAfter mmi pc n)++ns) vns 
--    | isNodeOfTys n [CMM_Compound] (gCRSG mmi) pc = let nas = nextNodesAfter mmi pc n in
--        if n `elem` vns then commonInnerKsOf mmi pc ns vns else commonInnerKsOf mmi pc ((compoundStart mmi pc n):(nas++ns)) (n:vns)
--    | isNodeOfTys n [CMM_Operator] (gCRSG mmi) pc = let nns = nextNodes mmi pc n in
--      (gintersec (foldr (\n cns->(innerKsOf mmi pc [n] vns):cns) [] nns)) `intersec` (commonInnerKsOf mmi pc ns (nns++vns))
--    | isNodeOfTys n [CMM_Stop] (gCRSG mmi) pc = commonInnerKsOf mmi pc ns vns 

divergentInnerKs0 :: MMI String String -> PC String String -> Set String -> Set String -> Set (Set String)
divergentInnerKs0 mmi pc EmptyS _ = nil
divergentInnerKs0 mmi pc (Set n ns) vns
    | isNodeOfTys n [CMM_Atom] (gCRSG mmi) pc = let nns = nextNodesAfter mmi pc n in
        divergentInnerKs0 mmi pc (nns `union` ns) vns 
    | (isNodeOfTys n [CMM_Reference] (gCRSG mmi) pc) && (not $ inner_Ref pc n) = 
        let nns = nextNodesAfter mmi pc n in divergentInnerKs0 mmi pc (nns `union` ns) vns 
    | (isNodeOfTys n [CMM_Reference] (gCRSG mmi) pc) && (inner_Ref pc n) =  
        let nns = nextNodesAfter mmi pc n in let rn = nmOfRefF mmi pc n in
        divergentInnerKs0 mmi pc (rn `intoSet` (nns `union` ns)) vns
    | isNodeOfTys n [CMM_Compound] (gCRSG mmi) pc = let nns = nextNodesAfter mmi pc n in
        if n `elem` vns then divergentInnerKs0 mmi pc ns vns else divergentInnerKs0 mmi pc (compoundStart mmi pc n `intoSet` (nns `union` ns)) (n `intoSet` vns)
    | isNodeOfTys n [CMM_Combination] (gCRSG mmi) pc = let nns = nextNodes mmi pc n in
        (foldr (\n' dss->(innerKsOf mmi pc (singles n') vns) `intoSet` dss) nil nns) `union` (divergentInnerKs0 mmi pc ns vns)
    | isNodeOfTys n [CMM_Stop,CMM_Skip] (gCRSG mmi) pc = divergentInnerKs0 mmi pc ns vns 

divergentInnerKs :: MMI String String -> PC String String -> String -> Set (Set String)
divergentInnerKs mmi pc n = divergentInnerKs0 mmi pc (singles $ compoundStart mmi pc n) (singles n)

commonInnerKs :: MMI String String -> PC String String -> String -> Set String
commonInnerKs mmi pc n = gunion (divergentInnerKs mmi pc n)

--nextKsOf0::MMInfo String String->PC String String->String->Set String->Set String
--nextKsOf0 mmi pc n nns = 
--  foldr (\n' ns->if isCompound n' then n' `intoSet` ns else (nextKsOf mmi pc n') `union` ns) EmptyS nns
--  where isCompound n = isNodeOfTys n [CMM_Compound] (gCRSG mmi) pc

nextKsOf::MMI String String->PC String String->String->Set String
nextKsOf mmi pc n =
  let nns = if isNxtNAtfer then nextNodesAfter mmi pc n else nextNodes mmi pc n in
  foldr (\n' ns->if isCompound n' then n' `intoSet` ns else (nextKsOf mmi pc n') `union` ns) EmptyS nns
  where isNxtNAtfer = isNodeOfTys n [CMM_Atom, CMM_Reference] (gCRSG mmi) pc
        isCompound sn = isNodeOfTys sn [CMM_Compound] (gCRSG mmi) pc
  
relKsOf::MMI String String->PC String String->Set String->Rel String String->Rel String String
relKsOf mmi pc EmptyS r = r
relKsOf mmi pc (n `Set` ns) r =
  let nks = nextKsOf mmi pc n `sminus` (singles n) 
      r' = fmap (pairUp n) nks `union` r in
  relKsOf mmi pc (ns `union` nks `sminus` (dom_of r)) r'

relKs::MMI String String->PC String String->Rel String String
relKs mmi pc = relKsOf mmi pc (singles $ startCompound mmi pc) nil

--getImports :: GrM a -> [String]
importsOf :: SGr String String -> PC String String -> Set String
importsOf sg_mm pc = ntyNsPC sg_mm pc CMM_Import
