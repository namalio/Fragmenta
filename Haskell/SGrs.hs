--------------------------------------
-- Project: PCs/Fragmenta
-- Module: 'SGrs'
-- Description: Fragmenta's structural graphs (SGs)
-- Author: Nuno Amálio
-------------------------------------
{-# LANGUAGE MultiParamTypeClasses #-}

module SGrs(SGr
   , consSG
   , inhG
   , g_sg
   , srcm
   , tgtm
   , nty
   , ety
   , pe
   , ds
   , nsTys
   , nsP
   , nsN
   , esTys
   , esA
   , esI
   , srcst
   , tgtst
   , inh
   , inhst
   , disjSGs
   , unionSG
   , unionSGs
   , subsume_sg
   , sg_refinesz
   , errs_sg_refinesz
   , tsg_refinesz
   , errs_tsg_refinesz
   , ns_of_ntys
   , es_of_ety
   , ins
   , okETSGs
   , rOkETSGs) 
where

import Sets (Set(..), sminus, gunion, intersec, union, singles, set, intoSet, toList, rest, filterS )
import Relations
import Gr_Cls
import Grs
import ErrorAnalysis
import ShowUtils ( showElems, showElems', showEdges, showNodes )
import SGElemTys
    (sgety_set
    , sgnty_set
    , SGED(Duni, Dbi)
    , SGETy(..)
    , SGNTy(..) )
import Mult
import MyMaybe
import GrswT ( consGWT, GrwT )
import PathExpressions
import TheNil
import SimpleFuns (pair_up)
import Logic ( implies )
import Utils ( reportWF )

data SGVCEOP = Eq | Neq | Leq | Geq | Lt | Gt
   deriving (Eq, Show)

-- Structural graphs (SGs)
data SGr a b = SGr {
   g_sg_ :: Gr a b
   , nty_ :: Rel a SGNTy
   , ety_ :: Rel b SGETy
   , srcm_ :: Rel b Mult
   , tgtm_ :: Rel b Mult
   , p_ :: Rel b (PE a b)
   , d_ :: Rel b b
   , vc_ :: Rel b ((SGVCEOP, Maybe b))
} deriving (Show, Eq)

g_sg :: SGr a b -> Gr a b
g_sg SGr {g_sg_ = g, nty_ = _, ety_ = _, srcm_ = _, tgtm_ = _, p_ = _, d_ = _, vc_ = _} 
   = g
nty :: SGr a b -> Rel a SGNTy
nty SGr {g_sg_ = _, nty_ = nt, ety_ = _, srcm_ = _, tgtm_ = _, p_ = _, d_ = _, vc_ = _} 
   = nt
ety :: SGr a b -> Rel b SGETy
ety SGr {g_sg_ = _, nty_ = _, ety_ = et, srcm_ = _, tgtm_ = _, p_ = _, d_ = _, vc_ = _} 
   = et
srcm :: SGr a b -> Rel b Mult
srcm SGr {g_sg_ = _, nty_ = _, ety_ = _, srcm_ = sm, tgtm_ = _, p_ = _, d_ = _, vc_ = _} 
   = sm
tgtm :: SGr a b -> Rel b Mult
tgtm SGr {g_sg_ = _, nty_ = _, ety_ = _, srcm_ = _, tgtm_ = tm, p_ = _, d_ = _, vc_ = _} 
   = tm
pe :: SGr a b -> Rel b (PE a b)
pe SGr {g_sg_ = _, nty_ = _, ety_ = _, srcm_ = _, tgtm_ = _, p_ = p, d_ = _, vc_ = _} 
   = p
ds :: SGr a b -> Rel b b
ds SGr {g_sg_ = _, nty_ = _, ety_ = _, srcm_ = _, tgtm_ = _, p_ = _, d_ = d, vc_ = _} 
   = d
vcei :: SGr a b -> Rel b (SGVCEOP, Maybe b)
vcei SGr {g_sg_ = _, nty_ = _, ety_ = _, srcm_ = _, tgtm_ = _, p_ = _, d_ = _, vc_ = vc}
   = vc

-- A SG constructor
consSG::Gr a b->Rel a SGNTy->Rel b SGETy->Rel b Mult->Rel b Mult->Rel b (PE a b)
   ->Rel b b->Rel b (SGVCEOP, Maybe b)-> SGr a b
consSG g nt et sm tm p d vc = 
   SGr {g_sg_ = g, nty_ = nt, ety_ = et, srcm_ = sm, tgtm_ = tm, p_ = p, d_ = d, vc_ = vc}

instance GR SGr where
   ns :: (Eq a, Eq b) => SGr a b -> Set a
   ns = ns . g_sg
   es :: (Eq a, Eq b) => SGr a b -> Set b
   es = es . g_sg
   src :: (Eq a, Eq b) => SGr a b -> Rel b a
   src = src . g_sg
   tgt :: (Eq a, Eq b) => SGr a b -> Rel b a
   tgt = tgt . g_sg
   empty :: SGr a b
   empty = consSG empty nil nil nil nil nil nil nil

-- Gets edges of certain types
esTys::(Eq a, Eq b, Foldable t)=>SGr a b->t SGETy->Set b
esTys sg = img (inv . ety $ sg)

-- Gets nodes of certain types
nsTys::(Eq a, Foldable t)=>SGr a b->t SGNTy->Set a
nsTys sg = img (inv . nty $ sg)

-- Gets proxy nodes
nsP :: Eq a=>SGr a b -> Set a
nsP = (flip nsTys) [Nprxy]

-- Gets normal nodes
nsN :: Eq a=>SGr a b -> Set a
nsN = (flip nsTys) [Nnrml]

-- Gets virtual nodes
nsVi :: Eq a=>SGr a b1 -> Set a
nsVi = (flip nsTys) [Nvirt]

-- Gets value nodes
nsVa :: Eq a=>SGr a b -> Set a
nsVa = (flip nsTys) [Nval]

-- Gets the ethereal nodes
nsEther :: Eq a=>SGr a b -> Set a
nsEther = (flip nsTys) [Nabst, Nvirt, Nenum]

-- Gets the inheritance edges
esI::(Eq a, Eq b)=>SGr a b->Set b
esI = (flip esTys) [Einh]

-- Gets the association edges
esA::(Eq a, Eq b)=>SGr a b->Set b
esA = (flip esTys) [et d | et<-[Ecomp, Erel], d<-[Dbi, Duni]]

-- Gets the wander edges
--esW::(Eq a, Eq b)=>SGr a b->Set b
--esW = (flip esTys) [Ewander]

-- Gets the derived edges
esD::(Eq a, Eq b)=>SGr a b->Set b
esD = (flip esTys) [Eder]

-- Gets path edges
esPa::(Eq a, Eq b)=>SGr a b->Set b
esPa = (flip esTys) [Epath]

-- Gets the path constraint edges
esPaCnt::(Eq a, Eq b)=>SGr a b->Set b
esPaCnt sg = esD sg `union` esPa sg

-- Gets the value constraint edges
esVCnt::(Eq a, Eq b)=>SGr a b->Set b
esVCnt = (flip esTys) [Evcnt]

-- Gets the constraint edges
esCnt::(Eq a, Eq b)=>SGr a b->Set b
esCnt sg = esPaCnt sg `union` esVCnt sg

-- Gets multiplicity edges (association + derived)
esM::(Eq a, Eq b)=>SGr a b->Set b
esM sg = esA sg `union` esD sg

-- Gets relation between path nodes as defined by path dependency edges
--ds::(Eq a, Eq b)=>SGr a b->[(a, a)]
--ds sg = (inv $ dres (src sg) (esPD sg)) `rcomp` (dres (tgt sg) (esPD sg))

-- Gets multiplicity edges (connection + derived)
-- esM::Eq a=>SGr a->[a]
-- esM sg = (esC sg) `union` (esD sg)

-- Inheritence graph: SG is restricted to inheritance edges only
inhG :: (Eq b, Eq a) => SGr a b -> Gr a b
inhG sg = restrict sg $ esI sg

-- Inheritence relation buillt from inheritance graph
inh::(Eq a, Eq b)=>SGr a b->Rel a a
inh = relOfG . inhG 

-- Reflexive transitive closure of inheritence relation
inhst::(Eq a, Eq b)=>SGr a b->Rel a a
inhst sg = rtrancl_on (inh sg) (ns sg)

-- totalises 'srcm' by providing multiplicities of uni-directional composition and relation edges
srcma :: (Eq a, Eq b) => SGr a b -> Rel b Mult
srcma sg = (srcm sg) `override` ((esTys sg [Ecomp Duni] `cross` (singles  .singles $ msole_k 1)) `override` (esTys sg [Erel Duni] `cross` (singles  .singles $ msole_many)))

-- src* relations: base and final definitions
srcstr :: (Foldable t, Eq a, Eq b) => SGr a b -> t b->Rel b a
srcstr sg es = dres (src sg) es 

-- src* relations: base and final definitions
srcst :: (Eq a, Eq b) => SGr a b ->Rel b a
srcst sg = (srcstr sg $ esA sg `union` esPaCnt sg) `rcomp` (inv . inhst $ sg)

-- version used in morphisms
srcstm :: (Eq a, Eq b) => SGr a b ->Rel b a
srcstm sg = (srcstr sg $ esA sg) `rcomp` (inv . inhst $ sg)

-- tgt* relations: base and final definitions
tgtstr :: (Foldable t, Eq a, Eq b) => SGr a b ->t b->Rel b a
tgtstr sg es = dres (tgt sg) es

tgtst :: (Eq a, Eq b) => SGr a b ->Rel b a
tgtst sg = (tgtstr sg $ esA sg `union` esPaCnt sg) `rcomp` (inv $ inhst sg)

-- version used in morphisms
tgtstm :: (Eq a, Eq b) => SGr a b ->Rel b a
tgtstm sg = (tgtstr sg $ esA sg) `rcomp` (inv $ inhst sg)

-- Incident edges to a set of nodes, which takes inheritance into account
--esIncidentst :: (Foldable t, Eq a, Eq b) => SGr a b -> t a -> Set b
--esIncidentst sg vs = img (inv $ srcst sg) vs `union` img (inv $ tgtst sg) vs

-- Checks whether edges comply with their type multiplicity allowances
edge_multOk::(Eq a, Eq b)=>SGr a b->b->Bool
edge_multOk sg e = (appl (ety sg) e) `allowedm` (appl (srcma sg) e, appl (tgtm sg) e)

mult_etys_ok::(Eq a, Eq b)=>SGr a b->Bool
mult_etys_ok sg = all (edge_multOk sg) $ esM sg

-- Inheritance relation between pair of nodes complies with the inheritance restrictions of their types
inh_nty_ok :: Eq a => SGr a b -> (a, a) -> Bool
inh_nty_ok sg (v, v') = (appl(nty sg) v) < (appl(nty sg) v')
inh_ntys_ok :: (Eq a, Eq b) => SGr a b -> Bool
inh_ntys_ok sg = all (inh_nty_ok sg) (inh sg)

-- Whether an inheritance hierarchy of a SG is scylic
acyclicI::(Eq a, Eq b)=>SGr a b->Bool
acyclicI = acyclicG . inhG

-- Checks whether the inheritance hierarchy complies with required restrictions
inhOk::(Eq a, Eq b)=>SGr a b->Bool
inhOk sg = inh_ntys_ok sg && acyclicI sg

-- Checks whether an optional node is involved in non-compulsory relations
--nodeopt_ok_src::(Eq a, Eq b)=>SGr a b->a->Bool
--nodeopt_ok_src sg n = all isMultLbZ (img (srcma sg) (img (inv . src $ sg) [n]))
--nodeopt_ok_tgt::(Eq a, Eq b)=>SGr a b->a->Bool
--nodeopt_ok_tgt sg n = all isMultLbZ (img (tgtm sg) (img (inv .tgt $ sg) [n]))
nodeopt_ok::(Eq a, Eq b)=>SGr a b->a->Bool
nodeopt_ok sg n = all isMultLbZ (img (srcma sg) (img (inv . src $ sg) [n]))
--nodeopt_ok sg n = nsIncident sg ((esIncident sg [n]) `sminus` (esI sg)) <= ((nsO sg) `union` (nsV sg))
--img (ety sg) ((esIncidentst sg [n]) `sminus` (esI sg))  `subseteq` [Ewander]

--optsVoluntary::(Eq a, Eq b)=>SGr a b->Bool
--optsVoluntary sg = all (nodeopt_ok sg) $ nsO sg
--adjacentNs (restrict sg (esA sg)) (nsO sg) <= (nsO sg) `union` (nsV sg)
   --nsIncident sg ((esIncident sg [nsO sg]) `sminus` (esI sg)) `subseteq` ((nsO sg) `union` (nsV sg))
--all (nodeopt_ok sg) $ nsO sg

-- Function that checks that a list of multiplicies are well-formed
mults_wf :: Set (Set MultC) -> Bool
mults_wf = all multwf

-- Checks whether a SG is well-formed either totally or partially
okaySGz::(Eq a, Eq b, GNumSets a)=>SGr a b->Bool
okaySGz sg = okayG Nothing (g_sg sg)
   && tfun (nty sg) (ns sg) (sgnty_set) 
   && tfun (ety sg) (es sg) (sgety_set)
   && (dom_of . srcm $ sg) <= es sg  
   && (dom_of . tgtm $ sg) <= es sg

-- Checks whether a SG is well-formed partially
okaySG::(Eq a, Eq b, GNumSets a)=>SGr a b->Bool
okaySG sg = okaySGz sg
   && mults_wf (ran_of . srcm $ sg) && mults_wf (ran_of . tgtm $ sg) 
   && tfun' (srcma sg) (esM sg) && tfun' (tgtm sg) (esM sg)
   && (dom_of . pe $ sg) == esPaCnt sg
   && antireflexive_on (ds sg) (esPa sg) 
   && mult_etys_ok sg 
--   && optsVoluntary sg 
   && inhOk sg 

-- Ethereal nodes must be inherited
etherealInherited::(Eq a, Eq b)=>SGr a b->Bool
etherealInherited sg = (nsEther sg) <= (ran_of $ inh sg)

-- WF conditions of derived edges which apply to total SGs
srcDerEOk :: (Eq a, Eq b) => SGr a b -> b -> Bool
srcDerEOk sg e = (appl (src sg) e, srcPE (restrict (g_sg sg) $ esA sg)  (appl (pe sg) e)) `elem` (inhst sg) 
tgtDerEOk :: (Eq a, Eq b) => SGr a b -> b -> Bool
tgtDerEOk sg e = (appl (tgt sg) e, tgtPE (restrict (g_sg sg) $ esA sg)  (appl (pe sg) e)) `elem` (inhst sg)
derEOk::(Eq a, Eq b)=>SGr a b->b->Bool
derEOk sg e = srcDerEOk sg e && tgtDerEOk sg e
derOk::(Eq a, Eq b)=>SGr a b->Bool
derOk sg = all (derEOk sg) (esD sg)

okPEASrc :: (Eq a, Eq b) => SGr b a -> b -> PEA a -> Bool
okPEASrc sg v (Edg e) = (e, v) `elem` srcst sg
okPEASrc sg v (Inv e) = (e, v) `elem` tgtst sg

okPEATgt :: (Eq a, Eq b) => SGr b a -> b -> PEA a -> Bool
okPEATgt sg v (Edg e) = (e, v) `elem` tgtst sg
okPEATgt sg v (Inv e) = (e, v) `elem` srcst sg

okPEA :: (GR g, Eq a, Eq b) => g b a -> PEA a -> Bool
okPEA sg (Edg e) = e `elem` es sg
okPEA sg (Inv e) = e `elem` es sg

okPEC :: (Eq a, Eq b) => SGr b a -> PEC b a -> Bool
okPEC sg (At pea) = okPEA sg pea
okPEC sg (Dres v pea) = okPEA sg pea && okPEASrc sg v pea
okPEC sg (Rres pea v) = okPEA sg pea && okPEATgt sg v pea

okPE :: (Eq a, Eq b) => SGr b a -> PE b a -> Bool
okPE sg (Ec pe) = okPEC sg pe 
okPE sg (SCmp pec pe) = 
   let g = restrict (g_sg sg) $ esA sg in
   okPEC sg pec && okPE sg pe 
   && (tgtPEC g pec, srcPE g pe) `elem` (inhst sg `union` (inv . inhst $ sg))

isVCEECnt::Eq b=>SGr a b ->b->Bool
isVCEECnt sg vce = isSomething (snd . appl (vcei sg) $ vce)

isVCENCnt::Eq b=>SGr a b ->b->Bool
isVCENCnt sg vce = isNil (snd . appl (vcei sg) $ vce)

isNumeric::(Eq a, Eq b, GNumSets a)=>SGr a b ->a->Bool
isNumeric sg n = 
   (n, nNatS) `elem` inhst sg || (n, nIntS) `elem` inhst sg || (n, nRealS) `elem` inhst sg

eVCntOk::(Eq a, Eq b, GNumSets a)=>SGr a b->b->Bool
eVCntOk sg vce = 
   let ns = appl (tgt sg) (the . snd . appl (vcei sg) $ vce) in
   isVCEECnt sg vce `implies` ((appl (tgt sg) vce, ns) `elem` inhst sg && isNumeric sg ns)
   && isVCENCnt sg vce `implies` ((appl (tgt sg) vce, appl (src sg) vce) `elem` inhst sg && isNumeric sg (appl (src sg) vce))

-- Checks that the value constraint edges are well-formed in a total setting
esVCntsOk::(Eq a, Eq b, GNumSets a)=>SGr a b->Bool
esVCntsOk sg = all (eVCntOk sg) (esVCnt sg)

esCntOk :: (Eq a, Eq b) => SGr a b -> b -> Bool
esCntOk sg e = okPE sg (appl (pe sg) e)
esCntsOk::(Eq a, Eq b, GNumSets a)=>SGr a b->Bool
esCntsOk sg = derOk sg && all (esCntOk sg) (esPaCnt sg) && esVCntsOk sg

-- Whether an inheritance hierarchy of a SG without virtual nodes forms a tree (single-inheritance model)
inhMinus :: (Eq b2, Eq a) => SGr a b2 -> Rel a a
inhMinus sg = relOfG $ subtractNs (inhG sg) (nsVi sg)
isInhTree :: (Eq a, Eq b) => SGr a b -> Bool
isInhTree sg = pfun (inhMinus sg) (ns sg) (ns sg) 

-- WF of total SGs
okayTSG::(Eq a, Eq b, GNumSets a)=>SGr a b->Bool
okayTSG sg = okaySG sg && etherealInherited sg 
   && esCntsOk sg && isInhTree sg 

check_mult_etys_ok :: (Show a, Show b, Eq a, Eq b, GNumSets a) => SGr a b -> ErrorTree
check_mult_etys_ok sg = 
   if mult_etys_ok sg then nile else consSET $ "Certain edges have incorrect multiplicities:"++ (showEdges err_es)
   where err_es = foldr (\e es->if edge_multOk sg e then es else (e:es)) [] (esM sg)

--check_optsVoluntary::(Eq a, Eq b, Show a, Show b)=>SGr a b->ErrorTree
--check_optsVoluntary sg = 
--   if optsVoluntary sg then nile else consSET $ "Optional nodes engaged in compulsory relations:" ++ (showElems' err_opts)
--   where err_opts = foldr (\n ns-> if nodeopt_ok sg n then ns else n:ns) [] (nsO sg)

errsSGz::(Eq a, Eq b, Show a, Show b, GNumSets a)=>SGr a b-> [ErrorTree]
errsSGz sg = 
   let err1 = err_prepend "The underlying graph is malformed." (faultsG "SG" Nothing $ g_sg sg)
       err2 = err_prepend "Function 'nty' is not total. " $ reportFT (nty sg) (ns sg) (sgnty_set)
       err3 = err_prepend "Function 'ety' is not total. " $ reportFT (ety sg) (es sg) (sgety_set)
       err4 = err_prepend "Source multplicity function is not total. " $ reportFT' (srcma sg) (esM sg)
       err5 = err_prepend "Target multplicity function is not total. " $ reportFT' (tgtm sg) (esM sg) in
   [err1, err2, err3, err4, err5]

rOkaySGz::(Eq a, Eq b, Show a, Show b, GNumSets a)=>String->SGr a b-> ErrorTree
rOkaySGz nm sg = reportWF sg nm okaySGz errsSGz

rInhOk::(Eq a, Eq b, Show a, Show b)=>SGr a b->ErrorTree
rInhOk sg = 
   let errs1 = if inh_ntys_ok sg then nile else consSET $ "The following inheritance pairs are not compliant with the node type restrictions:" ++ (showElems' err_inh_pairs)
       errs2 = if acyclicI sg then nile else consSET "The inheritance hierarchy has cycles." in
   if inhOk sg then nile else consET "Errors in the inheritance hierarchy." [errs1, errs2]
   where err_inh_pairs = filterS (not . inh_nty_ok sg) (inh sg)

errsSG::(Eq a, Eq b, Show a, Show b, GNumSets a)=>SGr a b-> [ErrorTree]
errsSG sg = 
   let errs = errsSGz sg in
   let err1 = if mults_wf (ran_of $ srcm sg) then nile else consSET "Well-formedness errors in edge source multiplicities." in
   let err2 = if mults_wf (ran_of $ tgtm sg) then nile else consSET "Well-formedness errors in edge target multiplicities." in
   let err3 = check_mult_etys_ok sg in
--   let err4 = check_optsVoluntary sg in
   let err4 = rInhOk sg in
   errs ++ [err1, err2, err3, err4]

rOkaySG::(Eq a, Eq b, Show a, Show b, GNumSets a)=>String->SGr a b-> ErrorTree
rOkaySG nm sg = reportWF sg nm okaySG errsSG

rEtherealInherited sg = 
   if etherealInherited sg then nile else consSET $ "The following ethereal nodes are not inherited: " ++ (showElems' ens_n_inh)
   where isInherited n = n `elem` (ran_of $ inh sg)
         ens_n_inh = filterS (not . isInherited)(nsEther sg) 

rIsInhTree :: (Eq a, Eq b, Show a) => SGr a b -> ErrorTree
rIsInhTree sg = 
   let msg1 = "The inheritance is not single." in
   let msg2 = "The inheritance hierarchy without virtual nodes is not a tree. " in
   if isInhTree sg then nile else consET msg1 [err_prepend msg2 $ reportPF (inhMinus sg) (ns sg) (ns sg)]

rDerOk::(Eq a, Eq b, Show a, Show b)=>SGr a b-> ErrorTree
rDerOk sg = 
   let msg_src e = "The source of edge " ++ (show e) ++ " is invalid." 
       msg_tgt e = "The target of edge " ++ (show e) ++ " is invalid." 
       cons_ems_src e = if (not $ srcDerEOk sg e) then [msg_src e] else [] 
       cons_ems_tgt e = if (not $ tgtDerEOk sg e) then [msg_tgt e] else [] 
       des_bad = foldr (\e ms->(cons_ems_src e) ++ (cons_ems_tgt e) ++ ms) [] (esD sg) in
   if derOk sg then nile else consSET $ "Errors in the following derived edges: " ++ (showElems' des_bad)

rEsCntsOk :: (Eq a, Show a,Eq b, Show b, GNumSets a)=>SGr a b -> ErrorTree
rEsCntsOk sg = 
   if esCntsOk sg then nile else consSET $ "Errors in the following constraint edges: " ++ (showElems' esCnts_nOk) ++ (show $ srcst sg) ++ (show $ tgtst sg)
   where esCnts_nOk = filterS (not . esCntOk sg) (esCnt sg) 

errsTSG::(Eq a, Eq b, Show a, Show b, GNumSets a)=>SGr a b-> [ErrorTree]
errsTSG sg = 
   let err1 = faultsG "SG" (Just Partial) sg in
   let err2 = rIsInhTree sg in
   let err3 = rEtherealInherited sg in
   let err4 = rDerOk sg in
   let err5 = rEsCntsOk sg in 
   [err1, err2, err3, err4, err5]

rOkayTSG::(Eq a, Eq b, Show a, Show b, GNumSets a)=>String->SGr a b-> ErrorTree
rOkayTSG nm sg = reportWF sg nm okayTSG errsTSG

--okaySG' :: (Eq a, Eq b) => Maybe TK -> SGr a b -> Bool
--okaySG' (Just Total) = okayTSG 
--okaySG' (Just Partial) = okaySG 
--okaySG' Nothing = okaySGz

--check_wf_sg' :: (Eq a, Eq b, Show a, Show b) =>String -> Maybe TK -> SGr a b -> ErrorTree
--check_wf_sg' id (Just Total) = check_wf_tsg id
--check_wf_sg' id _            = check_wf_sg id  

instance G_WF_CHK SGr where
   okayG (Just Total) = okayTSG 
   okayG (Just Partial) = okaySG 
   okayG Nothing = okaySGz
   --faultsG :: (Eq a, Eq b, Show a, Show b) =>String -> Maybe TK -> SGr a b -> ErrorTree
   faultsG id (Just Total) = rOkayTSG id
   faultsG id (Just Partial) = rOkaySG id 
   faultsG id Nothing = rOkaySGz id

-- Checs whether SGs are disjoint
disjSGs :: (Eq a, Eq b) => [SGr a b] -> Bool
disjSGs sgs = disjGs (map g_sg sgs) 

-- Union of SGs
unionSG :: (Eq a, Eq b) => SGr a b -> SGr a b -> SGr a b
unionSG sg1 sg2 = 
   let ug = (g_sg sg1) `unionG` (g_sg sg2) in
   let u_nty = (nty sg1) `union` (nty sg2) in
   let u_ety = (ety sg1) `union` (ety sg2) in
   let u_srcm = (srcm sg1) `union` (srcm sg2) in
   let u_tgtm = (tgtm sg1) `union` (tgtm sg2) in
   let u_pe = (pe sg1) `union` (pe sg2) in
   let u_ds = (ds sg1) `union` (ds sg2) in
   let u_vceis = (vcei sg1) `union` (vcei sg2) in
   consSG ug u_nty u_ety u_srcm u_tgtm u_pe u_ds u_vceis

unionSGs :: (Eq b, Eq a) => [SGr a b] -> SGr a b
unionSGs sgs = 
   consSG (unionGs $ map g_sg sgs) 
      (gunion $ map nty sgs) 
      (gunion $ map ety sgs) 
      (gunion $ map srcm sgs) 
      (gunion $ map tgtm sgs) 
      (gunion $ map pe sgs) 
      (gunion $ map ds sgs)
      (gunion $ map vcei sgs)

-- SG subsumption
subsume_sg :: (Eq a, Eq b)=>SGr a b-> Rel a a -> SGr a b
subsume_sg sg sub 
   | pfun sub (nsP sg) (ns sg) = consSG s_g (dsub (nty sg) ((dom_of sub) `sminus` (ran_of sub))) (ety sg) (srcm sg) (tgtm sg) (pe sg) (ds sg) (vcei sg)
   | otherwise = sg
   where s_g = subsumeG (g_sg sg) sub 

-- Notion of allowed edge refinefEnts
-- allow_edge_ref::SGETy->SGETy->Bool
-- allow_edge_ref (Ecomp Dbi) (Ecomp Dbi) = True
-- allow_edge_ref (Ecomp Dbi) (Ecomp Duni) = True
-- allow_edge_ref (Erel Dbi) (Erel d) = d `elem` [Dbi, Duni]
-- allow_edge_ref (Erel Dbi) (Ewander) = True
-- allow_edge_ref (Erel Dbi) (Erel Duni) = True
-- allow_edge_ref (Ewander) b = is_val_edge_ref_of_wander b
-- allow_edge_ref a b = a == b

-- is_val_edge_ref_of_wander b = b `elem` ([e d | e<-[Erel, Ecomp], d<-[Dbi, Duni]] ++ [Ewander])
-- --[Erel Dbi, Erel Duni, Erel Duni,Ecomp Dbi, Ecomp DUni, E wander]


-- allowed_edge_refs::[(SGETy,SGETy)]
-- allowed_edge_refs = [(x, y) | x<-sgety_set, y<-sgety_set, allow_edge_ref x y]
--zip [Einh] [Einh]
--allowed_edge_refs @ekv(Ecomp _) = [Ecomp Bi, Ecomp Uni]
--allowed_edge_refs (Erel _) = [Erel Bi, Erel Uni]
--allowed_edge_refs (Ewander) = [Erel Bi, Erel Uni,Ecomp Bi, Ecomp Uni,Ewander]

commute_sgm_src::(GRM gm, Eq a, Eq b) => (SGr a b, gm a b, SGr a b) -> (Rel b a, Rel b a)
commute_sgm_src (sgs, m, sgt) = 
   let lhs = (fV m) `bcomp` (srcstm sgs) in  
   let rhs = (srcstm sgt) `bcomp` (fE m) in
   (lhs, rhs)

-- Checks whether the source function commutes for morphisms between SGs
morphism_sgm_commutes_src :: (GRM gm, Eq a, Eq b) => (SGr a b, gm a b, SGr a b) -> Bool
morphism_sgm_commutes_src (sgs, m, sgt) = 
   let (lhs, rhs) = commute_sgm_src (sgs, m, sgt) in
   lhs  <= rhs

commute_sgm_tgt (sgs, m, sgt) = 
   let lhs = (fV m) `bcomp` (tgtstm sgs) in  
   let rhs = (tgtstm sgt) `bcomp` (fE m) in
   (lhs, rhs)

-- Checks whether the target function commutes for morphisms between SGs
morphism_sgm_commutes_tgt :: (GRM gm, Eq a, Eq b) => (SGr a b, gm a b, SGr a b) -> Bool
morphism_sgm_commutes_tgt (sgs, m, sgt) = 
   let (lhs, rhs) = commute_sgm_tgt (sgs, m, sgt) in
   lhs  <= rhs

-- Checks whether the inheritance is preserved
ihh_sgm_ok (sgs, m, sgt) = ((fV m) `bcomp` (inhst sgs)) <= ((inhst sgt) `bcomp` (fV m))

-- Common aspects of both graph morphism settings which involve SGs
--is_wf_gm_common::(Eq a, Eq b) => (SGr a b, GrM a b,  SGr a b) -> Bool
okay_gm_common :: (GRM gm, GR g1, GR g2, Eq a, Eq b) =>(g1 a b, gm a b, g2 a b) -> Bool
okay_gm_common (gs, m, gt) = 
   -- is_wf Nothing gs && is_wf Nothing gt 
   tfun (fV m) (ns gs) (ns gt)  

okSGMCommon::(Eq a, Eq b) =>(SGr a b, GrM a b, SGr a b)->Bool
okSGMCommon (sgs, m, sgt) =
   okay_gm_common (sgs, m, sgt) && tfun (fE m) (esA sgs) (esA sgt)
   && morphism_sgm_commutes_src (sgs, m, sgt)
   && morphism_sgm_commutes_tgt (sgs, m, sgt)

-- checks whether a morphisms between SGs is well-formed
okSGM::(Eq a, Eq b) => (SGr a b, GrM a b,  SGr a b) -> Bool
okSGM (sgs, m, sgt) = 
   okSGMCommon (sgs, m, sgt) && ihh_sgm_ok (sgs, m, sgt)

errors_commuting :: (Eq a, Show a) =>(Set a, Set a)->String-> ErrorTree
errors_commuting (r1, r2) ty = 
   if r1 <= r2 then nile else consET ("Problems in commuting of " ++ ty ++ " functions") [reportSSEq r1 r2]

errs_gm_common :: (Show b, GRM gm, Eq a, Eq b, Show a, GR g1, GR g2) =>(g1 a b, gm a b, g2 a b) -> [ErrorTree]
errs_gm_common (gs, m, gt) =
   let err1 = if tfun (fV m) (ns gs) (ns gt) then nile else consET "Function 'fV' is ill defined." [reportFT (fV m) (ns gs) (ns gt)] in
   [err1]
   
errs_sgm_common :: (Show b, GRM gm, Eq a, Eq b, Show a) =>(SGr a b, gm a b, SGr a b) -> [ErrorTree]
errs_sgm_common (gs, m, gt) =
   --let err1 = faultsG "Source graph" Nothing gs in
   --let err2 = faultsG "Target Graph" Nothing gt in
   let errs = errs_gm_common (gs, m, gt) 
       err1 = if tfun (fE m) (esA gs) (esA gt) then nile else consET "Function 'fE' is ill defined." [reportFT (fE m) (esA gs) (esA gt)] 
       err2 = if morphism_sgm_commutes_src (gs, m, gt) then nile else errors_commuting (commute_sgm_src (gs, m, gt)) "source" 
       err3 = if morphism_sgm_commutes_tgt (gs, m, gt) then nile else errors_commuting (commute_sgm_tgt (gs, m, gt)) "target" in
   errs ++ [err1, err2, err3]

errOkSGM :: (Show b, Show a, GRM gm, Eq a, Eq b)=>(SGr a b, gm a b, SGr a b)->[ErrorTree]
errOkSGM (gs, m, gt) = 
   let errs1 = errs_sgm_common (gs, m, gt) in
   let err2 = if ihh_sgm_ok (gs, m, gt) then nile else consSET "Problems in commuting of inheritance relation" in
   errs1 ++ [err2]

rOkSGM::(Eq a, Eq b, Show a, Show b)=>String->SGr a b-> GrM a b->SGr a b->ErrorTree
rOkSGM nm sgs gm sgt = reportWF (sgs, gm, sgt) nm okSGM errOkSGM

-- Totalises a morphism for the derived edges
-- totaliseForDer m sg = cons_gm (fV m) ((mktotal_in (dres (eb sg) (esD sg)) (esC sg)) `rcomp` (fE m))

commute_gm_src::(Eq a, Eq b, GR g, GRM g) => (g a b, SGr a b) ->(Rel b a, Rel b a)
commute_gm_src (g, sg) = 
   let lhs = (fV g) `bcomp` (src g) in  
   let rhs = (srcstm sg) `bcomp` (fE  g) in
   (lhs, rhs)

-- Checks whether the source function commutes for morphisms from Gs to SGs
morphism_gm_commutes_src::(Eq a, Eq b, GR g, GRM g) => (g a b, SGr a b) -> Bool
morphism_gm_commutes_src (g, sg) = 
   let (lhs, rhs) = commute_gm_src (g, sg) in
   lhs  <= rhs

commute_gm_tgt::(Eq a, Eq b, GR g, GRM g) => (g a b, SGr a b) ->(Rel b a, Rel b a)
commute_gm_tgt (g, sg) = 
   let lhs = (fV g) `bcomp` (tgt g) 
       rhs = (tgtstm sg) `bcomp` (fE g) in
   (lhs, rhs)

-- Checks whether the target function commutes for morphisms from Gs to SGs
morphism_gm_commutes_tgt::(Eq a, Eq b, GR g, GRM g) => (g a b, SGr a b) -> Bool
morphism_gm_commutes_tgt (g, sg) = 
   let (lhs, rhs) = commute_gm_tgt (g, sg) in
   lhs  <= rhs

is_wf_gwt_sg:: (Eq a, Eq b, GR g, GRM g, GWT g) => (g a b, SGr a b) -> Bool
is_wf_gwt_sg (gwt, sg) = okay_gm_common (gOf gwt, ty gwt, sg)
   && tfun (fE gwt) (es gwt) (esA sg)
   && morphism_gm_commutes_src (gwt, sg)
   && morphism_gm_commutes_tgt (gwt, sg)

errors_gwt_sg::(Eq a, Eq b, Show a, Show b, GR g, GRM g, GWT g) => (g a b, SGr a b) -> [ErrorTree]
errors_gwt_sg (gwt, sg) =
   let errs1 = errs_gm_common (gOf gwt, ty gwt, sg) in
   let err2 = if tfun (fE gwt) (es gwt) (esA sg) then nile else consET ("Function 'fE' is ill defined." ++ (show $ fE gwt)++ (show $ esA sg)) [reportFT (fE gwt) (es gwt) (esA sg)] in
   let err3 = if morphism_gm_commutes_src (gwt, sg) then nile else errors_commuting (commute_gm_src (gwt, sg)) "source" in
   let err4 = if morphism_gm_commutes_tgt (gwt, sg) then nile else errors_commuting (commute_gm_tgt (gwt, sg)) "target" in 
   errs1 ++ [err2, err3, err4]

check_wf_gwt_sg :: (Eq a, Eq b, GR g, GRM g, GWT g, Show a, Show b) =>String -> g a b -> SGr a b -> ErrorTree
check_wf_gwt_sg nm gwt sg = reportWF (gwt, sg) nm (is_wf_gwt_sg) (errors_gwt_sg)

-- Gets instance nodes of a set of meta-nodes, which are obtained via the given morphism
ins::(Foldable t, Eq a,  Eq b, GRM gm)=>gm a b->SGr a b->t a->Set a
ins m sg mns = img (inv . fV $ m) (img (inv . inhst $ sg) mns)

-- Gets instance edges of set of meta-edges using the given morphism
ies::(Foldable t, Eq a,  Eq b, GRM gm)=>gm a b->t b->Set b
ies m mes = img (inv . fE $ m) mes

-- Builds instance graph restricted to the instances of a set of meta-edges
igRMEs::(Foldable t, Eq a, Eq b, GRM g, GR g, GWT g)=>g a b->t b->Gr a b
igRMEs gwt mes =  gwt `restrict` (ies (ty gwt) mes)

-- Builds instance graph restricted to the instances of set of meta-nodes and -edges
igRMNsEs::(Foldable t, Eq a, Eq b)=>GrwT a b->SGr a b->t a->t b->Gr a b
igRMNsEs gwt sg mns mes = (igRMEs gwt mes) `restrictNs` (ins (ty gwt) sg mns)

-- SG multiplicity refinement (leq == '<=')
sgs_mult_leq :: (GRM gm, Eq a, Eq b) =>SGr a b -> gm a b -> SGr a b -> b -> Bool
sgs_mult_leq sgc m sga e  = (appl (srcma sgc) e)  `mcsLeq` (appl ((srcma sga) `bcomp` (fE m)) e) 
                            && (appl (tgtm sgc) e) `mcsLeq` (appl ((tgtm sga) `bcomp` (fE m)) e)

refinesM :: (GRM gm, Eq a, Eq b) =>(SGr a b, gm a b) -> SGr a b -> Bool
refinesM (sgc, m) sga = all (sgs_mult_leq sgc m sga) (esA sgc)

--sg_refines_m' :: (GRM gm, Eq a, Eq b) =>(SGr a b, gm a b) -> SGr a b -> Bool
--sg_refines_m' (sgc, m) sga = all (sgs_mult_leq sgc m sga) (esA sgc)

--ok_src_nodes :: (GRM gm, Eq a, Eq b) =>SGr a b-> gm a b->SGr a b->b->b->Bool
--ok_src_nodes sgc m sga e e' = appl (fV m) (appl (src sgc) e') == appl (src sga) e

--ok_tgt_nodes :: (GRM gm, Eq a, Eq b) =>SGr a b->gm a b->SGr a b->b->b->Bool
--ok_tgt_nodes sgc m sga e e' = appl (fV m) (appl (tgt sgc) e') == appl (tgt sga) e

--src_m_ok sgc m sga e e' = 
--   let peas e = startEdg (appl (pe sga) e) in
--   appl (esMult (peas e) sgc) e' `mcsLeq` appl (srcma sga) e
--   where esMult (Edg _) sg = srcma sg 
--         esMult (Inv _) sg = tgtm sg 

--tgt_m_ok sgc m sga e e' = 
--   let peae e = endEdg (appl (pe sga) e)  in
--   appl (etMult (peae e) sgc) e' `mcsLeq` (appl (tgtm sga) e)
--   where etMult (Edg _) sg = tgtm sg 
--         etMult (Inv _) sg = srcma sg 

smf :: (Eq a, Eq b) => PEA e -> SGr a b -> Rel b Mult
smf (Edg _) sg = srcma sg 
smf (Inv _) sg = tgtm sg 
tmf :: (Eq a, Eq b) => PEA e -> SGr a b -> Rel b Mult
tmf (Edg _) sg = tgtm sg 
tmf (Inv _) sg = srcma sg 

sf :: (GR g, Eq a, Eq b) => PEA e -> g a b -> Rel b a
sf (Edg _) sg = src sg 
sf (Inv _) sg = tgt sg 
tf :: (GR g, Eq a, Eq b) => PEA e -> g a b -> Rel b a
tf (Edg _) sg = tgt sg 
tf (Inv _) sg = src sg 

affectedPEAStart::(GRM gm, Eq a, Eq b) =>SGr a b->gm a b->SGr a b->PEA b->b->b->Bool
affectedPEAStart sgc m sga pea e ie = ie `elem` (img (inv . fE $ m) [ePEA pea])
   && appl (fV m) (appl (sf pea sgc) ie) == appl (sf  pea sga) e

affectedPEAEnd::(GRM gm, Eq a, Eq b) =>SGr a b-> gm a b -> SGr a b ->PEA b->b->b->Bool
affectedPEAEnd sgc m sga pea e ie = ie `elem` (img (inv . fE $ m) [ePEA pea])
   && appl (fV m) (appl (tf pea sgc) ie) == appl (tf pea sga) e

affectedPECStart::(GRM gm, Eq a, Eq b) =>SGr a b-> gm a b-> SGr a b ->PEC a b ->b ->b->Bool
affectedPECStart sgc m sga (At pea) e ie = affectedPEAStart sgc m sga pea e ie
affectedPECStart sgc m sga (Dres v pea) e ie = 
   affectedPEAStart sgc m sga pea e ie 
   && any (\v'->(appl (sf  pea sga) ie, v') `elem` inhst sgc) (img (inv . fV $ m) [v]) 
affectedPECStart sgc m sga (Rres pea v) e ie = affectedPEAStart sgc m sga pea e ie && (appl (inv . fV $ m) (appl (tf  pea sga) e), appl (inv . fV $ m) v) `elem` inhst sga
affectedPEStart sgc m sga (Ec pec) e ie = affectedPECStart sgc m sga pec e ie 
affectedPEStart sgc m sga (SCmp pec _) e ie = affectedPECStart sgc m sga pec e ie 

affectedPECEnd::(GRM gm, Eq a, Eq b) =>SGr a b-> gm a b-> SGr a b ->PEC a b ->b ->b->Bool
affectedPECEnd sgc m sga (At pea) e ie = affectedPEAEnd sgc m sga pea e ie
affectedPECEnd sgc m sga (Dres v pea) e ie = affectedPEAEnd sgc m sga pea e ie && any (\v'->(appl (sf  pea sga) ie, v') `elem` inhst sgc) (img (inv . fV $ m) [v]) 
affectedPECEnd sgc m sga (Rres pea v) e ie = affectedPEAEnd sgc m sga pea e ie && (appl (inv . fV $ m) (appl (tf  pea sga) e), appl (inv . fV $ m) v) `elem` inhst sga
affectedPEEnd sgc m sga (Ec pec) e ie = affectedPECEnd sgc m sga pec e ie 
affectedPEEnd sgc m sga (SCmp _ pe) e ie = affectedPEEnd sgc m sga pe e ie 

affectedPE::(GRM gm, Eq a, Eq b) =>SGr a b-> gm a b-> SGr a b ->PE a b ->b ->b->b->Bool
affectedPE sgc m sga (Ec pec) e ie ie' = 
   ie == ie' && affectedPECStart sgc m sga pec e ie 
   && affectedPECEnd sgc m sga pec e ie
affectedPE sgc m sga (SCmp pec1 (Ec pec2)) e ie ie' = 
   appl (tf (endEAC pec1) sgc) ie == appl (sf (startEAC pec2) sgc) ie' 
   && affectedPECStart sgc m sga pec1 e ie && affectedPECEnd sgc m sga pec2 e ie'
affectedPE sgc m sga (SCmp pec pe) e ie ie' = 
   affectedPECStart sgc m sga pec e ie
   && any (\ie''->appl (tf (endEAC pec) sgc) ie == appl (sf (startEA pe) sgc) ie''
               && affectedPE sgc m sga pe e ie'' ie')(es sgc)

refines_mcnt::(GRM gm, Eq a, Eq b) =>SGr a b-> gm a b -> SGr a b ->b-> Bool
refines_mcnt sgc m sga e = 
   let peas e = startEA (appl (pe sga) e) 
       peae e = endEA (appl (pe sga) e) 
       --ok_src_nodes e e' = appl (fV m) (appl (sf (peas e) sgc) e') == appl (src sga) e
       --ok_tgt_nodes e e' = appl (fV m) (appl (tf (peae e) sgc) e') == appl (tgt sga) e
       src_m_ok e e' = appl (smf (peas e) sgc) e' `mcsLeq` appl (srcma sga) e
       tgt_m_ok e e' = appl (tmf (peae e) sgc) e' `mcsLeq` appl (tgtm sga) e
       src_ok e e' = appl (fV m) (appl (sf (peas e) sgc) e') == appl (src sga) e
       tgt_ok e e' = appl (fV m) (appl (tf (peae e) sgc) e') == appl (tgt sga) e 
       case1 e' e'' = (affectedPE sgc m sga (appl (pe sga) e) e e' e'') `implies` (src_m_ok e e' && tgt_m_ok e e'') 
       case2 e' = ((affectedPEStart sgc m sga (appl (pe sga) e) e e') && ((singles . msole_k $ 1) `mcsLeq` appl (tgtm sga) e)) `implies` tgt_ok e e'
       case3 e' = ((affectedPEEnd sgc m sga (appl (pe sga) e) e e') && ((singles . msole_k $ 1) `mcsLeq` appl (srcma sga) e)) `implies` src_ok e e' in
   all(\e'->all(\e''-> case1 e' e'' && (case2 e' || case3 e'')) (img (inv . fE $ m) [ePEA . peae $ e])) (img (inv . fE $ m) [ePEA . peas $ e])
   -- && all(\e'->all(\e''-> case2 e' || case3 e'') (img (inv . fE $ m) [ePEA . peae $ e])) (img (inv . fE $ m) [ePEA . peas $ e])
   --(ok_src_nodes e e' && ok_tgt_nodes e e'') 
--  where smf (Edg _) sg = srcma sg 
--         smf (Inv _) sg = tgtm sg 
--         tmf (Edg _) sg = tgtm sg 
--         tmf (Inv _) sg = srcma sg 
--         sf (Edg _) sg = src sg 
--         sf (Inv _) sg = tgt sg 
--         tf (Edg _) sg = tgt sg 
--         tf (Inv _) sg = src sg 

sg_refines_mcnts::(GRM gm, Eq a, Eq b) =>(SGr a b, gm a b)->SGr a b->Bool
sg_refines_mcnts (sgc, m) sga = all (refines_mcnt sgc m sga) $ esD sga
   
-- SG refinement of edge types
sgs_ety_leq::(GRM gm, Eq a, Eq b) =>SGr a b->gm a b->SGr a b->b->Bool
sgs_ety_leq sgc m sga e  = appl (ety sgc) e <= appl ((ety sga) `bcomp` (fE m)) e
sg_refines_ety::(GRM gm, Eq a, Eq b) =>(SGr a b, gm a b) -> SGr a b -> Bool
sg_refines_ety (sgc, m) sga = all (sgs_ety_leq sgc m sga) $ esA sgc

-- SG refinement of node types
sgs_nty_leq :: (GRM gm, Eq a, Eq b) =>SGr a b -> gm a b -> SGr a b -> a -> Bool
sgs_nty_leq sgc m sga n  = appl (nty sgc) n <= appl ((nty sga) `bcomp` (fV m)) n
sg_refines_nty::(GRM gm, Eq a, Eq b) =>(SGr a b, gm a b) -> SGr a b -> Bool
sg_refines_nty (sgc, m) sga = all (sgs_nty_leq sgc m sga) $ ns sgc

-- SG refinement conditions
sg_refinesz :: (GRM gm, Eq a, Eq b) => (SGr a b, gm a b) -> SGr a b -> Bool
sg_refinesz (sgc, m) sga = (sgc, m) `sg_refines_nty` sga 
   && (sgc, m) `sg_refines_ety`  sga 
   && (sgc, m) `refinesM` sga
   && (sgc, m) `sg_refines_mcnts` sga

-- SG refinement 
sg_refines :: (Eq a, Eq b) => (SGr a b, GrM a b) -> SGr a b -> Bool
sg_refines (sgc, m) sga = 
   okSGM (sgc, m, sga) && (sgc, m) `sg_refinesz` sga

-- Error checking for SG refinement
check_sg_refines_m :: (GRM gm, Eq a, Eq b, Show a, Show b) =>(SGr a b, gm a b) -> SGr a b -> ErrorTree
check_sg_refines_m (sgc, m) sga = 
   if (sgc, m) `refinesM` sga then nile else consSET $ "Errors with multiplicity refinement. The following concrete edes fail to comply with the abstract multplicity restrictions:" ++ (showElems' es)
   where es = filterS (not . sgs_mult_leq sgc m sga) (esA sgc)

check_sg_refines_mcnts::(GRM gm, Eq a, Eq b, Show a, Show b) =>(SGr a b, gm a b) -> SGr a b -> ErrorTree
check_sg_refines_mcnts (sgc, m) sga = 
   if (sgc, m) `sg_refines_mcnts` sga then nile else consSET $ "The following derived edges are not multiplicity-refined properly:" ++ (showEdges es)
   where es = filterS (not . refines_mcnt sgc m sga) (esD sga)

check_sg_refines_ety::(GRM gm, Eq a, Eq b, Show a, Show b) =>(SGr a b, gm a b) -> SGr a b -> ErrorTree
check_sg_refines_ety (sgc, m) sga = 
   if (sgc, m) `sg_refines_ety` sga then nile else consSET $ "Issues with edge type refinement for the following edges:" ++ (showEdges es_n_ref)
   where es_n_ref = filterS (not . sgs_ety_leq  sgc m sga) (esA sgc)

check_sg_refines_nty::(GRM gm, Eq a, Eq b, Show a, Show b) =>(SGr a b, gm a b) -> SGr a b -> ErrorTree
check_sg_refines_nty (sgc, m) sga = 
   if (sgc, m) `sg_refines_nty` sga then nile else consSET $ "Certain instance nodes fail to preserve their type kinds: " ++ (showNodes ns_n_ref)
   where ns_n_ref = filterS (not . sgs_nty_leq sgc m sga) (ns sgc)

errs_sg_refinesz (sgc, m) sga = 
   let err1 = check_sg_refines_nty (sgc, m) sga in
   let err2 = check_sg_refines_ety (sgc, m) sga in
   let err3 = check_sg_refines_m (sgc, m) sga in
   let err4 = check_sg_refines_mcnts (sgc, m) sga in
   [err1, err2, err3, err4]

-- errors of SG refinement
errs_sg_refines id (sgc, m, sga) = 
   --let m' = totaliseForDer m sgc in 
   let err1 = rOkSGM id sgc m sga in
   let errs2 = errs_sg_refinesz (sgc, m) sga in
   (err1:errs2)

check_sg_refines id (sgc, m) sga = reportWF (sgc, m, sga) id sg_refines' (errs_sg_refines id)
   where sg_refines' (sgc, m, sga) = (sgc, m) `sg_refines` sga

-- Total SG refinement of abstract nodes
is_refined :: (GRM gm, Eq a, Eq b1, Eq b2) => gm a b2 -> SGr a b1 -> a -> Bool
is_refined m sga n = not . null $ (img (inhst sga) [n]) `intersec` (ran_of  $ fV m)
tsg_refines_ans :: (GRM gm, Eq a, Eq b, Eq b2) => gm a b2 -> SGr a b -> Bool
tsg_refines_ans m sga = all (\nn-> is_refined m sga nn) (nsTys sga [Nnrml])

-- Total SG refinement of abstract edges
tsg_refines_aes::(Eq a, Eq b)=>(SGr a b, GrM a b)->SGr a b->Bool
tsg_refines_aes (sgc, m) sga = all (\me->(sga, me) `okRefinedIn` (sgc, m)) (esA sga)

-- Checks if the instance relation is refined correctly
okRefinedIn::(Eq a, Eq b)=>(SGr a b, b)->(SGr a b, GrM a b)->Bool
okRefinedIn (sga, me) (sgc, m) = 
   let r = (inhst sgc) `rcomp` (relOfG $ igRMEs (consGWT (g_sg sgc) m) [me]) `rcomp` (inv . inhst $ sgc) in
   let s = (ins m sga $ img (src sga) [me]) `sminus`  (nsEther sgc `sminus` dom_of r) in
   let t = (ins m sga $ img (tgt sga) [me]) `sminus` (nsEther sgc `sminus` ran_of r) in
   (relation r s t) && (not . null) (img (nty sga) ((nsIncident sga [me]) `sminus` (nsVi sga))) `implies` (not . null $ r)
-- && (not . null $ r) 

-- Total SG refinement conditions
tsg_refinesz::(Eq a, Eq b)=>(SGr a b, GrM a b)->SGr a b->Bool
tsg_refinesz (sgc, m) sga = 
   (sgc, m) `sg_refinesz` sga && (sgc, m) `tsg_refines_aes` sga && m `tsg_refines_ans` sga

-- Total SG refinement
tsg_refines::(Eq a, Eq b)=>(SGr a b, GrM a b)->SGr a b->Bool
tsg_refines (sgc, m) sga = 
   okSGM (sgc, m, sga) && (sgc, m) `tsg_refinesz` sga 

-- Errors checking
-- errors of SG refinement of abstract nodes
check_tsg_refines_ans :: (Show a, GRM gm, Eq a, Eq b) =>gm a b -> SGr a b -> ErrorTree
check_tsg_refines_ans m sga = 
   if m `tsg_refines_ans` sga then nile else consSET $ "The following normal nodes are not refined: " ++ (showNodes nns_n_ref)
   where nns_n_ref = filterS (\nn-> not $ is_refined m sga nn) (nsTys sga $ singles Nnrml)

check_tsg_refines_aes::(Eq a, Eq b, Show a, Show b)=>(SGr a b, GrM a b)->SGr a b->ErrorTree
check_tsg_refines_aes (sgc, m) sga =
   if (sgc, m) `tsg_refines_aes` sga then nile else consSET $ "Certain association edges are incorrectly refined: " ++ (showEdges aes_nref)
   where aes_nref = filterS (\me-> not $ (sga, me) `okRefinedIn` (sgc, m)) (esA sga)

errs_tsg_refinesz::(Eq a, Eq b, Show a, Show b)=>(SGr a b, GrM a b)->SGr a b->[ErrorTree]
errs_tsg_refinesz (sgc, m) sga =
   let errs1 = errs_sg_refinesz (sgc, m) sga in
   let err2 = check_tsg_refines_ans m sga in
   let err3 = check_tsg_refines_aes (sgc, m) sga in
   errs1 ++ [err2, err3]

check_tsg_refines::(Eq a, Eq b, Show a, Show b)=>String->(SGr a b, GrM a b)->SGr a b->ErrorTree
check_tsg_refines id (sgc, m) sga = 
   let err1 = rOkSGM id sgc m sga in
   let errs2 = errs_tsg_refinesz (sgc, m) sga in
   if (sgc, m) `tsg_refines` sga then nile else consET "Errors in total SG refinement" (err1:errs2)


-- Checks that 'abstract' and 'enum' mEtamodel nodes have no direct nodes in instance graph
no_instances_of_abstract_tnodes m sgt = null (img (inv $ fV m) $ nsTys sgt [Nabst, Nenum])

-- ET Compatability with respect to extra typing

-- multiplicities of source SG must be included in those of target SG
mssgsLEq :: (GRM gm, Eq a, Eq b) =>SGr a b ->gm a b ->SGr a b->(b, b)-> Bool
mssgsLEq sgs m sgt (e, e') = appl (srcma sgs) e <= appl (srcma sgt) e'
                       && appl (tgtm sgs) e <= appl (tgtm sgt) e'

-- Compliance of multiplicities for extra typing
etCompliesM::(GRM gm, Eq a, Eq b)=>(SGr a b, gm a b)->SGr a b ->Bool 
etCompliesM (sgs, m) sgt = all (mssgsLEq sgs m sgt) (fE m)
   --dres (srcma sgt) (dom_of . fE $ m) <= (srcma sgs `bcomp` fE m)
   -- && dres (tgtm sgt) (dom_of . fE $ m) <= (tgtm sgs `bcomp` fE m)
   --

retCompliesM :: (GRM gm, Eq a, Eq b, Show a, Show b) =>(SGr a b, gm a b) -> SGr a b -> ErrorTree
retCompliesM (sgs, m) sgt = 
   if (sgs, m) `etCompliesM` sgt then nile else consSET $ "Errors with multiplicity strict refinement. The following edes fail to comply with the multplicity restrictions of the target SG:" ++ (showElems' esm)
   where es = filterS (not . mssgsLEq sgs m sgt) (fE m)
         esm = foldr (\(e, e') es'->((e, appl (srcma sgs) e, appl (tgtm sgs) e), (e', appl (srcma sgt) e', appl (tgtm sgs) e')):es') nil es

-- For extra typing compliance, node types must be preserved 
sgsNtyEq :: (Eq a, Eq b) =>SGr a b->a-> Bool
sgsNtyEq sgt n = appl (nty sgt) n `elem` [Nnrml, Nabst, Nvirt]

okTNtys::(GRM gm, Eq a, Eq b) =>gm a b->SGr a b-> Bool
okTNtys m sgt = img (nty sgt) (ran_of . fV $ m) <= set [Nnrml, Nabst, Nvirt]
   --dres (nty sgs) (dom_of . fV $ m) == (nty sgt `bcomp` fV m) --all (msgsNtyEq sgs m sgt) 

rOkNtys::(GRM gm, Eq a, Eq b, Show a) =>gm a b->SGr a b-> ErrorTree
rOkNtys m sgt = if okTNtys m sgt then nile else consSET $ "The types of certain target nodes are not allowed for extra typing: " ++ (showNodes ns_n_ref)
   where ns_n_ref = filterS (not . sgsNtyEq sgt) (ran_of . fV $ m)

--retCompliesNty::(GRM gm, Eq a, Eq b, Show a, Show b)=>(SGr a b, gm a b)->SGr a b->ErrorTree
--retCompliesNty (sgs, m) sgt = 
--   if (sgs, m) `etCompliesNty` sgt then nile else consSET $ "Certain source nodes fail to preserve their type kinds: " ++ (showNodes ns_n_ref)
--   where ns_n_ref = filterS (not . sgsNtyEq sgs sgt) (fV m)

-- For extra typing compliance, edge types must be preserved 
sgsEtyEq :: (GRM gm, Eq a, Eq b) =>SGr a b -> gm a b -> SGr a b -> b -> Bool
sgsEtyEq sgs m sgt e  = appl (ety sgs) e == appl (ety sgt `bcomp` fE m) e
etCompliesEty::(GRM gm, Eq a, Eq b) =>(SGr a b, gm a b) -> SGr a b -> Bool
etCompliesEty (sgs, m) sgt = dres (ety sgs) (dom_of . fE $ m) == (ety sgt `bcomp` fE m) --all (msgsEtyEq sgs m sgt) 

retCompliesEty::(GRM gm, Eq a, Eq b, Show a, Show b) =>(SGr a b, gm a b) -> SGr a b -> ErrorTree
retCompliesEty (sgs, m) sgt = 
   if (sgs, m) `etCompliesEty` sgt then nile else consSET $ "Certain edge nodes fail to preserve their type kinds:" ++ (showEdges es_n_ref)
   where es_n_ref = filterS (not . sgsEtyEq  sgs m sgt) (dom_of . fE $ m)

commutePPairSGsS :: (GRM gm, Eq a, Eq b) =>SGr a b-> gm a b-> SGr a b -> (Rel b a, Rel b a)
commutePPairSGsS sgs m sgt = 
   let lhs = (fV m) `bcomp` (dres (srcstm sgs) (dom_of . fE $ m))
       rhs = (srcstm sgt) `bcomp` (fE m) in
   (lhs, rhs)

commutePSGsS::(GRM gm, Eq a, Eq b)=>SGr a b->gm a b->SGr a b-> Bool
commutePSGsS sgs m sgt = 
   let (lhs, rhs) = commutePPairSGsS sgs m sgt in
   lhs  <= rhs

commutePPairSGsT :: (GRM gm, Eq a, Eq b) =>SGr a b-> gm a b-> SGr a b -> (Rel b a, Rel b a)
commutePPairSGsT sgs m sgt = 
   let lhs = (fV m) `bcomp` (dres (tgtstm sgs) (dom_of . fE $ m))  
       rhs = (tgtstm sgt) `bcomp` (fE m) in
   (lhs, rhs)

commutePSGsT::(GRM gm, Eq a, Eq b)=>SGr a b->gm a b->SGr a b-> Bool
commutePSGsT sgs m sgt = 
   let (lhs, rhs) = commutePPairSGsT sgs m sgt in
   lhs  <= rhs

okPSGM::(Eq a, Eq b) =>(SGr a b, GrM a b, SGr a b)->Bool
okPSGM (sgs, m, sgt) =
   pfun (fV m) (ns sgs) (ns sgt)
   && pfun (fE m) (esA sgs) (esA sgt)
   && commutePSGsS sgs m sgt
   && commutePSGsT sgs m sgt

errsOkPSGM:: (Show b, GRM gm, Eq a, Eq b, Show a) =>(SGr a b, gm a b, SGr a b)-> [ErrorTree]
errsOkPSGM (sgs, m, sgt) =
   let err1 = if pfun (fV m) (ns sgs) (ns sgt) then nile else consET "Function 'fV' is ill defined." [reportPF (fV m) (ns sgs) (ns sgt)] 
       err2 = if pfun (fE m) (esA sgs) (esA sgt) then nile else consET "Function 'fE' is ill defined." [reportPF (fE m) (esA sgs) (esA sgt)] 
       err3 = if commutePSGsS sgs m sgt then nile else errors_commuting (commutePPairSGsS sgs m sgt) "source" 
       err4 = if commutePSGsT sgs m sgt then nile else errors_commuting (commutePPairSGsT sgs m sgt) "target" in
   [err1, err2, err3]

rOkPSGM::(Eq a, Eq b, Show a, Show b) =>String->(SGr a b, GrM a b, SGr a b)->ErrorTree
rOkPSGM id (sgs, m, sgt) = reportWF (sgs, m, sgt) id okPSGM errsOkPSGM

-- Actual WF definition of extra typing of SGs: 
-- (i) there is a partial morphism, and strict refinements of (ii) multiplicity, 
-- and (iii) node and (iv) edge types
okETSGs::(Eq a, Eq b) =>(SGr a b, GrM a b) -> SGr a b -> Bool
okETSGs (sgs, m) sgt = okPSGM (sgs, m, sgt) 
   && (sgs, m) `etCompliesM` sgt 
   && okTNtys m sgt 
   && (sgs, m) `etCompliesEty` sgt

errsOkayETSGs::(Eq a, Eq b, Show a, Show b)=>String->(SGr a b, GrM a b, SGr a b)->[ErrorTree]
errsOkayETSGs id (sgs, m, sgt) =
   let errs = errsOkPSGM (sgs, m, sgt)
   --if pfun (fV m) (ns sgs) (ns sgt) then nile else consET "Function 'fV' is ill defined." [reportPF (fV m) (ns sgs) (ns sgt)] in
       err2 = retCompliesM (sgs, m) sgt 
       err3 = rOkNtys m sgt 
       err4 = retCompliesEty  (sgs, m) sgt in
   errs ++ [err2, err3, err4]

rOkETSGs ::(Eq a, Eq b, Show a, Show b)=>String->(SGr a b, GrM a b)->SGr a b->ErrorTree
rOkETSGs id (sgs, m) sgt = reportWF (sgs, m, sgt) id okayETSGs' (errsOkayETSGs id)
   where okayETSGs' (sgs, m, sgt) = (sgs, m) `okETSGs` sgt

-- Checks whether an edge is instantiated invertedly, which is permitted for wander edges
--inverted_ie gwt sg e = applM ((tgt sg) `bcomp` (fE . ty $ gwt)) e == applM ((fV . ty $ gwt) `bcomp` (src sg)) e

-- Gets the instance graph restricted to a wander edge
--gOfwei :: (Eq a, Eq b, GR g) => GrwT a b -> g a b -> b -> Gr a b
--gOfwei gwt sg e = 
--   let g' = gOf gwt in
--   if inverted_ie gwt sg e then invertG g' else g'

-- Gets instance graph restricted to a set of wander edges
--gOfweis :: (Eq b, Eq a, GR g) => GrwT a b -> g a b -> [b] -> Gr a b
--gOfweis gwt sg []     = empty
--gOfweis gwt sg (e:es) = gOfwei gwt sg e `unionG` gOfweis gwt sg es

-- Gets an instance graph restricted to a meta-edge
--igRMEsW::(Eq a, Eq b)=>GrwT a b->SGr a b->b->Gr a b
--igRMEsW gwt sg me 
--   | me `elem` esD sg = igRMNsEs gwt sg [appl (src sg) me, appl (tgt sg) me] [appl (eb sg) me]
--   | me `elem` esW sg =  gOfweis gwt sg (img (inv $ (fE . ty $ gwt)) [me])
--   | otherwise = igRMEs gwt [me]
--okay_sgm'::(Eq a, Eq b)=>Maybe MK->(SGr a b, GrM a b, SGr a b)->Bool
--okay_sgm' Nothing = okSGM
--okay_sgm' (Just WeakM) = okSGM
--okay_sgm' (Just PartialM) = (\(sgc, m, sga)->(sgc, m) `sg_refines` sga)
--okay_sgm' (Just TotalM) = (\(sgc, m, sga)->(sgc, m) `tsg_refines` sga)

--rokay_gm_g'::(Eq a, Eq b, Show a, Show b)=>String->Maybe MK->(SGr a b, GrM a b, SGr a b)->ErrorTree
--rokay_gm_g' id Nothing (sgc, m, sga)= rOkSGM id sgc m sga
--rokay_gm_g' id (Just WeakM) (sgc, m, sga) = rOkSGM id sgc m sga
--rokay_gm_g' id (Just  PartialM) (sgc, m, sga) = check_sg_refines id (sgc, m) sga
--rokay_gm_g' id (Just TotalM) (sgc, m, sga) = check_tsg_refines id (sgc, m) sga

instance GM_CHK SGr SGr where
      okayGM Nothing = okSGM
      okayGM (Just WeakM) = okPSGM
      okayGM (Just PartialM) = (\(sgc, m, sga)->(sgc, m) `sg_refines` sga)
      okayGM (Just TotalM) = (\(sgc, m, sga)->(sgc, m) `tsg_refines` sga)
      faultsGM id Nothing (sgc, m, sga)= rOkSGM id sgc m sga
      faultsGM id (Just WeakM) (sgc, m, sga) = rOkPSGM id (sgc, m, sga)
      faultsGM id (Just  PartialM) (sgc, m, sga) = check_sg_refines id (sgc, m) sga
      faultsGM id (Just TotalM) (sgc, m, sga) = check_tsg_refines id (sgc, m) sga

--
-- SG Type conformance

-- Instances of compounds are not allowed to share parts
tyCompliesPNS::(Eq a, Eq b, GRM g, GR g, GWT g)=>g a b->SGr a b->Bool
tyCompliesPNS gwt sg = injective $ relOfG (igRMEs gwt (esTys sg [Ecomp Dbi, Ecomp Duni]))

checkTyCompliesPNS::(Eq a, Eq b, Show a, Show b, GRM g, GR g, GWT g)=>g a b->SGr a b->ErrorTree
checkTyCompliesPNS gwt sg = 
   let r = relOfG $ igRMEs gwt (esTys sg [Ecomp Dbi, Ecomp Duni]) in
   if gwt `tyCompliesPNS` sg then nile else consET "Parts are being shared by compounds:" [reportI r]

-- Instances of ethereal nodes are not allowed
insEther :: (GRM gm, Eq a, Eq b) => gm a b -> SGr a b ->Set a
insEther gwt sg = img (inv . fV $ gwt) $ nsEther sg

-- Forbidden instances (FI)
tyCompliesFI::(Eq a, Eq b, GRM g)=>g a b->SGr a b->Bool
tyCompliesFI gwt sg = null $ insEther gwt sg

insEtherPairs :: (GRM gm, Eq a, Eq b) => gm a b -> SGr a b ->Rel a a
insEtherPairs gwt sg = foldr (\ne ps->fmap (flip pair_up $ ne) (img ((inv . fV) $ gwt) (singles ne)) `union` ps) nil $ nsEther sg

checkTyCompliesFI :: (Eq a, Eq b, Show a, GRM g)=>g a b -> SGr a b -> ErrorTree
checkTyCompliesFI gwt sg = 
   if tyCompliesFI gwt sg then nile else consSET $ "Error! There are the following ethereal nodes instances:" ++ (show_pairs (insEtherPairs gwt sg))
   where show_pairs EmptyS = ""
         show_pairs (p `Set` ps) = (showP p)++(show_pairs ps) 
         showP (x, y) = (show x)++ "->" ++(show y)


-- Builds a relation from a path expression atom
rPEA :: (Eq a, Eq b, GR g, GRM g) =>g a b -> SGr a b -> PEA b -> Rel a a 
rPEA gwt sg (Edg e) = relOfG $ restrict gwt (ies gwt [e])
rPEA gwt sg (Inv e) = inv. relOfG $ restrict gwt (ies gwt [e])
   --inv . relOfG $ restrict gwt [e]

-- Builds a relation from a path expression atom
rPEC :: (Eq a, Eq b, GR g, GRM g) =>g a b -> SGr a b -> PEC a b ->Rel a a
rPEC gwt sg (At pea) = rPEA gwt sg pea
rPEC gwt sg (Dres v pea) = dres (rPEA gwt sg pea) $ ins gwt sg [v]
rPEC gwt sg (Rres pea v) = rres (rPEA gwt sg pea) $ ins gwt sg [v]
rPE :: (Eq a, Eq b, GR g, GRM g) =>g a b -> SGr a b -> PE a b ->Rel a a
rPE gwt sg (Ec pec) = rPEC gwt sg pec
rPE gwt sg (SCmp pec pe) = (rPEC gwt sg pec) `rcomp` (rPE gwt sg pe)

ape :: (Eq a, Eq b) => SGr a b -> b -> PE a b
ape sg e = if e `elem` esCnt sg then appl (pe sg) e else (Ec . At . Edg $ e) 

multComp ::Mult -> Mult -> Mult
multComp m1 m2
   | isMultMany m1 || isMultMany m2       = singles msole_many
   | isMultVal_k m1 0 || isMultVal_k m2 0 = singles (msole_k 0)
   | isMultVal_k m1 1 = m2
   | isMultVal_k m2 1 = m1
   | isMultOpt m1 = msole_k 0 `intoSet` m2
   | isMultOpt m2 = msole_k 0 `intoSet` m1
   | isMultRange m1 && isMultRange m2 = singles $ (the m1) `mult_mr` (the m2)
   | isMultEither m2 = multComp m1 (singles $ the m2) `union` multComp m1 (rest m2)
   | isMultEither m1 = multComp (singles $ the m1) m2 `union` multComp (rest m1) m2

-- gives source multiplicity of path expression atom
smPEA :: (Eq a, Eq b) => SGr a b -> PEA b -> Mult
smPEA sg (Edg e) = appl (srcma sg) e
smPEA sg (Inv e) = appl (tgtm sg) e

-- source multiplicity of path expression 
smPEC :: (Eq a, Eq b) => SGr a b -> PEC a b -> Mult
smPEC sg (At pea) = smPEA sg pea
smPEC sg (Dres v pea) = smPEA sg pea
smPEC sg (Rres pea v) = smPEA sg pea

smPE :: (Eq a, Eq b) => SGr a b -> PE a b -> Mult
smPE sg (Ec pec) = smPEC sg pec
smPE sg (SCmp pec pe) = multComp (smPEC sg pec)  (smPE sg pe)

-- target multiplicity of path expression atom
tmPEA :: (Eq a, Eq b) => SGr a b -> PEA b -> Mult
tmPEA sg (Edg e) = appl (tgtm sg) e
tmPEA sg (Inv e) = appl (srcma sg) e

-- gives target multiplicity of path expression 
tmPEC :: (Eq a, Eq b) => SGr a b -> PEC a b -> Mult
tmPEC sg (At pea) = tmPEA sg pea
tmPEC sg (Dres v pea) = tmPEA sg pea
tmPEC sg (Rres pea v) = tmPEA sg pea
tmPE :: (Eq a, Eq b) => SGr a b -> PE a b -> Mult
tmPE sg (Ec pec) = tmPEC sg pec
tmPE sg (SCmp pec pe) = multComp (tmPEC sg pec)  (tmPE sg pe)

-- 'srcst' relation of a PEA
srcstPEA :: (Eq a, Eq b) => SGr a b -> PEA b ->Rel b a
srcstPEA sg (Edg _) = srcst sg
srcstPEA sg (Inv _) = tgtst sg

-- 'srcst' relation of a PE restricted to a particular node
srcstPEC :: (Eq a, Eq b) => SGr a b -> PEC a b->Rel b a
srcstPEC sg (At pea) = srcstPEA sg pea
srcstPEC sg (Dres v pea) = rres (srcstPEA sg pea) [v]
srcstPEC sg (Rres pea _) = srcstPEA sg pea
srcstPE :: (Eq a, Eq b) => SGr a b -> PE a b->Rel b a
srcstPE sg (Ec pec) = srcstPEC sg pec
srcstPE sg (SCmp pec pe) = srcstPEC sg pec

-- 'tgtst' relation of a PEA 
tgtstPEA :: (Eq a, Eq b) => SGr a b -> PEA b ->Rel b a
tgtstPEA sg (Edg e) = tgtst sg
tgtstPEA sg (Inv e) = srcst sg

-- 'tgtst' relation of a PE restricted to a particular node
tgtstPEC :: (Eq a, Eq b) => SGr a b -> PEC a b->Rel b a
tgtstPEC sg (At pea) = tgtstPEA sg pea
tgtstPEC sg (Dres _ pea) = tgtstPEA sg pea
tgtstPEC sg (Rres pea v) = rres (tgtstPEA sg pea) [v]
tgtstPE :: (Eq a, Eq b) => SGr a b -> PE a b->Rel b a
tgtstPE sg (Ec pec) = tgtstPEC sg pec
tgtstPE sg (SCmp pec pe) = tgtstPE sg pe

-- gives target of path expression atom
tPEA :: (Eq a, Eq b) => SGr a b -> PEA b -> a
tPEA sg (Edg e) = appl (tgt sg) e
tPEA sg (Inv e) = appl (src sg) e

-- gives target of path expression
tPEC :: (Eq a, Eq b) => SGr a b -> PEC a b -> a
tPEC sg (At pea) = tPEA sg pea
tPEC sg (Dres v pea) = tPEA sg pea
tPEC sg (Rres pea v) = tPEA sg pea
tPE :: (Eq a, Eq b) => SGr a b -> PE a b -> a
tPE sg (Ec pec) = tPEC sg pec
tPE sg (SCmp pec pe) = tPE sg pe

-- Builds relation to be subject to the multiplicity check
rMultOk :: (Eq a, Eq b, GR g, GRM g) => SGr a b -> b -> g a b ->Rel a a
rMultOk sg me gwt = 
   let s = ins gwt sg $ img (srcst sg) [me] in
   let t = ins gwt sg $ img (tgtst sg) [me] in
   rres (dres (rPE gwt sg $ ape sg me) s) t

-- Builds 'srcst' relation to be used in the multiplicity check
srcstMultOk :: (Eq a, Eq b) => SGr a b -> b ->Rel b a
srcstMultOk sg me = rres (srcstPE sg (ape sg me)) (img (srcst sg) [me])

-- Builds 'tgtst' relation to be used in the multiplicity check
tgtstMultOk :: (Eq a, Eq b) => SGr a b -> b ->Rel b a
tgtstMultOk sg me = rres (tgtstPE sg (ape sg me)) (img (tgtst sg) [me])

-- Checks whether appropriate instances of a SG comply to the meta-edges's multiplicity constraints
meMultOk::(Eq a, Eq b)=>SGr a b->b->GrwT a b->Bool
meMultOk sg me gwt = 
   let r = rMultOk sg me gwt in
   let s = ins gwt sg $ img (srcstMultOk sg me) [rsrcPE $ ape sg me] in
   let t = ins gwt sg $ img (tgtstMultOk sg me) [rtgtPE $ ape sg me] in
   multOk r s t (appl (srcma sg) me) (appl (tgtm sg) me)

checkMEMultOk::(Eq a, Eq b, Show a, Show b)=>SGr a b->b->GrwT a b->ErrorTree
checkMEMultOk sg me gwt = 
   let r = rMultOk sg me gwt in
   let s = ins gwt sg $ img (srcstMultOk sg me) [rsrcPE $ ape sg me] in
   let t = ins gwt sg $ img (tgtstMultOk sg me) [rtgtPE $ ape sg me] in
   check_multOk me r s t (appl (srcma sg) me) (appl (tgtm sg) me)

-- Multiplicity compliance of all multiplicity edges (association plus derived edges)
tyCompliesMult::(Eq a, Eq b)=>GrwT a b->SGr a b->Bool
tyCompliesMult gwt sg = all (\me->meMultOk sg me gwt) $ esM sg

checkTyCompliesMult :: (Eq a, Eq b, Show a, Show b) => GrwT a b -> SGr a b -> ErrorTree
checkTyCompliesMult gwt sg = 
   if tyCompliesMult gwt sg then nile else consET "Multiplicity breached in instance model." errs
   where errs = foldr (\me errs ->(checkMEMultOk sg me gwt):errs) [] (esM sg)

-- Checks that numeric constraints are satisfied for natural numbers

-- Gets natural number node instances
natIs::(Eq a, Eq b, GNumSets a)=>GrwT a b->Set a
natIs gwt = img (inv . fV $ gwt) (singles nNatS)

-- Checks that a node complies to the natural number constraints
okNatI::(Read a, GNodesNumConv a)=>a->Bool
okNatI nn = isSomething on && the on >= 0
   where on = toInt nn

okINats::(Eq a, Eq b, Read a, GNodesNumConv a, GNumSets a)=>GrwT a b->Bool
okINats gwt = all okNatI (natIs gwt)

errINats::(Eq a, Eq b, Show a, Show b, Read a, GNodesNumConv a, GNumSets a)
   =>GrwT a b -> ErrorTree
errINats gwt = 
   let errNs  = filterS (not . okNatI) (natIs gwt)
       emsg = "Instance nodes which fail to satisfy the natural number constraints:" ++ (showElems' errNs) in
   if okINats gwt then nile else consSET emsg

-- Checks that numeric constraints are satisfied for integers 

-- Gets the integer node instances
intIs::(Eq a, Eq b, GNumSets a)=>GrwT a b->Set a
intIs gwt = img (inv . fV $ gwt) (singles nIntS)

-- Checks that a node complies to the integer contraints
okIntI::(Read a, GNodesNumConv a)=>a->Bool
okIntI = isSomething . toInt

okIInts::(Eq a, Eq b, Read a, GNodesNumConv a, GNumSets a)=>GrwT a b->Bool
okIInts gwt = all okIntI (intIs gwt)

errIInts::(Eq a, Eq b, Show a, Show b, Read a, GNodesNumConv a, GNumSets a)
   =>GrwT a b -> ErrorTree
errIInts gwt = 
   let errIs  = filterS (not . okIntI) (intIs gwt)
       emsg = "Instance nodes which fail to satisfy the integer constraints:" ++ (showElems' errIs) in
   if okIInts gwt then nile else consSET emsg

-- Checks that numeric constraints are satisfied for reals
-- Gets the reals node instances
realIs::(Eq a, Eq b, GNumSets a)=>GrwT a b->Set a
realIs gwt = img (inv . fV $ gwt) (singles nRealS)

-- Checks that a node complies to the real contraints
okRealI::(Read a, GNodesNumConv a)=>a->Bool
okRealI = isSomething . toReal

okIReals::(Eq a, Eq b, Read a, GNodesNumConv a, GNumSets a)=>GrwT a b->Bool
okIReals gwt = all okRealI (realIs gwt)

errIReals::(Eq a, Eq b, Show a, Show b, Read a, GNodesNumConv a, GNumSets a)
   =>GrwT a b -> ErrorTree
errIReals gwt = 
   let errIs  = filterS (not . okRealI) (realIs gwt)
       emsg = "Instance nodes which fail to satisfy the real number constraints:" ++ (showElems' errIs) in
   if okIReals gwt then nile else consSET emsg

-- Checks that a GWT complies to the numeric constraints set by the type
okINumbers::(Eq a, Eq b, Read a, GNodesNumConv a, GNumSets a)=>GrwT a b->Bool
okINumbers gwt = okINats gwt && okIInts gwt && okIReals gwt

rOp::(Eq a, Ord a)=>SGVCEOP->a->a->Bool
rOp Eq n1 n2 = n1 == n2
rOp Neq n1 n2 = n1 /= n2
rOp Leq n1 n2 = n1 <= n2
rOp Geq n1 n2 = n1 >= n2
rOp Lt n1 n2 = n1 < n2
rOp Gt n1 n2 = n1 > n2

toNum::SGr a b->gm a b->a->Maybe (Either Int Float)
toNum sg t n = 
   let cond = n `elem` dom_of (fV t) && ((appl (fV t) n, nNatS) `elem` inhst sg || (appl (fV t) n, nNatS) `elem` inhst sg) in
   if cond then fmap Left (toInt n) else fmap Right (toReal n)

satisfiesACnt::GRM gm=>SGr a b->gm a b->a->SGVCEOP->a->Bool
satisfiesACnt sg t ns op nt = 
   let ons = toNum sg t ns 
       ont = toNum sg t nt 
       bothInt = isInt ons && isInt ont 
       bothReal = isReal ons && isReal ont in
   if bothInt then rOp op (gInt ons) (gInt ont) else bothReal && rOp op (gReal ons) (gReal ont)
   where
      isInt (Just (Left _)) = True
      isInt _ = False
      isReal (Just (Right _)) = True
      isReal _ = False
      gInt (Just (Left n)) = n
      gReal (Just (Right x)) = x

satisfiesVCEECnt::(Eq a, Eq b)=>SGr a b->GrwT a b->b->Bool
satisfiesVCEECnt sg gwt vce = 
   let ns e = appl (tgt gwt) e
       op = fst . appl (vcei sg) $ vce 
       nt = appl (tgt sg) vce in
   all (\e->satisfiesACnt sg (ty gwt) (ns e) op nt) (img (inv . fE $ gwt) (maybeToSet . snd . appl (vcei sg) $ vce))

satisfiesVCENCnt::(Eq a, Eq b)=>SGr a b->GrwT a b->b->Bool
satisfiesVCENCnt sg gwt vce = 
   let op = fst . appl (vcei sg) $ vce 
       nt = appl (tgt sg) vce in
   all (\n->satisfiesACnt sg (ty gwt) n op nt) (img (inv . fV $ gwt) $ singles (appl (src sg) $ vce))

ivcesOk::(Eq a, Eq b)=>SGr a b->GrwT a b->Bool
ivcesOk sg gwt = 
   let cond e = (isVCEECnt sg e `implies` satisfiesVCEECnt sg gwt e) && (isVCENCnt sg e `implies` satisfiesVCENCnt sg gwt e) in
   all cond (esVCnt sg)

-- Compliance with constraits of a SG type
tyCompliesCnts::(Eq a, Eq b, Read a, GNodesNumConv a, GNumSets a)=>GrwT a b->SGr a b->Bool
tyCompliesCnts gwt sg = okINumbers gwt && ivcesOk sg gwt

checkTyCompliesCnts::(Eq a, Eq b, Show a, Show b, Read a, GNodesNumConv a, GNumSets a) 
   => GrwT a b -> SGr a b -> ErrorTree
checkTyCompliesCnts gwt sg  = 
   let err1 = errINats gwt 
       err2 = errIInts gwt
       err3 = errIReals gwt 
       el = [err1, err2, err3] in
   if tyCompliesCnts gwt sg then nile else consET "Numeric constraints of SG type breached in instance model." el

tyComplies::(Eq a, Eq b, Read a, GNodesNumConv a, GNumSets a)=>GrwT a b->SGr a b->Bool
tyComplies gwt sg = 
   is_wf_gwt_sg (gwt, sg) && gwt `tyCompliesMult` sg 
   &&  gwt `tyCompliesFI` sg && gwt `tyCompliesPNS` sg 
   && gwt `tyCompliesCnts` sg

checkTyComplies::(Eq a, Eq b, Read a, Show a, Show b, GNodesNumConv a, GNumSets a)
   =>String->GrwT a b->SGr a b->ErrorTree
checkTyComplies id gwt sg =
   let err1 = check_wf_gwt_sg id gwt sg 
       err2 = checkTyCompliesMult gwt sg 
       err3 = checkTyCompliesFI gwt sg 
       err4 = checkTyCompliesPNS gwt sg 
       err5 = checkTyCompliesCnts gwt sg in 
   if gwt `tyComplies` sg then nile else consET "The graph does not comply to its SG type" [err1, err2, err3, err4, err5]

is_wf_ty::(Eq a, Eq b, Read a, GNodesNumConv a, GNumSets a)
   =>(Maybe MK)->(GrwT a b, SGr a b)->Bool
is_wf_ty Nothing          = is_wf_gwt_sg 
is_wf_ty (Just WeakM)     = is_wf_gwt_sg 
is_wf_ty (Just PartialM)  = (\(gwt, sg)->gwt `tyComplies` sg)
is_wf_ty (Just TotalM)    = (\(gwt, sg)->gwt `tyComplies` sg)

check_wf_ty ::(Show a, Show b, Read a, Eq a, Eq b, GNodesNumConv a, GNumSets a)=> 
   String -> Maybe MK -> (GrwT a b, SGr a b) -> ErrorTree
check_wf_ty id Nothing (gwt, sg) = check_wf_gwt_sg id gwt sg
check_wf_ty id (Just WeakM) (gwt, sg) = check_wf_gwt_sg id gwt sg
check_wf_ty id (Just PartialM) (gwt, sg) = checkTyComplies id gwt sg
check_wf_ty id (Just TotalM) (gwt, sg) = checkTyComplies id gwt sg

instance GM_CHK' GrwT SGr where
   okayGM' = is_wf_ty
   faultsGM' = check_wf_ty

-- Checks whether the target function commutes for morphisms from Gs to SGs
-- morphism_gm_commutes_tgt_ss::Eq a => (GrwTSs a, SGr a) -> Bool
-- morphism_gm_commutes_tgt_ss (g, sg) = 
--    let lhs = (fV g) `bcomp` (tgtext g) in  
--    let rhs = (tgtst sg) `bcomp` (fE g) in
--    lhs  `subseteq` rhs

-- commute_gm_tgt_ss::Eq a => (GrwTSs a, SGr a) ->([(a, a)], [(a, a)])
-- commute_gm_tgt_ss (g, sg) = 
--    let lhs = (fV g) `bcomp` (tgtext g) in  
--    let rhs = (tgtst sg) `bcomp` (fE g) in
--    (lhs, rhs)

-- errors_gwtss_sg::(Eq a, Show a) => (GrwTSs a, SGr a) -> [ErrorTree]
-- errors_gwtss_sg (g, sg) =
--    let err1 = if fun_total (fV g) (ans g) (ns sg) then nile else consET "Function 'fV' is ill defined." [reportFT (fV g) (ans g) (ns sg)] in
--    let err2 = if fun_total (fE g) (es g) (esC sg) then nile else consET "Function 'fE' is ill defined." [reportFT (fE g) (es g) (esC sg)] in
--    let err3 = if morphism_gm_commutes_src (gwt g, sg) then nile else errors_commuting (commute_gm_src (gwt g, sg)) "source" in
--    let err4 = if morphism_gm_commutes_tgt_ss (g, sg) then nile else errors_commuting (commute_gm_tgt_ss (g, sg)) "target" in 
--    [err1, err2, err3, err4]

-- check_wf_gwtss_sg nm g sg = check_wf_of (g, sg) nm (is_wf_gwtss_sg) (errors_gwtss_sg)

-- tyss_complies::Eq a=>GrwTSs a->SGr a->Bool
-- tyss_complies g sg = is_wf_gwtss_sg (g, sg) 
--     &&  (gwt g) `ty_complies_mult` sg &&  (gwt g)`ty_complies_fi` sg && (gwt g) `ty_complies_pns` sg 

-- check_tyss_complies::(Eq a, Show a)=>String->GrwTSs a->SGr a->ErrorTree
-- check_tyss_complies id g sg =
--    let err1 = check_wf_gwtss_sg id g sg in
--    let err2 = check_ty_complies_mult (gwt g) sg in
--    let err3 = check_ty_complies_fi (gwt g) sg in
--    let err4 = check_ty_complies_pns (gwt g) sg in
--    if g `tyss_complies` sg then nile else consET "Errors in compliance of graph to its SG type" [err1, err2, err3, err4]

-- is_wf_tyss::(Eq a)=>(Maybe MK)->(GrwTSs a, SGr a)->Bool
-- is_wf_tyss Nothing          = is_wf_gwtss_sg
-- is_wf_tyss (Just WeakM)     = is_wf_gwtss_sg
-- is_wf_tyss (Just PartialM)  = (\(g, sg)->g `tyss_complies` sg)
-- is_wf_tyss (Just TotalM)    = (\(g, sg)->g  `tyss_complies` sg)

-- check_wf_tyss id Nothing (g, sg) =check_wf_gwtss_sg id g sg
-- check_wf_tyss id (Just WeakM) (g, sg) = check_wf_gwtss_sg id g sg
-- check_wf_tyss id (Just PartialM) (g, sg) = check_tyss_complies id g sg
-- check_wf_tyss id (Just TotalM) (g, sg) = check_tyss_complies id g sg

-- instance GM_CHK' GrwTSs SGr where
--    is_wf_gm' = is_wf_tyss
--    check_wf_gm' = check_wf_tyss

--Gets instance nodes of particular node type given a type sg and a morphism
ns_of_ntys :: (GRM gm, Eq a, Eq b, Foldable t) => gm a b -> SGr a b->t a -> Set a
ns_of_ntys m sg ns = img (inv . fV $ m) (img (inv . inhst $ sg) ns)

--Gets instance edges of particular node type given a morphism
es_of_ety :: (GRM gm, Eq a, Eq b) => gm a b -> b -> Set b
es_of_ety m e = img (inv . fE $ m) [e]

-- is_wf_ty_sgs_strong:: (Eq a, Show a) => (GrM a, SGr a, SGr a) -> Bool
-- is_wf_ty_sgs_strong (gm, sgc, sga) = 
--    is_wf_ty_sgs_weak (gm, sgc, sga)
--    && (nsTys sga [Nnrml]) `subseteq` (ran_of $ fV gm)

-- -- The typing notion between a graph and a SG
-- is_wf_ty_g_sg:: (Eq a, Show a) => (GrM a, Gr a, SGr a) -> Bool
-- is_wf_ty_g_sg (m, g, sg) = 
--    is_wf_gm_g_sg (m, g, sg)
--    && no_instances_of_abstract_tnodes m sg 
--    && composites_not_shared m g sg
--    && instMultsOk m g sg

-- non_preserving_nodes gm sgs sgt = filter (\n->not $ appl (nty sgs) n <= appl ((fV gm) `rcomp` (nty sgt)) n) (ns sgs)

-- errors_ty_sgs_partial::(Eq a, Show a)=>String -> (GrM a, SGr a, SGr a) -> [ErrorTree]
-- errors_ty_sgs_partial nm (gm, sgs, sgt) = 
--    let errs1 = check_wf_gm_sgs nm gm sgs sgt in
--    let npns = non_preserving_nodes gm sgs sgt in
--    let errs2 = if node_types_preserved gm sgs sgt then nile else consSET $ "Instance nodes fail to preserve their type kinds: " ++ (showElems' npns) in
--    let errs3 = check_mults_respected gm (srcm sgs) (srcm sgt) "Source" in
--    let errs4 = check_mults_respected gm (tgtm sgs) (tgtm sgt) "Target" in
--    [errs1, errs2,errs3, errs4]


-- errors_ty_sgs_weak nm (gm, sgs, sgt) = 
--    let errs1 = errors_ty_sgs_partial nm (gm, sgs, sgt) in
--    let errs2 = checkInstSGMults gm sgs sgt in --if (esA sgt) `subseteq` ran_of (fE gm) then [] else ["Not all association edges of the type graph are being mapped."] in
--    errs1++errs2

-- errors_ty_sgs_strong nm (gm, sgs, sgt) = 
--    let errs1 = errors_ty_sgs_weak nm (gm, sgs, sgt) in
--    let errs2 = if ((nsTys sgt [Nnrml]) `subseteq` ran_of ((fV gm) `rcomp` (inhst sgt))) 
--                then nile 
--                else consSET $ "Not all normal nodes are being mapped to in the type morphism: " ++ (show (sminus (nsTys sgt [Nnrml]) (ran_of ((fV gm) `rcomp` (inhst sgt))))) in
--    errs1++[errs2]

-- errors_ty_sgs::(Eq a, Show a)=>String -> MK -> (GrM a, SGr a, SGr a) -> [ErrorTree]
-- errors_ty_sgs nm PartialM = errors_ty_sgs_partial nm
-- errors_ty_sgs nm FullM = errors_ty_sgs_strong nm
-- errors_ty_sgs nm PartialM = errors_ty_sgs_weak nm
-- errors_ty_sgs nm WeakM = errors_gm_sgs 

-- errors_ty_g_sg::(Eq a, Show a)=>String ->(GrM a, Gr a, SGr a) -> [ErrorTree]
-- errors_ty_g_sg nm (gm, g, sg) = 
--    let errs1 = check_wf_gm_g_sg nm gm g sg in
--    let abstract_nodes_msg ns = "Type nodes " ++ (show ns) ++ ", either abstract or enufEration, cannot have direct instances." in
--    let errs2 = if no_instances_of_abstract_tnodes gm sg then nile else consSET (abstract_nodes_msg $ (nsTys sg [Nabst, Nenum])) in
--    let errs3 = checkInstMults gm g sg in
--    let errs4 = check_composites gm g sg in
--    [errs1, errs2] ++ errs3 ++ [errs4]


-- is_wf_ty_sgs PartialM = is_wf_ty_sgs_partial 
-- is_wf_ty_sgs FullM = is_wf_ty_sgs_strong 
-- is_wf_ty_sgs PartialM = is_wf_ty_sgs_weak 
-- is_wf_ty_sgs WeakM = is_wf_gm_sgs 

-- check_wf_ty_g_sg::(Eq a, Show a)=>String -> (GrM a, Gr a, SGr a) -> ErrorTree
-- check_wf_ty_g_sg nm (gm, g, sg) = 
--    check_wf_of (gm, g, sg) nm (is_wf_ty_g_sg) (errors_ty_g_sg nm)

-- check_wf_ty_sgs::(Eq a, Show a)=>String -> MK -> (GrM a, SGr a, SGr a) -> ErrorTree
-- check_wf_ty_sgs nm mk (gm, sgs, sgt) = 
--    check_wf_of (gm, sgs, sgt) nm (is_wf_ty_sgs mk) (errors_ty_sgs nm mk)

--check_wf_gm_sg nm PartialM (gm, sg, sgt) = check_wf_ty_sgs_partial nm gm sg sgt
--check_wf_gm_sg nm (TotalM Strong) (gm, sg, sgt) = check_wf_ty_sgs_strong nm gm sg sgt
--check_wf_gm_sg nm (TotalM Weak) (gm, sg, sgt) = check_wf_ty_sgs_weak nm gm sg sgt