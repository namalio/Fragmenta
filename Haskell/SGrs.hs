--------------------------------------
-- Project: PCs/Fragmenta
-- Module: 'SGrs'
-- Description: Fragmenta's structural graphs (SGs)
-- Author: Nuno Amálio
-------------------------------------
{-# LANGUAGE MultiParamTypeClasses #-}

module SGrs(SGr, is_wf_sg, is_wf_sgz, inhG, cons_sg, g_sg, nty, ety, srcm, tgtm, pe, ds, empty_sg, nsTys, nsP, nsO, esTys, esA, esI, esW, 
   esC, srcst, tgtst, inh, inhst, disj_sgs, union_sg, union_sgs, subsume_sg, sg_refinesz, errs_sg_refinesz, tsg_refinesz, 
   errs_tsg_refinesz, ns_of_ntys, es_of_ety,
   ins)  
where

import Sets ( diff, gunion, intersec, seteq, subseteq, union )
import Relations
import Gr_Cls
import Grs
import ErrorAnalysis
import Utils
import ShowUtils
import SGElemTys
import Mult
import MyMaybe
import GrswT
import PathExpressions
import The_Nil
import SimpleFuns (pair_up)

-- Structural graphs (SGs)
data SGr a b = SGr {
   g_sg_ :: Gr a b
   , nty_ :: [(a, SGNTy)]
   , ety_ :: [(b, SGETy)]
   , srcm_ :: [(b, Mult)]
   , tgtm_ :: [(b, Mult)]
   , p_ :: [(b, PE a b)]
   , d_ :: [(b, b)]
} deriving (Show, Eq)

g_sg :: SGr a b -> Gr a b
g_sg SGr {g_sg_ = g, nty_ = _, ety_ = _, srcm_ = _, tgtm_ = _, p_ = _, d_ = _} = g
nty :: SGr a b -> [(a, SGNTy)]
nty SGr {g_sg_ = _, nty_ = nt, ety_ = _, srcm_ = _, tgtm_ = _, p_ = _, d_ = _} = nt
ety :: SGr a b -> [(b, SGETy)]
ety SGr {g_sg_ = _, nty_ = _, ety_ = et, srcm_ = _, tgtm_ = _, p_ = _, d_ = _} = et
srcm :: SGr a b -> [(b, Mult)]
srcm SGr {g_sg_ = _, nty_ = _, ety_ = _, srcm_ = sm, tgtm_ = _, p_ = _, d_ = _} = sm
tgtm :: SGr a b -> [(b, Mult)]
tgtm SGr {g_sg_ = _, nty_ = _, ety_ = _, srcm_ = _, tgtm_ = tm, p_ = _, d_ = _} = tm
pe :: SGr a b -> [(b, PE a b)]
pe SGr {g_sg_ = _, nty_ = _, ety_ = _, srcm_ = _, tgtm_ = _, p_ = p, d_ = _} = p
ds :: SGr a b -> [(b, b)]
ds SGr {g_sg_ = _, nty_ = _, ety_ = _, srcm_ = _, tgtm_ = _, p_ = _, d_ = d} = d

-- A SG constructor
cons_sg :: Gr a b-> [(a, SGNTy)]-> [(b, SGETy)]-> [(b, Mult)]-> [(b, Mult)]-> [(b, PE a b)]-> [(b, b)]-> SGr a b
cons_sg g nt et sm tm p d = SGr {g_sg_ = g, nty_ = nt, ety_ = et, srcm_ = sm, tgtm_ = tm, p_ = p, d_ = d}

-- The empty SG
empty_sg :: SGr a b
empty_sg = cons_sg empty_g [] [] [] [] [] []

instance GR SGr where
   ns = ns . g_sg
   es = es . g_sg
   src = src . g_sg
   tgt = tgt . g_sg
   empty = empty_sg

-- Gets edges of certain types
--esTys::(Eq a, Foldable t)=>SGr a->t SGETy->[a]
esTys sg ets = img (inv . ety $ sg) ets

-- Gets nodes of certain types
--nsTys::(Eq a, Show a, Foldable t)=>SGr a->t SGNTy->[a]
nsTys sg nts = img (inv . nty $ sg) nts

-- Gets proxy nodes
nsP = (flip nsTys) [Nprxy]

-- Gets optional nodes
nsO :: SGr b1 b2 -> [b1]
nsO = (flip nsTys) [Nopt]

-- Gets virtual nodes
nsV :: SGr b1 b2 -> [b1]
nsV = (flip nsTys) [Nvirt]

-- Gets the ethereal nodes
nsEther :: SGr b1 b2 -> [b1]
nsEther = (flip nsTys) [Nabst, Nvirt, Nenum]

-- Gets the inheritance edges
esI::(Eq a, Eq b)=>SGr a b->[b]
esI = (flip esTys) [Einh]

-- Gets the association edges
esA::(Eq a, Eq b)=>SGr a b->[b]
esA = (flip esTys) [et d | et<-[Ecomp, Erel], d<-[Dbi, Duni]]

-- Gets the wander edges
esW::(Eq a, Eq b)=>SGr a b->[b]
esW = (flip esTys) [Ewander]

-- Gets the derived edges
esD::(Eq a, Eq b)=>SGr a b->[b]
esD = (flip esTys) [Eder]

-- Gets path edges
esPa::(Eq a, Eq b)=>SGr a b->[b]
esPa = (flip esTys) [Epath]

-- Gets the constraint edges
esCnt::(Eq a, Eq b)=>SGr a b->[b]
esCnt sg = (esD sg) `union` (esPa sg)

-- Gets connection edges (association + wander)
esC::(Eq a, Eq b)=>SGr a b->[b]
esC sg = (esA sg) `union` (esW sg)

-- Gets multiplicity edges (connection + derived)
esM::(Eq a, Eq b)=>SGr a b->[b]
esM sg = (esC sg) `union` esD sg

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
inh::(Eq a, Eq b)=>SGr a b->[(a, a)]
inh = relOfG . inhG 

-- Reflexive transitive closure of inheritence relation
inhst::(Eq a, Eq b)=>SGr a b->[(a, a)]
inhst sg = rtrancl_on (inh sg) (ns sg)

-- totalises 'srcm' by providing multiplicities of uni-directional composition and relation edges
srcma :: Eq b => SGr a b -> [(b, Mult)]
srcma sg = (srcm sg) `override` ((esTys sg [Ecomp Duni] `cross` [[msole_k 1]]) `override` (esTys sg [Erel Duni] `cross` [[msole_many]]))

-- src relation which takes wander edges into account
srcr::(Eq a, Eq b)=>SGr a b->[(b, a)]
srcr sg = src sg `union` (dres (tgt sg) (esW sg))

-- tgt relation which takes wander edges into account
tgtr::(Eq a, Eq b)=>SGr a b->[(b, a)]
tgtr sg = tgt sg `union` (dres (src sg) (esW sg))

-- src* relations: base and final definitions
srcstr :: (Eq a, Eq b) => SGr a b -> [b]->[(b, a)]
srcstr sg es = dres (srcr sg) es 

-- src* relations: base and final definitions
srcst :: (Eq a, Eq b) => SGr a b -> [(b, a)]
srcst sg = (srcstr sg $ esC sg `union` esCnt sg) `rcomp` (inv . inhst $ sg)

-- the version used in morphisms
srcstm :: (Eq a, Eq b) => SGr a b -> [(b, a)]
srcstm sg = (srcstr sg $ esC sg) `rcomp` (inv . inhst $ sg)

-- tgt* relations: base and final definitions
tgtstr :: (Eq a, Eq b) => SGr a b ->[b]->[(b, a)]
tgtstr sg es = dres (tgtr sg) es
tgtst :: (Eq a, Eq b) => SGr a b -> [(b, a)]
tgtst sg = (tgtstr sg $ esC sg `union` esCnt sg) `rcomp` (inv $ inhst sg)
-- the version used in morphisms
tgtstm :: (Eq a, Eq b) => SGr a b -> [(b, a)]
tgtstm sg = (tgtstr sg $ esC sg) `rcomp` (inv $ inhst sg)

-- Incident edges to a set of nodes, which takes inheritance into account
esIncidentst sg vs = img (inv $ srcst sg) vs `union` img (inv $ tgtst sg) vs

-- Checks whether edges comply with their type multiplicity allowances
edge_multOk::(Eq a, Eq b)=>SGr a b->b->Bool
edge_multOk sg e = (appl (ety sg) e) `allowedm` (appl (srcma sg) e, appl (tgtm sg) e)

mult_etys_ok::(Eq a, Eq b)=>SGr a b->Bool
mult_etys_ok sg = all (\e->edge_multOk sg e) $ esM sg

-- Inheritance relation between pair of nodes complies with the inheritance restrictions of their types
inh_nty_ok :: Eq a => SGr a b -> (a, a) -> Bool
inh_nty_ok sg (v, v') = (appl(nty sg) v) < (appl(nty sg) v')
inh_ntys_ok :: (Eq a, Eq b) => SGr a b -> Bool
inh_ntys_ok sg = all (inh_nty_ok sg) (inh sg)

-- Whether an inheritance hierarchy of a SG is scylic
acyclicI::(Eq a, Eq b)=>SGr a b->Bool
acyclicI = acyclicG . inhG

-- Checks whether the inheritance hierarchy complies with required restrictions
inh_ok::(Eq a, Eq b)=>SGr a b->Bool
inh_ok sg = inh_ntys_ok sg && acyclicI sg

-- Checks whether an optional node is involved in non-compulsory relations
nodeopt_ok::(Eq a, Eq b)=>SGr a b->a->Bool
nodeopt_ok sg n = img (ety sg) ((esIncidentst sg [n]) `diff` (esI sg))  `subseteq` [Ewander]

optsVoluntary::(Eq a, Eq b)=>SGr a b->Bool
optsVoluntary sg = all (nodeopt_ok sg) $ nsO sg

-- Function that checks that a list of multiplicies are well-formed
mults_wf = all multwf

-- Checks whether a SG is well-formed either totally or partially
is_wf_sgz::(Eq a, Eq b)=>SGr a b->Bool
is_wf_sgz sg = is_wf Nothing (g_sg sg)
   && fun_total (nty sg) (ns sg) (sgnty_set) 
   && fun_total (ety sg) (es sg) (sgety_set)
   && (dom_of . srcm $ sg) `subseteq` es sg  
   && (dom_of . tgtm $ sg) `subseteq` es sg

-- Checks whether a SG is well-formed partially
is_wf_sg::(Eq a, Eq b)=>SGr a b->Bool
is_wf_sg sg = is_wf_sgz sg
   && mults_wf (ran_of $ srcm sg) && mults_wf (ran_of $ tgtm sg) 
   && fun_total' (srcma sg) (esM sg) && fun_total' (tgtm sg) (esM sg)
   && (dom_of . pe $ sg) `seteq` esCnt sg
   && antireflexive_on (ds sg) (esPa sg) 
   && mult_etys_ok sg 
   && optsVoluntary sg 
   && inh_ok sg 

-- Ethereal nodes must be inherited
etherealInherited::(Eq a, Eq b)=>SGr a b->Bool
etherealInherited sg = (nsEther sg) `subseteq` (ran_of $ inh sg)

-- WF conditions of derived edges which apply to total SGs
srcDerEOk :: (Eq a, Eq b) => SGr a b -> b -> Bool
srcDerEOk sg e = (appl (src sg) e, srcPE (restrict (g_sg sg) $ esA sg)  (appl (pe sg) e)) `elem` (inhst sg) 
tgtDerEOk :: (Eq a, Eq b) => SGr a b -> b -> Bool
tgtDerEOk sg e = (appl (tgt sg) e, tgtPE (restrict (g_sg sg) $ esA sg)  (appl (pe sg) e)) `elem` (inhst sg)
derEOk::(Eq a, Eq b)=>SGr a b->b->Bool
derEOk sg e = srcDerEOk sg e && tgtDerEOk sg e
derOk::(Eq a, Eq b)=>SGr a b->Bool
derOk sg = all (derEOk sg) (esD sg)

okPEASrc sg v (Edg e) = (e, v) `elem` (srcst sg)
okPEASrc sg v (Inv e) = (e, v) `elem` (tgtst sg)

okPEATgt sg v (Edg e) = (e, v) `elem` (tgtst sg)
okPEATgt sg v (Inv e) = (e, v) `elem` (srcst sg)

okPEA :: (GR g, Eq a, Eq b) => g a b -> PEA b -> Bool
okPEA sg (Edg e) = e `elem` (es sg)
okPEA sg (Inv e) = e `elem` (es sg)

okPE sg (At pea) = okPEA sg pea
okPE sg (Dres v pea) = okPEA sg pea && okPEASrc sg v pea
okPE sg (Rres pea v) = okPEA sg pea && okPEATgt sg v pea
okPE sg (SCmp pe1 pe2) = 
   let g = restrict (g_sg sg) $ esA sg in
   okPE sg pe1 && okPE sg pe2 && (tgtPE g pe1, srcPE g pe2) `elem` ((inhst sg) `union` (inv . inhst $ sg))

esCntOk sg e = okPE sg (appl (pe sg) e)
esCntsOk::(Eq a, Eq b)=>SGr a b->Bool
esCntsOk sg = derOk sg && all (esCntOk sg) (esCnt sg) 
   

-- Whether an inheritance hierarchy of a SG without virtual nodes forms a tree (single-inheritance model)
inhMinus sg = relOfG $ subtractNs (inhG sg) (nsV sg)
isInhTree :: (Eq a, Eq b) => SGr a b -> Bool
isInhTree sg = pfun (inhMinus sg) (ns sg) (ns sg) 

-- WF of total SGs
is_wf_tsg::(Eq a, Eq b)=>SGr a b->Bool
is_wf_tsg sg = is_wf_sg sg && etherealInherited sg 
   && esCntsOk sg && isInhTree sg 

check_mult_etys_ok sg = 
   if mult_etys_ok sg then nile else cons_se $ "The following edges have incorrect multiplicities:"++ (showElems' err_es)
   where err_es = foldr (\e es->if edge_multOk sg e then es else (e:es)) [] (esM sg)

check_optsVoluntary::(Eq a, Eq b, Show a, Show b)=>SGr a b->ErrorTree
check_optsVoluntary sg = 
   if optsVoluntary sg then nile else cons_se $ "The following optional nodes are engaged in compulsory relations:" ++ (showElems' err_opts)
   where err_opts = foldr (\n ns-> if nodeopt_ok sg n then ns else n:ns) [] (nsO sg)

check_inh_ok::(Eq a, Eq b, Show a, Show b)=>SGr a b->ErrorTree
check_inh_ok sg = 
   let errs1 = if inh_ntys_ok sg then nile else cons_se $ "The following inheritance pairs are not compliant with the node type restrictions:" ++ (showElems' err_inh_pairs) in
   let errs2 = if acyclicI sg then nile else cons_se "The inheritance hierarchy has cycles." in
   if inh_ok sg then nile else cons_et "Errors in the inheritance hierarchy." [errs1, errs2]
   where err_inh_pairs = filter (not . (inh_nty_ok sg)) (inh sg)


errors_sg::(Eq a, Eq b, Show a, Show b)=>SGr a b-> [ErrorTree]
errors_sg sg = 
   let err1 = err_prepend "The underlying graph is malformed." (check_wf "SG" Nothing $ g_sg sg) in
   let err2 = err_prepend "Function 'nty' is not total. " $ check_fun_total (nty sg) (ns sg) (sgnty_set) in
   let err3 = err_prepend "Function 'ety' is not total. " $ check_fun_total (ety sg) (es sg) (sgety_set) in
   let err4 = if mults_wf (ran_of $ srcm sg) then nile else cons_se "Well-formedness errors in edge source multiplicities." in
   let err5 = if mults_wf (ran_of $ tgtm sg) then nile else cons_se "Well-formedness errors in edge target multiplicities." in
   let err6 = err_prepend "Source multplicity function is not total. " $ check_fun_total' (srcma sg) (esM sg) in
   let err7 = err_prepend "Target multplicity function is not total. " $ check_fun_total' (tgtm sg) (esM sg) in
   let err8 = check_mult_etys_ok sg in
   let err9 = check_optsVoluntary sg in
   let err10 = check_inh_ok sg in
   [err1, err2, err3, err4, err5, err6, err7, err8, err9, err10]

check_wf_sg::(Eq a, Eq b, Show a, Show b)=>String->SGr a b-> ErrorTree
check_wf_sg nm sg = check_wf_of sg nm is_wf_sg errors_sg

check_etherealInherited sg = 
   if etherealInherited sg then nile else cons_se $ "The following ethereal nodes are not inherited: " ++ (showElems' ens_n_inh)
   where isInherited n = n `elem` (ran_of $ inh sg)
         ens_n_inh = filter (not . isInherited)(nsEther sg) 

check_isInhTree sg = 
   let msg1 = "The inheritance is not single." in
   let msg2 = "The inheritance hierarchy without virtual nodes is not a tree. " in
   if isInhTree sg then nile else cons_et msg1 [err_prepend msg2 $ check_pfun (inhMinus sg) (ns sg) (ns sg)]

check_derOk::(Eq a, Eq b, Show a, Show b)=>SGr a b-> ErrorTree
check_derOk sg = 
   let msg_src e = "The source of edge " ++ (show e) ++ " is invalid." in
   let msg_tgt e = "The target of edge " ++ (show e) ++ " is invalid." in
   let cons_ems_src e = if (not $ srcDerEOk sg e) then [msg_src e] else [] in
   let cons_ems_tgt e = if (not $ tgtDerEOk sg e) then [msg_tgt e] else [] in
   let des_bad = foldr (\e ms->(cons_ems_src e) ++ (cons_ems_tgt e) ++ ms) [] (esD sg) in
   if derOk sg then nile else cons_se $ "Errors with derived edges: " ++ (showElems' des_bad)

check_esCntsOk sg = 
   if esCntsOk sg then nile else cons_se $ "Errors with the following constraint edges: " ++ (showElems' esCnts_nOk) ++ (show $ srcst sg) ++ (show $ tgtst sg)
   where esCnts_nOk = filter (not . (esCntOk sg)) (esCnt sg) 

errors_tsg::(Eq a, Eq b, Show a, Show b)=>SGr a b-> [ErrorTree]
errors_tsg sg = 
   let err1 = check_wf "SG" Nothing sg in
   let err2 = check_isInhTree sg in
   let err3 = check_etherealInherited sg in
   let err4 = check_derOk sg in
   let err5 = check_esCntsOk sg in 
   [err1] ++ [err2, err3, err4, err5]

check_wf_tsg::(Eq a, Eq b, Show a, Show b)=>String->SGr a b-> ErrorTree
check_wf_tsg nm sg = check_wf_of sg nm is_wf_tsg errors_tsg

is_wf_sg' :: (Eq a, Eq b) => Maybe TK -> SGr a b -> Bool
is_wf_sg' (Just Total) = is_wf_tsg 
is_wf_sg' (Just Partial) = is_wf_sg 
is_wf_sg' Nothing = is_wf_sgz

check_wf_sg' :: (Eq a, Eq b, Show a, Show b) =>String -> Maybe TK -> SGr a b -> ErrorTree
check_wf_sg' id (Just Total) = check_wf_tsg id
check_wf_sg' id _            = check_wf_sg id  

instance G_WF_CHK SGr where
   is_wf = is_wf_sg'
   check_wf = check_wf_sg'

-- Checs whether SGs are disjoint
disj_sgs :: (Eq a, Eq b) => [SGr a b] -> Bool
disj_sgs sgs = disj_gs (map g_sg sgs) 

-- Union of SGs
union_sg :: (Eq a, Eq b) => SGr a b -> SGr a b -> SGr a b
union_sg sg1 sg2 = 
   let ug = (g_sg sg1) `union_g` (g_sg sg2) in
   let u_nty = (nty sg1) `union` (nty sg2) in
   let u_ety = (ety sg1) `union` (ety sg2) in
   let u_srcm = (srcm sg1) `union` (srcm sg2) in
   let u_tgtm = (tgtm sg1) `union` (tgtm sg2) in
   let u_pe = (pe sg1) `union` (pe sg2) in
   let u_ds = (ds sg1) `union` (ds sg2) in
   cons_sg ug u_nty u_ety u_srcm u_tgtm u_pe u_ds

union_sgs :: (Eq b, Eq a) => [SGr a b] -> SGr a b
union_sgs sgs = 
   cons_sg (union_gs $ map g_sg sgs) (gunion $ map nty sgs) (gunion $ map ety sgs) (gunion $ map srcm sgs) (gunion $ map tgtm sgs) (gunion $ map pe sgs) (gunion $ map ds sgs)

-- SG subsumption
subsume_sg :: (Eq a, Eq b)=>SGr a b-> [(a, a)] -> SGr a b
subsume_sg sg sub 
   | pfun sub (nsP sg) (ns sg) = cons_sg s_g (dsub (nty sg) ((dom_of sub) `diff` (ran_of sub))) (ety sg) (srcm sg) (tgtm sg) (pe sg) (ds sg) 
   | otherwise = sg
   where s_g = subsume_g (g_sg sg) sub 

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

commute_sgm_src (sgs, m, sgt) = 
   let lhs = (fV m) `bcomp` (srcstm sgs) in  
   let rhs = (srcstm sgt) `bcomp` (fE m) in
   (lhs, rhs)

-- Checks whether the source function commutes for morphisms between SGs
morphism_sgm_commutes_src (sgs, m, sgt) = 
   let (lhs, rhs) = commute_sgm_src (sgs, m, sgt) in
   lhs  `subseteq` rhs

commute_sgm_tgt (sgs, m, sgt) = 
   let lhs = (fV m) `bcomp` (dres (tgtstm sgs) $ esC sgs) in  
   let rhs = (tgtstm sgt) `bcomp` (fE m) in
   (lhs, rhs)

-- Checks whether the target function commutes for morphisms between SGs
morphism_sgm_commutes_tgt :: (GRM gm, Eq a, Eq b) => (SGr a b, gm a b, SGr a b) -> Bool
morphism_sgm_commutes_tgt (sgs, m, sgt) = 
   let (lhs, rhs) = commute_sgm_tgt (sgs, m, sgt) in
   lhs  `subseteq` rhs

-- Checks whether the inheritance is preserved
ihh_sgm_ok (sgs, m, sgt) = ((fV m) `bcomp` (inhst sgs)) `subseteq` ((inhst sgt) `bcomp` (fV m))

-- Common aspects of both graph morphism settings which involve SGs
is_wf_gm_common (gs, m, gt) = 
   -- is_wf Nothing gs && is_wf Nothing gt 
   fun_total (fV m) (ns gs) (ns gt)  

-- checks whether a morphisms between SGs is well-formed
is_wf_sgm::(Eq a, Eq b) => (SGr a b, GrM a b,  SGr a b) -> Bool
is_wf_sgm (sgs, m, sgt) = is_wf_gm_common (sgs, m, sgt)
   && fun_total (fE m) (esC sgs) (esC sgt)
   && morphism_sgm_commutes_src (sgs, m, sgt)
   && morphism_sgm_commutes_tgt (sgs, m, sgt)
   && ihh_sgm_ok (sgs, m, sgt)

errors_sgm_common (gs, m, gt) =
   let err1 = check_wf "Source graph" Nothing gs in
   let err2 = check_wf "Target Graph" Nothing gt in
   let err3 = if fun_total (fV m) (ns gs) (ns gt) then nile else cons_et "Function 'fV' is ill defined." [check_fun_total (fV m) (ns gs) (ns gt)] in
   [err1, err2, err3]

errors_commuting (r1, r2) ty = 
   if  r1 `subseteq` r2 then nile else cons_et ("Problems in commuting of " ++ ty ++ " functions") [check_subseteq r1 r2]

errors_wf_sgm :: (Show b, Show a, GRM gm, Eq a, Eq b) =>(SGr a b, gm a b, SGr a b) -> [ErrorTree]
errors_wf_sgm (gs, m, gt) = 
   let errs1 = errors_sgm_common (gs, m, gt) in
   let err2 = if fun_total (fE m) (esC gs) (esC gt) then nile else cons_et "Function 'fE' is ill defined." [check_fun_total (fE m) (esC gs) (esC gt)] in
   let err3 = if morphism_sgm_commutes_src (gs, m, gt) then nile else errors_commuting (commute_sgm_src (gs, m, gt)) "source" in
   let err4 = if morphism_sgm_commutes_tgt (gs, m, gt) then nile else errors_commuting (commute_sgm_tgt (gs, m, gt)) "target" in
   let err5 = if ihh_sgm_ok (gs, m, gt) then nile else cons_se "Problems in the commuting of the inheritance relation" in
   errs1 ++ [err2, err3, err4, err5]

check_wf_sgm::(Eq a, Eq b, Show a, Show b)=>String->SGr a b-> GrM a b->SGr a b->ErrorTree
check_wf_sgm nm sgs gm sgt = check_wf_of (sgs, gm, sgt) nm (is_wf_sgm) (errors_wf_sgm)

-- Totalises a morphism for the derived edges
-- totaliseForDer m sg = cons_gm (fV m) ((mktotal_in (dres (eb sg) (esD sg)) (esC sg)) `rcomp` (fE m))

commute_gm_src::(Eq a, Eq b) => (GrwT a b, SGr a b) ->([(b, a)], [(b, a)])
commute_gm_src (gwt, sg) = 
   let lhs = (fV gwt) `bcomp` (src gwt) in  
   let rhs = (srcstm sg) `bcomp` (fE  gwt) in
   (lhs, rhs)

-- Checks whether the source function commutes for morphisms from Gs to SGs
morphism_gm_commutes_src::(Eq a, Eq b) => (GrwT a b, SGr a b) -> Bool
morphism_gm_commutes_src (gwt, sg) = 
   let (lhs, rhs) = commute_gm_src (gwt, sg) in
   lhs  `subseteq` rhs

commute_gm_tgt::(Eq a, Eq b) => (GrwT a b, SGr a b) ->([(b, a)], [(b, a)])
commute_gm_tgt (gwt, sg) = 
   let lhs = (fV gwt) `bcomp` (tgt gwt) in  
   let rhs = (tgtstm sg) `bcomp` (fE gwt) in
   (lhs, rhs)

-- Checks whether the target function commutes for morphisms from Gs to SGs
morphism_gm_commutes_tgt::(Eq a, Eq b) => (GrwT a b, SGr a b) -> Bool
morphism_gm_commutes_tgt (gwt, sg) = 
   let (lhs, rhs) = commute_gm_tgt (gwt, sg) in
   lhs  `subseteq` rhs

is_wf_gwt_sg:: (Eq a, Eq b) => (GrwT a b, SGr a b) -> Bool
is_wf_gwt_sg (gwt, sg) = is_wf_gm_common (gOf gwt, ty gwt, sg)
   && fun_total (fE gwt) (es gwt) (esC sg)
   && morphism_gm_commutes_src (gwt, sg)
   && morphism_gm_commutes_tgt (gwt, sg)

errors_gwt_sg::(Eq a, Eq b, Show a, Show b) => (GrwT a b, SGr a b) -> [ErrorTree]
errors_gwt_sg (gwt, sg) =
   let errs1 = errors_sgm_common (gOf gwt, ty gwt, sg) in
   let err2 = if fun_total (fE gwt) (es gwt) (esC sg) then nile else cons_et ("Function 'fE' is ill defined." ++ (show $ fE gwt)++ (show $ esC sg)) [check_fun_total (fE gwt) (es gwt) (esC sg)] in
   let err3 = if morphism_gm_commutes_src (gwt, sg) then nile else errors_commuting (commute_gm_src (gwt, sg)) "source" in
   let err4 = if morphism_gm_commutes_tgt (gwt, sg) then nile else errors_commuting (commute_gm_tgt (gwt, sg)) "target" in 
   errs1 ++ [err2, err3, err4]

check_wf_gwt_sg nm gwt sg = check_wf_of (gwt, sg) nm (is_wf_gwt_sg) (errors_gwt_sg)

-- Gets instance nodes of a set of meta-nodes, which are obtained via the given morphism
ins::(Eq a,  Eq b, GRM gm)=>gm a b->SGr a b->[a]->[a]
ins m sg mns = img (inv . fV $ m) (img (inv . inhst $ sg) mns)

-- Gets instance edges of set of meta-edges using the given morphism
ies::(Eq a,  Eq b, GRM gm)=>gm a b->[b]->[b]
ies m mes = img (inv . fE $ m) mes

-- Builds instance graph restricted to the instances of a set of meta-edges
igRMEs::(Eq a, Eq b)=>GrwT a b->[b]->Gr a b
igRMEs gwt mes = (gOf gwt) `restrict` (ies (ty gwt) mes)

-- Builds instance graph restricted to the instances of set of meta-nodes and -edges
igRMNsEs::(Eq a, Eq b)=>GrwT a b->SGr a b->[a]->[b]->Gr a b
igRMNsEs gwt sg mns mes = (igRMEs gwt mes) `restrictNs` (ins (ty gwt) sg mns)

-- SG multiplicity refinement (leq == '<=')
sgs_mult_leq sgc m sga e  = appl (srcma sgc) e `m_leq` appl ((srcma sga) `bcomp` (fE m)) e
sg_refines_m (sgc, m) sga = all (\e-> sgs_mult_leq sgc m sga e) $ esC sgc

-- SG refinement of edge types
sgs_ety_leq sgc m sga e  = appl (ety sgc) e <= appl ((ety sga) `bcomp` (fE m)) e
sg_refines_ety (sgc, m) sga = all (\e-> sgs_ety_leq sgc m sga e) $ esC sgc

-- SG refinement of node types
sgs_nty_leq sgc m sga n  = appl (nty sgc) n <= appl ((nty sga) `bcomp` (fV m)) n
sg_refines_nty (sgc, m) sga = all (\n-> sgs_nty_leq sgc m sga n) $ ns sgc

-- SG refinement conditions
sg_refinesz (sgc, m) sga = (sgc, m) `sg_refines_nty` sga && (sgc, m) `sg_refines_ety`  sga 
   && (sgc, m) `sg_refines_m` sga

-- SG refinement 
sg_refines (sgc, m) sga = 
   --let m' = totaliseForDer m sgc  in 
   is_wf_sgm (sgc, m, sga) &&  (sgc, m) `sg_refinesz` sga

-- Error checking
check_sg_refines_m (sgc, m) sga = 
   if (sgc, m) `sg_refines_m` sga then nile else cons_se $ "Issues with multiplicity refinement for the following edges:" ++ (showElems' es_n_ref)
   where es_n_ref = filter (\e-> not $ sgs_mult_leq sgc m sga e) (esC sgc)

check_sg_refines_ety (sgc, m) sga = 
   if (sgc, m) `sg_refines_ety` sga then nile else cons_se $ "Issues with edge type refinement for the following edges:" ++ (showElems' es_n_ref)
   where es_n_ref = filter (\e-> not $ sgs_ety_leq  sgc m sga e) (esC sgc)

check_sg_refines_nty (sgc, m) sga = 
   if (sgc, m) `sg_refines_nty` sga then nile else cons_se $ "The following instance nodes fail to preserve their type kinds: " ++ (showElems' ns_n_ref)
   where ns_n_ref = filter (\n-> not $ sgs_nty_leq sgc m sga n) (ns sgc)

errs_sg_refinesz (sgc, m) sga = 
   let err1 = check_sg_refines_nty (sgc, m) sga in
   let err2 = check_sg_refines_ety (sgc, m) sga in
   let err3 = check_sg_refines_m (sgc, m) sga in
   [err1, err2, err3]

-- errors of SG refinement
errs_sg_refines id (sgc, m, sga) = 
   --let m' = totaliseForDer m sgc in 
   let err1 = check_wf_sgm id sgc m sga in
   let errs2 = errs_sg_refinesz (sgc, m) sga in
   (err1:errs2)

check_sg_refines id (sgc, m) sga = check_wf_of (sgc, m, sga) id (sg_refines') (errs_sg_refines id)
   where sg_refines' (sgc, m, sga) = (sgc, m) `sg_refines` sga

-- Total SG refinement of abstract nodes
is_refined m sga n = not . null $ (img (inhst sga) [n]) `intersec` (ran_of  $ fV m)
tsg_refines_ans m sga = all (\nn-> is_refined m sga nn) (nsTys sga [Nnrml])

-- Total SG refinement of abstract edges
tsg_refines_aes::(Eq a, Eq b)=>(SGr a b, GrM a b)->SGr a b->Bool
tsg_refines_aes (sgc, m) sga = all (\me->(sga, me) `okRefinedIn` (sgc, m)) (esA sga)

-- Checks if the instance relation is refined correctly
okRefinedIn::(Eq a, Eq b)=>(SGr a b, b)->(SGr a b, GrM a b)->Bool
okRefinedIn (sga, me) (sgc, m) = 
   let r = (inhst sgc) `rcomp` (relOfG $ igRMEs (cons_gwt (g_sg sgc) m) [me]) `rcomp` (inv . inhst $ sgc) in
   let s = (ins m sga $ img (src sga) [me]) `diff`  (nsEther sgc `diff` dom_of r) in
   let t = (ins m sga $ img (tgt sga) [me]) `diff` (nsEther sgc `diff` ran_of r) in
   (relation r s t) && (not . null $ r) 

-- Total SG refinement conditions
tsg_refinesz::(Eq a, Eq b)=>(SGr a b, GrM a b)->SGr a b->Bool
tsg_refinesz (sgc, m) sga = 
   (sgc, m) `sg_refinesz` sga && (sgc, m) `tsg_refines_aes` sga && m `tsg_refines_ans` sga

-- Total SG refinement
tsg_refines::(Eq a, Eq b)=>(SGr a b, GrM a b)->SGr a b->Bool
tsg_refines (sgc, m) sga = 
   is_wf_sgm (sgc, m, sga) && (sgc, m) `tsg_refinesz` sga 

-- Errors checking
-- errors of SG refinement of abstract nodes
check_tsg_refines_ans m sga = 
   if m `tsg_refines_ans` sga then nile else cons_se $ "The following normal nodes are not being refined: " ++ (showElems' nns_n_ref)
   where nns_n_ref = filter (\nn-> not $ is_refined m sga nn) (nsTys sga [Nnrml])

check_tsg_refines_aes::(Eq a, Eq b, Show a, Show b)=>(SGr a b, GrM a b)->SGr a b->ErrorTree
check_tsg_refines_aes (sgc, m) sga =
   if (sgc, m) `tsg_refines_aes` sga then nile else cons_se $ "Certain association edges are not correctly refined: " ++ (showElems' aes_nref)
   where aes_nref = filter (\me-> not $ (sga, me) `okRefinedIn` (sgc, m)) (esA sga)

errs_tsg_refinesz::(Eq a, Eq b, Show a, Show b)=>(SGr a b, GrM a b)->SGr a b->[ErrorTree]
errs_tsg_refinesz (sgc, m) sga =
   let errs1 = errs_sg_refinesz (sgc, m) sga in
   let err2 = check_tsg_refines_ans m sga in
   let err3 = check_tsg_refines_aes (sgc, m) sga in
   errs1 ++ [err2, err3]

check_tsg_refines::(Eq a, Eq b, Show a, Show b)=>String->(SGr a b, GrM a b)->SGr a b->ErrorTree
check_tsg_refines id (sgc, m) sga = 
   let err1 = check_wf_sgm id sgc m sga in
   let errs2 = errs_tsg_refinesz (sgc, m) sga in
   if (sgc, m) `tsg_refines` sga then nile else cons_et "Errors in total SG refinement" (err1:errs2)


-- Checks that 'abstract' and 'enum' mEtamodel nodes have no direct nodes in instance graph
no_instances_of_abstract_tnodes m sgt = null (img (inv $ fV m) $ nsTys sgt [Nabst, Nenum])

-- Checks whether an edge is instantiated invertedly, which is permitted for wander edges
inverted_ie gwt sg e = applM ((tgt sg) `bcomp` (fE . ty $ gwt)) e == applM ((fV . ty $ gwt) `bcomp` (src sg)) e

-- Gets the instance graph restricted to a wander edge
gOfwei :: (Eq a, Eq b, GR g) => GrwT a b -> g a b -> b -> Gr a b
gOfwei gwt sg e = 
   let g' = gOf gwt in
   if inverted_ie gwt sg e then invertg g' else g'

-- Gets instance graph restricted to a set of wander edges
gOfweis :: (Eq b, Eq a, GR g) => GrwT a b -> g a b -> [b] -> Gr a b
gOfweis gwt sg []     = empty_g
gOfweis gwt sg (e:es) = gOfwei gwt sg e `union_g` gOfweis gwt sg es

-- Gets an instance graph restricted to a meta-edge
--igRMEsW::(Eq a, Eq b)=>GrwT a b->SGr a b->b->Gr a b
--igRMEsW gwt sg me 
--   | me `elem` esD sg = igRMNsEs gwt sg [appl (src sg) me, appl (tgt sg) me] [appl (eb sg) me]
--   | me `elem` esW sg =  gOfweis gwt sg (img (inv $ (fE . ty $ gwt)) [me])
--   | otherwise = igRMEs gwt [me]


is_wf_sgm'::(Eq a, Eq b)=>Maybe MK->(SGr a b, GrM a b, SGr a b)->Bool
is_wf_sgm' Nothing = is_wf_sgm
is_wf_sgm' (Just WeakM) = is_wf_sgm
is_wf_sgm' (Just PartialM) = (\(sgc, m, sga)->(sgc, m) `sg_refines` sga)
is_wf_sgm' (Just TotalM) = (\(sgc, m, sga)->(sgc, m) `tsg_refines` sga)

check_wf_gm_g'::(Eq a, Eq b, Show a, Show b)=>String->Maybe MK->(SGr a b, GrM a b, SGr a b)->ErrorTree
check_wf_gm_g' id Nothing (sgc, m, sga)= check_wf_sgm id sgc m sga
check_wf_gm_g' id (Just WeakM) (sgc, m, sga) = check_wf_sgm id sgc m sga
check_wf_gm_g' id (Just  PartialM) (sgc, m, sga) = check_sg_refines id (sgc, m) sga
check_wf_gm_g' id (Just TotalM) (sgc, m, sga) = check_tsg_refines id (sgc, m) sga

instance GM_CHK SGr SGr where
   is_wf_gm = is_wf_sgm'
   check_wf_gm = check_wf_gm_g'

--
-- SG Type conformance

-- Instances of compounds are not allowed to share parts
ty_complies_pns::(Eq a, Eq b)=>GrwT a b->SGr a b->Bool
ty_complies_pns gwt sg = injective $ relOfG (igRMEs gwt (esTys sg [Ecomp Dbi, Ecomp Duni]))

check_ty_complies_pns::(Eq a, Eq b, Show a, Show b)=>GrwT a b->SGr a b->ErrorTree
check_ty_complies_pns gwt sg = 
   let r = relOfG $ igRMEs gwt (esTys sg [Ecomp Dbi, Ecomp Duni]) in
   if gwt `ty_complies_pns` sg then nile else cons_et "Parts are being shared by compounds:" [check_inj r]

-- Instances of ethereal nodes are not allowed
insEther :: (GRM gm, Eq a, Eq b) => gm a b -> SGr a b -> [a]
insEther gwt sg = img ((inv . fV) $ gwt) $ nsEther sg
ty_complies_fi::(Eq a, Eq b)=>GrwT a b->SGr a b->Bool
ty_complies_fi gwt sg = null $ insEther gwt sg

insEtherPairs :: (GRM gm, Eq a, Eq b) => gm a b -> SGr a b -> [(a, a)]
insEtherPairs gwt sg = foldr (\ne ps->(map ((flip pair_up) ne) (img ((inv . fV) $ gwt) [ne])) ++ ps) [] $ nsEther sg

check_ty_complies_fi gwt sg = 
   if ty_complies_fi gwt sg then nile else cons_se $ "Error! There are the following ethereal nodes instances:" ++ (show_pairs (insEtherPairs gwt sg))
   where show_pairs [] = ""
         show_pairs ((x, y):ps) = (show x)++"->"++(show y)++(show_pairs ps) 


-- Builds a relation from a path expression atom
rPEA :: (Eq a, Eq b, GR g, GRM g) =>g a b -> SGr a b -> PEA b -> [(a, a)]
rPEA gwt sg (Edg e) = 
   let r = relOfG $ restrict gwt (ies gwt [e]) in
   if e `elem` esW sg then r `union` (inv r) else r 
rPEA gwt sg (Inv e) = 
   let r = relOfG $ restrict gwt (ies gwt [e]) in
   if e `elem` esW sg then r `union` (inv r) else inv r
   --inv . relOfG $ restrict gwt [e]

-- Builds a relation from a path expression atom
rPE :: (Eq a, Eq b, GR g, GRM g) =>g a b -> SGr a b -> PE a b -> [(a, a)]
rPE gwt sg (At pea) = rPEA gwt sg pea
rPE gwt sg (Dres v pea) = dres (rPEA gwt sg pea) $ ins gwt sg [v]
rPE gwt sg (Rres pea v) = rres (rPEA gwt sg pea) $ ins gwt sg [v]
rPE gwt sg (SCmp pe1 pe2) = (rPE gwt sg pe1) `rcomp` (rPE gwt sg pe2)

ape :: (Eq a, Eq b) => SGr a b -> b -> PE a b
ape sg e = if e `elem` esCnt sg then appl (pe sg) e else At (Edg e) 

multComp :: [MultC] -> [MultC] -> [MultC]
multComp m1 m2
   | isMultMany m1 || isMultMany m2       = [msole_many]
   | isMultVal_k m1 0 || isMultVal_k m2 0 = [msole_k 0]
   | isMultVal_k m1 1 = m2
   | isMultVal_k m2 1 = m1
   | isMultOpt m1 = (msole_k 0):m2
   | isMultOpt m2 = (msole_k 0):m1
   | isMultRange m1 && isMultRange m2 = [(the m1) `mult_mr` (the m2)]
   | isMultEither m2 = multComp m1 [head m2] `union` multComp m1 (tail m2)
   | isMultEither m1 = multComp [head m1] m2 `union` multComp (tail m1) m2


-- 'srcst' relation of a PEA
srcstPEA :: (Eq a, Eq b) => SGr a b -> PEA b ->[(b,a)]
srcstPEA sg (Edg e) = srcst sg
srcstPEA sg (Inv e) = tgtst sg

-- 'srcst' relation of a PE
srcstPE :: (Eq a, Eq b) => SGr a b -> PE a b ->a->[(b,a)]
srcstPE sg (At pea) v = rres (srcstPEA sg pea) [v]
srcstPE sg (Dres v1 pea) v2 = rres (srcstPEA sg pea) [v1, v2]
srcstPE sg (Rres pea _) v2 = rres (srcstPEA sg pea) [v2]
srcstPE sg (SCmp pe1 pe2) v = srcstPE sg pe1 v

-- 'tgtst' relation of a PEA
tgtstPEA :: (Eq a, Eq b) => SGr a b -> PEA b ->[(b,a)]
tgtstPEA sg (Edg e) = tgtst sg
tgtstPEA sg (Inv e) = srcst sg

-- 'tgtst' relation of a PE
tgtstPE :: (Eq a, Eq b) => SGr a b -> PE a b ->a->[(b,a)]
tgtstPE sg (At pea) v = rres (tgtstPEA sg pea) [v]
tgtstPE sg (Dres v1 pea) v2 = rres ( tgtstPEA sg pea) [v2]
tgtstPE sg (Rres pea v1) v2 = rres (tgtstPEA sg pea) [v1, v2]
tgtstPE sg (SCmp pe1 pe2)v  = tgtstPE sg pe1 v

-- gives target of path expression atom
tPEA :: (Eq a, Eq b) => SGr a b -> PEA b -> a
tPEA sg (Edg e) = appl (tgt sg) e
tPEA sg (Inv e) = appl (src sg) e

-- gives target of path expression
tPE :: (Eq a, Eq b) => SGr a b -> PE a b -> a
tPE sg (At pea) = tPEA sg pea
tPE sg (Dres v pea) = tPEA sg pea
tPE sg (Rres pea v) = tPEA sg pea
tPE sg (SCmp pe1 pe2) = tPE sg pe2

-- gives source multiplicity of path expression atom
smPEA :: Eq b => SGr a b -> PEA b -> Mult
smPEA sg (Edg e) = appl (srcma sg) e
smPEA sg (Inv e) = appl (tgtm sg) e

-- source multiplicity of path expression 
smPE :: Eq b => SGr a b -> PE a b -> [MultC]
smPE sg (At pea) = smPEA sg pea
smPE sg (Dres v pea) = smPEA sg pea
smPE sg (Rres pea v) = smPEA sg pea
smPE sg (SCmp pe1 pe2) = multComp (smPE sg pe1)  (smPE sg pe2)

-- target multiplicity of path expression atom
tmPEA :: Eq b => SGr a b -> PEA b -> Mult
tmPEA sg (Edg e) = appl (tgtm sg) e
tmPEA sg (Inv e) = appl (srcma sg) e

-- gives target multiplicity of path expression 
tmPE :: Eq b => SGr a b -> PE a b -> [MultC]
tmPE sg (At pea) = tmPEA sg pea
tmPE sg (Dres v pea) = tmPEA sg pea
tmPE sg (Rres pea v) = tmPEA sg pea
tmPE sg (SCmp pe1 pe2) = multComp (tmPE sg pe1)  (tmPE sg pe2)

-- Builds the relatin for the multiplicity check
rMultOk :: (Eq a, Eq b, GR g, GRM g) => SGr a b -> b -> g a b -> [(a, a)]
rMultOk sg me gwt = 
   let s = ins gwt sg $ img (srcst sg) [me] in
   let t =  ins gwt sg $ img (tgtst sg) [me] in
   rres (dres (rPE gwt sg $ ape sg me) s) t

multOk_srcstr :: (Eq a, Eq b) => SGr a b -> b -> [(b, a)]
multOk_srcstr sg me = srcstPE sg (ape sg me) (appl (src sg) me)

multOk_tgtstr :: (Eq a, Eq b) => SGr a b -> b -> [(b, a)]
multOk_tgtstr sg me = tgtstPE sg (ape sg me) (appl (tgt sg) me)
-- Checks whether appropriate instances of a SG comply to the meta-edges's multiplicity constraints
me_multOk::(Eq a, Eq b)=>SGr a b->b->GrwT a b->Bool
me_multOk sg me gwt = 
   let r = rMultOk sg me gwt in
   let s = ins gwt sg $ img (multOk_srcstr sg me) [rsrcPE $ ape sg me] in
   let t = ins gwt sg $ img (multOk_tgtstr sg me) [rtgtPE $ ape sg me] in
   multOk r s t (appl (srcma sg) me) (appl (tgtm sg) me)

check_me_multOk::(Eq a, Eq b, Show a, Show b)=>SGr a b->b->GrwT a b->ErrorTree
check_me_multOk sg me gwt = 
   let r = rMultOk sg me gwt in
   let s = ins gwt sg $ img (multOk_srcstr sg me) [rsrcPE $ ape sg me] in
   let t = ins gwt sg $ img (multOk_tgtstr sg me) [rtgtPE $ ape sg me] in
   check_multOk me r s t (appl (srcma sg) me) (appl (tgtm sg) me)

-- Multiplicity compliance of all connection and derived edges
ty_complies_mult::(Eq a, Eq b)=>GrwT a b->SGr a b->Bool
ty_complies_mult gwt sg = all (\me->me_multOk sg me gwt) $ esM sg

check_ty_complies_mult :: (Eq a, Eq b, Show a, Show b) => GrwT a b -> SGr a b -> ErrorTree
check_ty_complies_mult gwt sg = 
   if ty_complies_mult gwt sg then nile else cons_et "Multiplicity breached in instance model." errs
   where errs = foldr (\me errs ->(check_me_multOk sg me gwt):errs) [] (esM sg)

ty_complies::(Eq a, Eq b)=>GrwT a b->SGr a b->Bool
ty_complies gwt sg = is_wf_gwt_sg (gwt, sg) && gwt `ty_complies_mult` sg &&  gwt `ty_complies_fi` sg && gwt `ty_complies_pns` sg 

check_ty_complies::(Eq a, Eq b, Show a, Show b)=>String->GrwT a b->SGr a b->ErrorTree
check_ty_complies id gwt sg =
   let err1 = check_wf_gwt_sg id gwt sg in
   let err2 = check_ty_complies_mult gwt sg in
   let err3 = check_ty_complies_fi gwt sg in
   let err4 = check_ty_complies_pns gwt sg in
   if gwt `ty_complies` sg then nile else cons_et "The graph does not comply to its SG type" [err1, err2, err3, err4]

is_wf_ty::(Eq a, Eq b)=>(Maybe MK)->(GrwT a b, SGr a b)->Bool
is_wf_ty Nothing          = is_wf_gwt_sg 
is_wf_ty (Just WeakM)     = is_wf_gwt_sg 
is_wf_ty (Just PartialM)  = (\(gwt, sg)->gwt `ty_complies` sg)
is_wf_ty (Just TotalM)    = (\(gwt, sg)->gwt  `ty_complies` sg)

check_wf_ty id Nothing (gwt, sg) =check_wf_gwt_sg id gwt sg
check_wf_ty id (Just WeakM) (gwt, sg) = check_wf_gwt_sg id gwt sg
check_wf_ty id (Just PartialM) (gwt, sg) = check_ty_complies id gwt sg
check_wf_ty id (Just TotalM) (gwt, sg) = check_ty_complies id gwt sg

instance GM_CHK' GrwT SGr where
   is_wf_gm' = is_wf_ty
   check_wf_gm' = check_wf_ty

--is_wf_gwtss_sg:: Eq a => (GrwTSs a, SGr a) -> Bool
--is_wf_gwtss_sg (g, sg) = fun_total (fV g) (ans g) (ns sg)  
--   && fun_total (fE g) (es g) (esC sg)
--   && img (fE g) (ses g) `subseteq` (esSeq sg) 
--   && ((fV g) `bcomp` (src g)) `subseteq` ((srcst sg) `bcomp` (fE  g))
--   && ((fV g) `bcomp` (tgtext g)) `subseteq` ((tgtst sg) `bcomp` (fE  g))


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
--    let err1 = if fun_total (fV g) (ans g) (ns sg) then nile else cons_et "Function 'fV' is ill defined." [check_fun_total (fV g) (ans g) (ns sg)] in
--    let err2 = if fun_total (fE g) (es g) (esC sg) then nile else cons_et "Function 'fE' is ill defined." [check_fun_total (fE g) (es g) (esC sg)] in
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
--    if g `tyss_complies` sg then nile else cons_et "Errors in compliance of graph to its SG type" [err1, err2, err3, err4]

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
ns_of_ntys m sg ns = img (inv . fV $ m) (img (inv . inhst $ sg) ns)

--Gets instance edges of particular node type given a morphism
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
--    let errs2 = if node_types_preserved gm sgs sgt then nile else cons_se $ "Instance nodes fail to preserve their type kinds: " ++ (showElems' npns) in
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
--                else cons_se $ "Not all normal nodes are being mapped to in the type morphism: " ++ (show (diff (nsTys sgt [Nnrml]) (ran_of ((fV gm) `rcomp` (inhst sgt))))) in
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
--    let errs2 = if no_instances_of_abstract_tnodes gm sg then nile else cons_se (abstract_nodes_msg $ (nsTys sg [Nabst, Nenum])) in
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


