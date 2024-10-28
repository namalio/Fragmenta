------------------
-- Project: Fragmenta
-- Module: 'Grs'
-- Description: Module dedicated to Fragmenta's graphs (Grs)
-- Author: Nuno Amálio
-----------------

{-# LANGUAGE MultiParamTypeClasses #-}

module Grs (
   Gr
   , TK(..)
   , MK(..)
   , isKTotal
   , consGM
   , emptyGM
   , fV
   , fE
   , restrict
   , restrictNs
   , subtractNs
   , adjacent
   , adjacentE
   , successors
   , predecessors
   , adjacentNs
   , relOfG
   , relOfGE
   , esIncident
   , esConnect
   , acyclicG
   , nsIncident
   , disjGs
   , unionG
   , unionGs
   , unionGM
   , gid
   , ogm
   , unionGMs
   , subsumeG
   , invertG) 
where

import Gr_Cls
import Sets ( sminus, disjoint, intersec, union, Set, intoSet, singles, filterS )
import Relations
import ErrorAnalysis
    ( reportFT, reportPF, consET, consSET, nile, ErrorTree ) 
import Utils (reportWF)
import TheNil


-- projection functions
--nsG :: Gr a b -> [a]
--nsG Gr {ns_ = ns', es_ = _, src_ = _, tgt_ = _} = ns'
--esG :: Gr a b -> [b]
--esG Gr {ns_ = _, es_ = es', src_ = _, tgt_ = _} = es'
--src_g :: Gr a b -> [(b, a)]
--src_g Gr {ns_ = _, es_ = _, src_ = s, tgt_ = _} = s
--tgt_g :: Gr a b -> [(b, a)]
--tgt_g Gr {ns_ = _, es_ = _, src_ = _, tgt_ = t} = t

instance GR Gr where
   ns :: Gr a b -> Set a
   ns Gr {ns_ = ns', es_ = _, src_ = _, tgt_ = _} = ns'
   es :: Gr a b -> Set b
   es Gr {ns_ = _, es_ = es', src_ = _, tgt_ = _} = es'
   src :: Gr a b -> Rel b a
   src Gr {ns_ = _, es_ = _, src_ = s, tgt_ = _} = s
   tgt :: Gr a b -> Rel b a
   tgt Gr {ns_ = _, es_ = _, src_ = _, tgt_ = t} = t
   empty :: Gr a b
   empty = consG nil nil nil nil
--gOf g = consG (ns g) (es g) (src g) (tgt g)

okG:: (Eq a, Eq b, GR g) => g a b-> Bool
okG g = tfun (src g) (es g) (ns g) && tfun (tgt g) (es g) (ns g)

errorsG:: (GR g, Eq a, Eq b, Show a, Show b) => g a b-> [ErrorTree]
errorsG g =
   let errs1 = if tfun (src g) (es g) (ns g) then nile else consET ("Function 'src' is ill defined.") [reportFT (src g) (es g) (ns g)]
       errs2 = if tfun (tgt g) (es g) (ns g) then nile else consET ("Function 'tgt' is ill defined.") [reportFT (tgt g) (es g) (ns g)] in
   [errs1, errs2]

reportG :: (Eq a, Eq b, GR g, Show a, Show b) => String -> g a b -> ErrorTree
reportG id g = reportWF g id okG errorsG

-- Nodes of a graph connected a set of edges, either as source or target nodes
nsIncident :: (Foldable t, Eq a, Eq b, GR g) => g a b -> t b -> Set a
nsIncident g le = ran_of (dres (src g)  le) `union` ran_of (dres (tgt g)  le)

-- Incident edges of a set of nodes
esIncident :: (Foldable t, Eq a, Eq b, GR g) => g a b -> t a -> Set b
esIncident g vs = img (inv $ src g) vs `union` img (inv $ tgt g) vs

-- Connection edges of a set of nodes
esConnect :: (Foldable t, Eq a, Eq b, GR g) => g a b -> t a -> Set b
esConnect g vs = img (inv $ src g) vs `intersec` img (inv $ tgt g) vs

-- Restricts a graph to a given set of edges
restrict :: (GR g, Eq b, Eq a) => g a b -> Set b -> Gr a b
restrict g as = 
   let es' = es g `intersec` as in
   let s = dres (src g) as in
   let t = dres (tgt g) as in
   consG (nsIncident g as) es' s t

-- Restricts a graph to a given set of nodes
restrictNs :: (GR g, Eq b, Eq a) => g a b -> Set a -> Gr a b
restrictNs g vs = 
   let ns' = ns g `intersec` vs in
   let es' = esConnect g vs in
   let s = dres (src g) es' in
   let t = dres (tgt g) es' in
   consG ns' es' s t

-- Subtracts nodes from a graph 
subtractNs :: (GR g, Eq b, Eq a) => g a b -> Set a -> Gr a b
subtractNs g vs = 
   let ns' = ns g `sminus` vs in
   let es' = es g `sminus` esIncident g vs in
   let s = dsub (src g) (esIncident g vs) in
   let t = dsub (tgt g) (esIncident g vs) in
   consG ns' es' s t


--function that yields the map of a source function
--esId_g g = filter (\e-> appl (src g) e == appl (tgt g) e)(es g)

-- Gives all successor nodes of a given node in a given graph
successors :: (Foldable t, GR g, Eq a, Eq b) => g a b -> t a -> Set a
successors g vs = img (tgt g) $ img (inv . src $ g) vs

-- Gives all predecessor nodes of a given node in a given graph
predecessors :: (Foldable t, GR g, Eq a, Eq b) => g a b -> t a -> Set a
predecessors g vs =  img (src g) $ img (inv . tgt $ g) vs
--img (src g) $ filter (\e-> appl (tgt g) e == v) (es g)

--Gives all nodes adjacent to a set of nodes (sucessors and predecessors)
adjacentNs :: (Foldable t, GR g, Eq a, Eq b) => g a b -> t a -> Set a
adjacentNs g vs = (successors g vs) `union` (predecessors g vs)

-- Graph adjency: whether one node is adjacent to another
adjacent::(GR g, Eq a, Eq b) => g a b->a->a->Bool
adjacent g v1 v2 = 
   any (\e-> img (src g) [e] == (singles v1) && img (tgt g) [e] == singles v2) (es g)

adjacentE::(GR g, Eq a, Eq b) => g a b->b->b->Bool
adjacentE g e1 e2 = appl (src g) e1 == appl (src g) e2

-- Inverts a graph
invertG :: (GR g, Eq a, Eq b) => g a b -> Gr a b
invertG g = consG (ns g) (es g) (tgt g) (src g)
 
-- gets adjacency relation between nodes induced by graph
relOfG :: (GR g, Eq a, Eq b) => g a b-> Rel a a
relOfG g = foldr (\e r-> (appl (src g) e, appl (tgt g) e) `intoSet` r) nil (es g)

-- gets adjacency relation between edges induced by graph
relOfGE :: (GR g, Eq a, Eq b) => g a b-> Rel b b
relOfGE g = foldr (\e r-> singles e `cross` (img (inv . src $ g) (singles $ appl (tgt g) e)) `union` r) nil (es g)

-- checks whether a graph is acyclic
acyclicG::(Eq a, Eq b, GR g) => g a b->Bool
acyclicG = acyclic . relOfGE

-- Total function check on 'fV'
totalfV::(Eq a, Eq b, GR g) => (g a b, GrM a b, g a b) -> Bool
totalfV (gs, m, gt) = tfun (fV m) (ns gs) (ns gt)

-- Total function check on 'fE'
totalfE::(Eq a, Eq b, GR g) => (g a b, GrM a b, g a b) -> Bool
totalfE (gs, m, gt) = tfun (fE m) (es gs) (es gt)

-- Partial function check on 'fV'
partialfV::(Eq a, Eq b, GR g) => (g a b, GrM a b, g a b) -> Bool
partialfV (gs, m, gt) = pfun (fV m) (ns gs) (ns gt)

-- Partial function check on 'fE'
partialfE::(Eq a, Eq b, GR g) => (g a b, GrM a b, g a b) -> Bool
partialfE (gs, m, gt) = pfun (fE m) (es gs) (es gt)

-- Checks whether the source function commutes
morphism_commutes_src (gs, m, gt) = (src gt) `bcomp` (fE m)  == (fV m) `bcomp` (src gs) 
pmorphism_commutes_src (gs, m, gt) = (src gt) `bcomp` (fE m)  == (fV m) `bcomp` (dres (src gs) (dom_of . fE $ m)) 
morphism_commutes_tgt (gs, m, gt) = (tgt gt) `bcomp` (fE m) == (fV m) `bcomp` (tgt gs)  
pmorphism_commutes_tgt (gs, m, gt) = (tgt gt) `bcomp` (fE m)  == (fV m) `bcomp` (dres (tgt gs) (dom_of . fE $ m))

-- Well-formedness of total morphisms
wfGM:: (Eq a, Eq b, GR g) => (g a b, GrM a b, g a b) -> Bool
wfGM (gs, m, gt) = totalfV (gs, m, gt) && totalfE (gs, m, gt)
   && morphism_commutes_src (gs, m, gt)
   && morphism_commutes_tgt (gs, m, gt)

-- Well-formedness of partial morphisms
wfPGM:: (Eq a, Eq b, GR g) => (g a b, GrM a b, g a b) -> Bool
wfPGM (gs, m, gt) = partialfV (gs, m, gt) && partialfE (gs, m, gt)
   && pmorphism_commutes_src (gs, m, gt)
   && pmorphism_commutes_tgt (gs, m, gt)

instance G_WF_CHK Gr where
   okayG :: (Eq a, Eq b) => Maybe TK -> Gr a b -> Bool
   okayG _ = okG
   faultsG :: (Eq a, Eq b, Show a, Show b) =>String -> Maybe TK -> Gr a b -> ErrorTree
   faultsG id _ = reportG id

instance GM_CHK Gr Gr where
   okayGM :: (Eq a, Eq b) => Maybe MK -> (Gr a b, GrM a b, Gr a b) -> Bool
   okayGM (Just WeakM) = wfPGM
   okayGM _ = wfGM
   faultsGM :: (Eq a, Eq b, Show a, Show b) =>String -> Maybe MK -> (Gr a b, GrM a b, Gr a b) -> ErrorTree
   faultsGM nm (Just WeakM) = reportPGM nm
   faultsGM nm _ = reportGM nm

--check_gr_wf:: (GR g, Eq a, Show a) => String -> g a -> IO () 
--check_gr_wf g_id g = 
--   let errs = check_wf_g g_id g in
--   if null errs 
--      then putStrLn $ "Graph " ++ g_id ++ " is well forfEd" 
--      else putStrLn $ "Graph " ++ g_id ++ " is not well-forfEd. " ++ (show errs) 

errorsGM:: (GR g, Eq a, Eq b, Show a, Show b) => (g a b, GrM a b, g a b) -> [ErrorTree]
errorsGM (gs, m, gt) =
   let err1 = if totalfV (gs, m, gt) then nile else consET "Function 'fV' is ill defined." [reportFT (fV m) (ns gs) (ns gt)] in
   let err2 = if totalfE (gs, m, gt) then nile else consET "Function 'fE' is ill defined." [reportFT (fE m) (es gs) (es gt)] in
   let err3 = if morphism_commutes_src (gs, m, gt) then nile else consSET "Problems in the commuting of the source functions" in
   let err4 = if morphism_commutes_tgt (gs, m, gt) then nile else consSET "Problems in the commuting of the target functions" in
   [err1,err2,err3,err4]

errorsPGM:: (GR g, Eq a, Eq b, Show a, Show b) => (g a b, GrM a b, g a b) -> [ErrorTree]
errorsPGM (gs, m, gt) =
   let err1 = if partialfV (gs, m, gt) then nile else consET "Function 'fV' is ill defined." [reportPF (fV m) (ns gs) (ns gt)] in
   let err2 = if partialfE (gs, m, gt) then nile else consET "Function 'fE' is ill defined." [reportPF (fE m) (es gs) (es gt)] in
   let err3 = if pmorphism_commutes_src (gs, m, gt) then nile else consSET "Problems in the commuting of the source functions" in
   let err4 = if pmorphism_commutes_tgt (gs, m, gt) then nile else consSET "Problems in the commuting of the target functions" in
   [err1,err2,err3,err4]

reportGM:: (GR g, Eq a, Eq b, Show a, Show b) => String-> (g a b, GrM a b, g a b) -> ErrorTree
reportGM nm (gs, gm, gt) = reportWF (gs, gm, gt) nm (wfGM) (errorsGM)

reportPGM:: (GR g, Eq a, Eq b, Show a, Show b) => String-> (g a b, GrM a b, g a b) -> ErrorTree
reportPGM nm (gs, gm, gt) = reportWF (gs, gm, gt) nm (wfPGM) (errorsPGM)

--reportGM' nm Nothing = check_wf_gm_g nm 

disjGs gs = disjoint (map ns gs) && disjoint (map es gs)

-- graph union
unionG :: (Eq b, Eq a, GR g1, GR g2) => g1 a b -> g2 a b -> Gr a b
unionG g1 g2 = 
   let ns' = ns g1 `union` ns g2 in
   let es' = es g1 `union` es g2 in
   let s = src g1 `union` src g2 in
   let t = tgt g1 `union` tgt g2 in
   consG ns' es' s t

-- generalised graph union
unionGs::(Foldable t, Eq a, Eq b, GR g)=>t (g a b)->Gr a b
unionGs = foldl (\gacc g-> gacc `unionG` g) empty

-- graph subsumption: takes a graph and a substituion mapping
subsumeG :: (Eq a, Eq b) => Gr a b -> Rel a a -> Gr a b
subsumeG g sub =
   let total_ns = sub `mktotal_in` ns g in
   let g' = consG ((ns g `sminus` dom_of sub) `union` (ran_of sub)) (es g) (total_ns `bcomp` src g) (total_ns `bcomp` tgt g) in
   if pfun sub (ns g) (ns g) then g' else g

-- Identity morphism over a graph
gid::(Eq a, Eq b, GR g)=>g a b->GrM a b
gid g = consGM (id_on . ns $ g) (id_on . es $ g)

-- Domain of a graph morphism
--domg :: (GRM gm, Eq a, Eq b) => gm a b -> (Set a, Set b)
--domg gm = (dom_of . fV $ gm, dom_of . fE $ gm)

-- Co-domain of a graph morphism
codg :: (GRM gm, Eq a, Eq b) => gm a b -> (Set a, Set b)
codg gm = (ran_of . fV $ gm, ran_of . fE $ gm)

-- Union on graph morphisms
unionGM gm1 gm2 = consGM ((fV gm1) `union` (fV gm2)) ((fE gm1) `union` (fE gm2))

-- Generalised union for graph morphisms 
unionGMs gms = foldl (\gmacc gm-> gmacc `unionGM` gm) emptyGM gms

-- Morphism composition
ogm :: (Eq a, Eq b, GRM gm1, GRM gm2) => gm1 a b -> gm2 a b -> GrM a b
ogm g f = consGM (fV g `bcomp` fV f) (fE g `bcomp` fE f)

--replace_in_gm gm subs_ns_dom subs_ns_ran =
--   let ns_dom' = substitute (map fst (fV gm)) subs_ns_dom in
--   let ns_ran' = substitute (map snd (fV gm)) subs_ns_ran in
--   cons_gm (zip ns_dom' ns_ran') (fE gm)

-- Registricts an instance graph to a set of edge types given a morphism
--REMOVE LATER IF UNNECESSARY
--restrictGToTyEdges m g tes = restrict g (img (inv . fE $ m) tes)
