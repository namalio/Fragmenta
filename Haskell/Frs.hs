-------------------------
-- Project: PCs/Fragmenta
-- Module: 'Frs'
-- Description: Fragmenta's fragments (Frs)
-- Author: Nuno Amálio
---------------------------
{-# LANGUAGE MultiParamTypeClasses #-}

module Frs(Fr
    , srcR
    , tgtR
    , esR
    , fsg
    , fet
    , fLNs
    , consF
    , unionF
    , disjFs
    , rep_ns_of_fs
    , rep_es_of_fs
    , refs
    , unionFs
    , reso_f
    , mres
    , rEtCompliesF) where

import Gr_Cls
import Grs ( acyclicG, ogm, relOfG, unionGM, Gr )
import SGrs
import Sets
import Relations
    ( tfun,
      rcomp,
      mktotal_in,
      cl_override,
      inv,
      tfun',
      fun_bij,
      dres,
      rsub,
      dom_of,
      rres,
      ran_of,
      Rel )
import ErrorAnalysis
import Utils
import GrswT
import GrswET
import ShowUtils
import SimpleFuns
import TheNil

data Fr a b = Fr {
   sg_ :: SGr a b
   , esr_ :: Set b
   , sr_  :: Rel b a
   , tr_ :: Rel b a
   , et_ :: GrM a b
} deriving (Eq, Show)

-- Fragment's SG
fsg :: Fr a b -> SGr a b
fsg Fr {sg_ = sg, esr_ = _, sr_ = _, tr_ = _} = sg
-- Fragmet's reference edges
esR :: Fr a b -> Set b
esR Fr {sg_ = _, esr_ = es, sr_ = _, tr_ = _} = es
-- Fource function of reference edges
srcR :: Fr a b -> Rel b a
srcR Fr {sg_ = _, esr_ = _, sr_ = s, tr_ = _} = s
-- Target function of reference edges
tgtR :: Fr a b -> Rel b a
tgtR Fr {sg_ = _, esr_ = _, sr_ = _, tr_ = t} = t

-- Fragment's Extra typing morphism
fet :: Fr a b -> GrM a b
fet Fr {sg_ = _, esr_ = _, sr_ = _, tr_ = _, et_ = et} = et

-- Constructor of fragments
consF::SGr a b->Set b-> Rel b a-> Rel b a->GrM a b->Fr a b
consF sg es s t et = Fr {sg_ = sg, esr_ = es, sr_ = s, tr_ = t, et_ = et} 

-- Constructs the empty fragment
emptyF :: Fr a b
emptyF = consF empty nil nil nil emptyGM

-- Gets the local edges of a fragment (exclude reference edges)
fLEs::(Eq a, Eq b)=>Fr a b->Set b
fLEs = es . fsg 

-- Gets all edges of a fragment (includes reference edges)
fEs::(Eq a, Eq b)=>Fr a b->Set b
fEs f = fLEs f `union` esR f

-- Gets all association edges of a fragment
fEsA::(Eq a, Eq b)=>Fr a b->Set b
fEsA = esA . fsg

-- Gets all local nodes of a fragment (excludes foreign references)
fLNs::(Eq a, Eq b)=>Fr a b->Set a
fLNs = ns . fsg 

-- Gets all reference of a fragment (all references of proxies, including foreign ones)
fRNs::(Eq a, Eq b)=>Fr a b->Set a
fRNs = ran_of . tgtR

-- Gets all nodes involved in a fragment, including including foreign references
fNs::(Eq a, Eq b)=>Fr a b->Set a
fNs f = (fLNs f) `union` (fRNs f)

-- Source function which caters to all edges including reference edges
srcF::(Eq a, Eq b)=>Fr a b->Rel b a
srcF f = (src . fsg $ f) `union` (srcR f)

-- Target function which caters to all edges including reference edges
tgtF::(Eq a, Eq b)=>Fr a b->Rel b a
tgtF f = (tgt . fsg $ f) `union` (tgtR f)

-- Gets references graph
refsG::(Eq a, Eq b)=>Fr a b->Gr a b
refsG f = consG ns' (esR f) (srcR f) (tgtR f)
    where ns' = (nsP . fsg $ f) `union` fRNs f

-- References function obtained from references graph
refs::(Eq a, Eq b)=>Fr a b->Rel a a 
refs = relOfG . refsG 

-- Union of fragments 
unionF :: (Eq a, Eq b)=>Fr a b -> Fr a b -> Fr a b
unionF f1 f2 = consF usg uesr usr utr uet
            where usg = fsg f1 `unionSG` fsg f2
                  uesr = esR f1 `union` esR f2
                  usr = srcR f1 `union` srcR f2
                  utr = tgtR f1 `union` tgtR f2
                  uet = fet f1 `unionGM` fet f2

-- distributed union of fragments 
unionFs :: (Eq a, Eq b,Foldable t) => t (Fr a b) -> Fr a b
unionFs fs = foldr (\f ufs->f `unionF` ufs) emptyF fs

-- Checks whether fragments are disjoint
disjFs :: (Eq a, Eq b) => [Fr a b] -> Bool
disjFs fs = disjoint (map fLNs fs) && disjoint (map fEs fs) 

-- Gets the repeated nodes of fragments
rep_ns_of_fs::(Eq a, Eq b)=>Set (Fr a b)->Set a
rep_ns_of_fs fs = dups . gunion $ fmap fLNs fs

-- Gets the repeated edges of fragments
rep_es_of_fs::(Eq a, Eq b)=>Set (Fr a b)->Set b
rep_es_of_fs fs = dups . gunion $ fmap fEs fs
-- ++ (dups . gapp $ map fEs fs)

-- Resolution function, which restricts range of references function to the local nodes (those that can be resolved locally)
res::(Eq a, Eq b)=>Fr a b->Rel a a
res f = rres (refs f) (fLNs f)

-- Constructs resolved SG (◉ operator, subsumption)
reso_sg::(Eq a, Eq b)=>Fr a b->SGr a b
reso_sg f = subsume_sg (fsg f) (res f)

-- Gives reference edges of the resolved fragment, which removes those reference edges that are resolved
rEsR::(Eq a, Eq b)=>Fr a b->Set b
rEsR f = dom_of (rsub (srcR f) $ dom_of (res f))

-- Constructs resolved fragment (◉ F)
reso_f::(Eq a, Eq b)=>Fr a b->Fr a b
reso_f f = consF (reso_sg f) es' (dres (srcR f) es') (dres (tgtR f) es') (fet f)
    where es' = rEsR f

-- Base well-formedness predicate
okayFz :: (Eq a, Eq b) => Fr a b -> Bool
okayFz f = okayG Nothing (fsg f) && disjoint [fLEs f, esR f] 
    && fun_bij (srcR f) (esR f) (nsP . fsg $ f) 
    && tfun' (tgtR f) (esR f) 
    && domg (fet f) <= (nsN . fsg $ f, fEsA f)
    -- && disjoint [ran_of . tgtR $ f, nsO . fsg $ f]

-- Base well-formedness with acyclicity
okayFa :: (Eq a, Eq b) => Fr a b -> Bool
okayFa f = okayFz f && acyclicG (refsG f)

-- Partial well-formedness of fragments (last predicate could be proved and hence removed)
okayF :: (Eq a, Eq b) => Fr a b -> Bool
okayF f = okayFa f && okayG (Just Partial) (reso_sg f)

-- Says whether flow of references goes from one fragment into another
refs_in :: (Eq b1, Eq b2) => Fr b1 a -> Fr b1 b2 -> Bool
refs_in f1 f2 = ran_of (tgtR f1) <= fLNs f2

-- Says whether flow of references is uni-directional (from one fragment into another, but not the reverse)
oneway f1 f2 = f1 `refs_in` f2 && (not $ f2 `refs_in` f1)

-- checks whether references are local
refsLocal :: (Eq a, Eq b) => Fr a b -> Bool
refsLocal f = fRNs f <= fLNs f

-- Well-formedness of total fragments
okayTF :: (Eq a, Eq b) => Fr a b -> Bool
okayTF f = okayFa f && refsLocal f && okayG (Just Total) (reso_sg f)

errsFz::(Eq a, Eq b, Show a, Show b)=>String->Fr a b -> [ErrorTree]
errsFz nm f =
    let err1 = faultsG ("SG (" ++ nm ++ ")") (Just Partial) (fsg f) in
    let err2 = if disjoint [(fLEs f), esR f] then nile else consSET "Sets of SG edges and reference edges are not disjoint" in 
    let err3 = if fun_bij (srcR f) (esR f) (nsP .fsg $ f) then nile 
        else consET "Function 'srcR' is not bijective " [reportFB (srcR f) (esR f) (nsP .fsg $ f)] in
    let err4 = if tfun' (tgtR f) (esR f) then nile else consET "Function 'tgtR' is not total" [reportFT' (tgtR f) (esR f)] in
    [err1, err2, err3, err4]

--reportFz :: (Eq a, Eq b, Show a, Show b) => String -> Fr a b -> ErrorTree
--reportFz nm f = reportWF f nm okayFz (errsFz nm)

errsFa::(Eq a, Eq b, Show a, Show b)=>String->Fr a b -> [ErrorTree]
errsFa nm f = 
    let errs1 = errsFz nm f in
    let err2 = if acyclicG (refsG f) then nile else consSET "The fragment's references contains cycles" in
    errs1 ++ [err2]

errsF::(Eq a, Eq b, Show a, Show b)=>String->Fr a b -> [ErrorTree]
errsF nm f = 
    let errs1 = errsFa nm f in
    let err2 = faultsG ("Resolved SG (" ++ nm ++ ")") (Just Partial) (reso_sg f) in
    errs1 ++ [err2]

rOkayF :: (Eq a, Eq b, Show a, Show b) => String -> Fr a b -> ErrorTree
rOkayF nm f = reportWF f nm okayF (errsF nm)

errsTF::(Eq a, Eq b, Show a, Show b)=>String->Fr a b -> [ErrorTree]
errsTF nm f = 
    let errs = errsFa nm f in
    let err2 = if refsLocal f then nile else consSET $ "Some proxy references are foreign (or not local): " ++ (showNodes (sminus (fRNs f) (fLNs f))) in
    let err3 = faultsG ("Resolved SG (" ++ nm ++ ")") (Just Total) (reso_sg f) in
    errs ++ [err2, err3]

rOkayTF :: (Eq a, Eq b, Show a, Show b) => String -> Fr a b -> ErrorTree
rOkayTF id f = reportWF f id okayTF (errsTF id) -- check_wf_of f nm is_wf_tf (errors_tfr nm)

instance G_WF_CHK Fr where
   okayG :: (Eq a, Eq b) => Maybe TK -> Fr a b -> Bool
   okayG Nothing = okayFz
   okayG (Just Total) = okayTF
   okayG (Just Partial) = okayF
   faultsG :: (Eq a, Eq b, Show a, Show b) =>String -> Maybe TK -> Fr a b -> ErrorTree
   faultsG id Nothing f = reportWF f id okayFz (errsFz id)
   faultsG id (Just Partial) f = rOkayF id f 
   faultsG id (Just Total) f   = rOkayTF id f --okayTF (errsTF id)

-- morphism resolution operation
mres :: (GRM gm, Eq a, Eq b) =>gm a b -> (Fr a b, Fr a b) -> GrM a b
mres m (fs, ft) = 
    let mv = (inv $ (cl_override $ res fs) `mktotal_in` (fLNs fs)) `rcomp` ((fV m) `rcomp` ((cl_override $ res ft) `mktotal_in` (fLNs ft))) in
    consGM mv (fE m)

-- Checks that a morphism between fragments is well-formed 
okayFGM :: (GRM gm, Eq a, Eq b, GNodesNumConv a) => (Fr a b, gm a b, Fr a b) -> Bool
okayFGM (fs, m, ft) = tfun (fV m) (fLNs fs) (fLNs ft) 
    && tfun (fE m) (fEsA fs) (fEsA ft)
    && okayGM (Just WeakM) (reso_sg fs, mres m (fs, ft), reso_sg ft)

errsFGM :: (Eq a, Eq b, Show a, Show b, GRM gm, GNodesNumConv a) 
    =>(Fr a b, gm a b, Fr a b) -> [ErrorTree]
errsFGM (fs, m, ft) = 
    let err1 = if tfun (fV m) (fLNs fs) (fLNs ft) then nile 
        else consET "Function 'fV' is not total" [reportFT (fV m) (fLNs fs) (fLNs ft)] in
    let err2 = if tfun (fE m) (fEsA fs) (fEsA ft) then nile 
        else consET "Function 'fE' is not total" [reportFT (fE m) (fEsA fs) (fEsA ft)] in
    let err3 = faultsGM "Resolved Morphism between SGs of resolved fragments" (Just WeakM) (reso_sg fs, mres m (fs, ft), reso_sg ft) in
    [err1, err2, err3]

reportFGM::(GRM gm, Eq a, Eq b, Show a, Show b, GNodesNumConv a)=>String->(Fr a b, gm a b, Fr a b)->ErrorTree
reportFGM nm (fs, m, ft) = reportWF (fs, m, ft) nm okayFGM errsFGM

-- Partial fragment refinement
frefines::(Eq a, Eq b, GRM gm, GNodesNumConv a)=>(Fr a b, gm a b)->Fr a b->Bool
frefines (fc, m) fa = okayFGM (fc, m, fa) 
    && sg_refinesz (reso_sg fc, mres m (fc, fa)) (reso_sg fa)

errs_frefines::(Eq a, Eq b, Show a, Show b, GRM gm, GNodesNumConv a) =>String->(Fr a b, gm a b)->Fr a b->[ErrorTree]
errs_frefines nm (fc, m) fa =
    let err1 = reportFGM nm (fc, m, fa) in
    let errs2 = errs_sg_refinesz (reso_sg fc, mres m (fc, fa)) (reso_sg fa) in
    (err1:errs2)

report_frefines :: (Eq a, Eq b, GRM gm, Show a, Show b, GNodesNumConv a) 
    =>String-> (Fr a b, gm a b, Fr a b) -> ErrorTree
report_frefines nm (fc, m, fa) = reportWF (fc, m, fa) nm (appl frefines) (appl $ errs_frefines nm)
    where appl f = (\(fc, m, fa)->f (fc, m) fa)

-- Total fragment refinement
tfrefines::(GRM gm, Eq a, Eq b, GNodesNumConv a)=>(Fr a b, gm a b)->Fr a b->Bool
tfrefines (fc, m) fa = okayFGM (fc, m, fa) 
    && okayG (Just Total) fc 
    && okayG (Just Total) fa
    && tsg_refinesz (reso_sg fc, mres m (fc, fa)) (reso_sg fa)

errs_tfrefines :: (Eq a, Eq b, Show a, Show b, GRM gm, GNodesNumConv a) 
    =>String -> (Fr a b, gm a b) -> Fr a b -> [ErrorTree]
errs_tfrefines nm (fc, m) fa =
    let err1 = reportFGM nm (fc, m, fa) in
    let err2 = rOkayTF "Fragment concrete" fc in
    let err3 = rOkayTF "Fragment abstract" fa in
    let errs = errs_tsg_refinesz (reso_sg fc, mres m (fc, fa)) (reso_sg fa) in
    (err1:err2:err3:errs)

report_tfrefines nm (fc, m, fa) = reportWF (fc, m, fa) nm (appl tfrefines) (appl $ errs_tfrefines nm)
    where appl f = (\(fc, m, fa)->f (fc, m) fa)

--is_wf_fgm' Nothing         = is_wf_fgm  
--is_wf_fgm' (Just WeakM)    = is_wf_fgm 
--is_wf_fgm' (Just PartialM) = (\(fc, m, fa)-> frefines (fc, m) fa)
--is_wf_fgm' (Just TotalM)   = (\(fc, m, fa)-> tfrefines (fc, m) fa)

--check_wf_fgm' id Nothing         = check_wf_fgm id
--check_wf_fgm' id (Just WeakM)    = check_wf_fgm id
--check_wf_fgm' id (Just PartialM) = check_frefines id
--check_wf_fgm' id (Just TotalM)   = check_tfrefines id

instance GM_CHK Fr Fr where
   --okayGM :: (Eq a, Eq b) => Maybe MK -> (Fr a b, GrM a b, Fr a b) -> Bool
   okayGM Nothing      = okayFGM
   okayGM (Just WeakM) = okayFGM
   okayGM (Just PartialM) = \(fc, m, fa)->frefines (fc, m) fa
   okayGM (Just TotalM) = \(fc, m, fa)-> tfrefines (fc, m) fa
   --faultsGM :: (Eq a, Eq b, Show a, Show b) =>String-> Maybe MK->(Fr a b, GrM a b, Fr a b)->ErrorTree
   faultsGM id Nothing         = reportFGM id
   faultsGM id (Just WeakM)    = reportFGM id
   faultsGM id (Just PartialM) = report_frefines id
   faultsGM id (Just TotalM)   = report_tfrefines id

gwtCompliesf::(Eq a, Eq b, Read a, GNodesNumConv a, GNumSets a)=>GrwT a b->Fr a b->Bool
gwtCompliesf gwt f = okayGM' (Just PartialM) (gwt, reso_sg f)

rgwtCompliesf::(Eq a, Eq b, Read a, Show a, Show b, GNodesNumConv a, GNumSets a)=>String->GrwT a b->Fr a b->ErrorTree
rgwtCompliesf id gwt f = faultsGM' id (Just PartialM) (gwt, reso_sg f)

--is_wf_ty::(Eq a, Eq b)=>(Maybe MK)->(GrwT a b, Fr a b)->Bool
--is_wf_ty Nothing (gwt, f)         = okayGM' Nothing (gwt, reso_sg f)
--is_wf_ty (Just WeakM) (gwt, f)    = okayGM' (Just WeakM) (gwt,  reso_sg f) 
--is_wf_ty (Just PartialM) (gwt, f) = gwt `ty_compliesf` f
--is_wf_ty (Just TotalM) (gwt, f)   = gwt  `ty_compliesf` f

--check_wf_ty id Nothing (gwt, f) = faultsGM' id Nothing (gwt,  reso_sg f)
--check_wf_ty id (Just WeakM) (gwt, f) = faultsGM' id  (Just WeakM) (gwt,  reso_sg f)
--check_wf_ty id (Just PartialM) (gwt, f) = check_ty_compliesf id gwt f
--check_wf_ty id (Just TotalM) (gwt, f) = check_ty_compliesf id gwt f

instance GM_CHK' GrwT Fr where
   okayGM' Nothing (gwt, f)      = okayGM' Nothing (gwt, reso_sg f)
   okayGM' (Just WeakM) (gwt, f) = okayGM' (Just WeakM) (gwt,  reso_sg f) 
   okayGM' (Just PartialM) (gwt, f) = gwt `gwtCompliesf` f
   okayGM' (Just TotalM) (gwt, f)   = gwt  `gwtCompliesf` f
   faultsGM' id Nothing (gwt, f) = faultsGM' id Nothing (gwt,  reso_sg f)
   faultsGM' id (Just WeakM) (gwt, f) = faultsGM' id  (Just WeakM) (gwt,  reso_sg f)
   faultsGM' id (Just PartialM) (gwt, f) = rgwtCompliesf id gwt f
   faultsGM' id (Just TotalM) (gwt, f) = rgwtCompliesf id gwt f

instance GM_CHK' GrwET Fr where
   --okayGM' :: (Eq a, Eq b, GNodesNumConv a, GNumSets) => Maybe MK -> (GrwET a b, Fr a b) -> Bool
   okayGM' Nothing (gwet, f) = okayGM' Nothing (ggwt gwet, reso_sg f)
   okayGM' (Just WeakM) (gwet, f) = okayGM' (Just WeakM) (ggwt gwet,  reso_sg f) 
   okayGM' (Just PartialM) (gwet, f) = ggwt gwet `gwtCompliesf` f
   okayGM' (Just TotalM) (gwet, f)   = ggwt gwet  `gwtCompliesf` f
   --faultsGM' :: (Eq a, Eq b, Show a, Show b) =>String ->Maybe MK ->(GrwET a b, Fr a b)->ErrorTree
   faultsGM' id Nothing (gwet, f) = faultsGM' id Nothing (ggwt gwet,  reso_sg f)
   faultsGM' id (Just WeakM) (gwet, f) = faultsGM' id  (Just WeakM) (ggwt gwet,  reso_sg f)
   faultsGM' id (Just PartialM) (gwet, f) = rgwtCompliesf id (ggwt gwet) f
   faultsGM' id (Just TotalM) (gwet, f) = rgwtCompliesf id (ggwt gwet) f

-- Checks whether one fragment is extra typed by another, which requires that:
-- (i) that the extra typing morphism is defined
-- and (ii) and that the underpinning SGs are compatible
okayETCFs::(Eq a, Eq b) =>Fr a b->Fr a b->Bool
okayETCFs fs ft = (not . isEmptyGM . fet $ fs) && okETSGs (reso_sg fs, fet fs) (reso_sg ft)

-- checks whether a graph with extra typing complies to: 
-- (i) its type fragment F1,
-- (ii) the given instance graph complies to its type fragment F2,
-- (iii) the domain of the extra typing morphism is the same as the domain of the typing morphism composed with the fragemnt's extra typing,
-- (iv) the extra typing is a partial morphism from the instance graph into the type graph,
-- (v) the graph's type fragment is an instance of the fragment which is a type of the given extra type graph (okayETFs)
etCompliesF::(Eq a, Eq b, Read a, GNodesNumConv a, GNumSets a) =>(GrwET a b, Fr a b)->(GrwT a b, Fr a b)->Bool
etCompliesF (gwet, f1) (gwt, f2) = 
    okayGM' (Just PartialM) (gwet, f1)
    && okayGM' (Just PartialM) (gwt, f2) 
    && domg (etm gwet) == domg (fet f1 `ogm` ty gwet) 
    && okayGM (Just WeakM) (gOf gwet, etm gwet, gOf gwt)
    && okayETCFs f1 f2

--errsWfETFs::(Eq a, Eq b, Show a, Show b)=>String->Fr a b->Fr a b->[ErrorTree]
--errsWfETFs id fs ft = 
--    let err = if wfETFs fs ft then nile else consET "Invalid extra typing" [rWfETSGs id (reso_sg fs, fet fs) (reso_sg ft)] in
--    [err]

errsOkayETFs::(Eq a, Eq b, Show a, Show b)=>String->Fr a b->Fr a b->[ErrorTree]
errsOkayETFs id fs ft = 
    let err1 = if not . isEmptyGM . fet $ fs then nile else consSET "Source fragment has no extra typing morphism"
        err2 = rOkETSGs id (reso_sg fs, fet fs) (reso_sg ft) in
    [err1, err2]

rOkayETCFs::(Eq a, Eq b, Show a, Show b)=>String->Fr a b->Fr a b->ErrorTree
rOkayETCFs id fs ft = 
    let err = if okayETCFs fs ft then nile else consET (id ++ " is invalid") (errsOkayETFs id fs ft) in
    err

errsEtCompliesF::(Eq a, Eq b, Read a, Show a, Show b, GNodesNumConv a, GNumSets a)=>
    String->GrwET a b->Fr a b->GrwT a b->Fr a b->[ErrorTree]
errsEtCompliesF id gwet f1 gwt f2 = 
    let err1 = faultsGM' id (Just PartialM) (gwet, f1)
        err2 = faultsGM' id (Just PartialM) (gwt, f2) 
        s1 = domg (etm gwet)
        s2 = domg (fet f1 `ogm` ty gwet)
        err3 = if s1 == s2 then nile else consET "Extra typing is missing extra typed elements" [reportSPEq s1 s2]
        err4 = faultsGM id (Just WeakM) (gOf gwet, etm gwet, gOf gwt)
        err5 = rOkayETCFs id f1 f2 in
    [err1, err2, err3, err4, err5]

rEtCompliesF::(Eq a, Eq b, Read a, Show a, Show b, GNodesNumConv a, GNumSets a)
    =>String->(GrwET a b, Fr a b)->(GrwT a b, Fr a b)->ErrorTree
rEtCompliesF id (gwet, f1) (gwt, f2) = 
   let errs = errsEtCompliesF id gwet f1 gwt f2 in
   if etCompliesF (gwet, f1) (gwt, f2)  then nile else consET ("Errors with extra typing compliance with " ++ id) errs

instance ET_GM_CHK GrwET GrwT Fr where
    okayETGM  = etCompliesF 
    faultsETGM = rEtCompliesF


instance GET Fr where
    etc = fet

instance Ok_ETC_CHK Fr where
    okETC = okayETCFs
    faultsETC = rOkayETCFs
