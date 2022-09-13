-------------------------
-- Project: PCs/Fragmenta
-- Module: 'Frs'
-- Description: Fragmenta's fragments (Frs)
-- Author: Nuno Amálio
---------------------------
{-# LANGUAGE MultiParamTypeClasses #-}

module Frs(Fr, srcR, tgtR, esR, fsg, cons_f, union_f, disj_fs, rep_ns_of_fs, rep_es_of_fs, refs, union_fs, reso_f, mres) where

import Gr_Cls
import Grs
import SGrs
import Sets
import Relations
import ErrorAnalysis
import Utils
import GrswT
import ShowUtils
import SimpleFuns

data Fr a b = Fr {
   sg_ :: (SGr a b), 
   esr_ :: [b],
   sr_  :: [(b, a)],
   tr_ :: [(b, a)]
} deriving (Eq, Show)

-- Gets fragmet's SG
fsg Fr {sg_ = sg, esr_ = _, sr_ = _, tr_ = _} = sg
-- Gets fragmet's reference edges
esR Fr {sg_ = _, esr_ = es, sr_ = _, tr_ = _} = es
-- Gets source function of reference edges
srcR Fr {sg_ = _, esr_ = _, sr_ = s, tr_ = _} = s
-- Gets target function of reference edges
tgtR Fr {sg_ = _, esr_ = _, sr_ = _, tr_ = t} = t

-- constructor of fragment
cons_f sg es s t = Fr {sg_ = sg, esr_ = es, sr_ = s, tr_ = t} 

-- The empty fragment
empty_f = cons_f (empty_sg) [] [] []

-- Gets the local edges of a fragment (exclude reference edges)
fLEs::(Eq a, Eq b)=>Fr a b->[b]
fLEs = es . fsg 

-- Gets all edges of a fragment (includes reference edges)
fEs::(Eq a, Eq b)=>Fr a b->[b]
fEs f = fLEs f `union` esR f

fEsC::(Eq a, Eq b)=>Fr a b->[b]
fEsC = esC . fsg

-- Gets all local nodes of a fragment (excludes foreign references)
fLNs::(Eq a, Eq b)=>Fr a b->[a]
fLNs = ns . fsg 

-- Gets all reference of a fragment (all references of proxies, including foreign ones)
fRNs::(Eq a, Eq b)=>Fr a b->[a]
fRNs = ran_of . tgtR

-- Gets all nodes involved in a fragment, including including foreign references
fNs::(Eq a, Eq b)=>Fr a b->[a]
fNs f = (fLNs f) `union` (fRNs f)

-- Source function which caters to all edges including reference edges
srcF::(Eq a, Eq b)=>Fr a b->[(b, a)]
srcF f = (src . fsg $ f) `union` (srcR f)

-- Target function which caters to all edges including reference edges
tgtF::(Eq a, Eq b)=>Fr a b->[(b, a)]
tgtF f = (tgt . fsg $ f) `union` (tgtR f)

-- Gets references graph
refsG::(Eq a, Eq b)=>Fr a b->Gr a b
refsG f = cons_g ns' (esR f) (srcR f) (tgtR f)
    where ns' = (nsP . fsg $ f) `union` fRNs f

-- The references function obtained from the references graph
refs::(Eq a, Eq b)=>Fr a b->[(a, a)]
refs = relOfG . refsG 

-- union of fragments operator
union_f f1 f2 = cons_f ((fsg f1) `union_sg` (fsg f2)) ((esR f1) `union` (esR f2)) ((srcR f1) `union` (srcR f2)) ((tgtR f1) `union` (tgtR f2)) 

-- distributed union of fragments 
union_fs fs = foldr (\f ufs->f `union_f` ufs) empty_f fs

-- Checks whether fragments are disjoint
disj_fs fs = disjoint (map fLNs fs) && disjoint (map fEs fs) 

-- Gets the repeated nodes of fragments
rep_ns_of_fs::(Eq a, Eq b)=>[Fr a b]->[a]
rep_ns_of_fs fs = dups . gapp $ (map fLNs) fs

-- Gets the repeated edges of fragments
rep_es_of_fs::(Eq a, Eq b)=>[Fr a b]->[b]
rep_es_of_fs fs = dups . gapp $ (map fEs) fs
-- ++ (dups . gapp $ map fEs fs)

-- Resolution function, which restricts range of references function to the local nodes (those can that can be resolved locally)
res::(Eq a, Eq b)=>Fr a b->[(a, a)]
res f = rres (refs f) (fLNs f)

-- Yields resolved SG (◉ operator, subsumption)
reso_sg::(Eq a, Eq b)=>Fr a b->SGr a b
reso_sg f = subsume_sg (fsg f) (res f)

-- Gives reference edges of the resolved fragment, which removes those reference edges that are resolved
rEsR::(Eq a, Eq b)=>Fr a b->[b]
rEsR f = dom_of (rsub (srcR f) $ dom_of (res f))

-- Gives resolved fragment (◉ operator)
reso_f::(Eq a, Eq b)=>Fr a b->Fr a b
reso_f f = cons_f (reso_sg f) es' (dres (srcR f) es') (dres (tgtR f) es')
    where es' = rEsR f

-- Base well-formedness predicate
is_wfz_f f = is_wf Nothing (fsg f) && disjoint [(fLEs f), esR f] 
    && fun_bij (srcR f) (esR f) (nsP .fsg $ f) && fun_total' (tgtR f) (esR f) 
    && disjoint [ran_of . tgtR $ f, nsO . fsg $ f]

-- Base well-formedness with acyclicity
is_wfa_f f = is_wfz_f f && acyclicG (refsG f)

-- Partial well-formedness of fragments (last predicate could be proved and hence removed)
is_wf_f f = is_wfa_f f && is_wf (Just Partial) (reso_sg f)

-- Says whether flow of references goes from one fragment into another
refs_in f1 f2 = ran_of (tgtR f1) `subseteq` fLNs f2

-- Says whether flow of references is uni-directional (from one fragment into another, but not the reverse)
oneway f1 f2 = f1 `refs_in` f2 && (not $ f2 `refs_in` f1)

-- checks whether references are local
refsLocal f = fRNs f `subseteq` fLNs f
is_wf_tf f = is_wfa_f f && refsLocal f && is_wf (Just Total) (reso_sg f)

errors_frz::(Eq a, Eq b, Show a, Show b)=>String->Fr a b -> [ErrorTree]
errors_frz nm f =
    let err1 = check_wf ("SG (" ++ nm ++ ")") (Just Partial) (fsg f) in
    let err2 = if disjoint [(fLEs f), esR f] then nile else cons_se "Sets of SG edges and reference edges are not disjoint" in 
    let err3 = if fun_bij (srcR f) (esR f) (nsP .fsg $ f) then nile 
        else cons_et "Function 'srcR' is not bijective " [check_fun_bij (srcR f) (esR f) (nsP .fsg $ f)] in
    let err4 = if fun_total' (tgtR f) (esR f) then nile else cons_et "Function 'tgtR' is not total" [check_fun_total' (tgtR f) (esR f)] in
    [err1, err2, err3, err4]

errors_fra::(Eq a, Eq b, Show a, Show b)=>String->Fr a b -> [ErrorTree]
errors_fra nm f = 
    let errs1 = errors_frz nm f in
    let err2 = if acyclicG (refsG f) then nile else cons_se "The fragment's references contains cycles" in
    errs1 ++ [err2]

errors_fr::(Eq a, Eq b, Show a, Show b)=>String->Fr a b -> [ErrorTree]
errors_fr nm f = 
    let errs1 = errors_fra nm f in
    let err2 = check_wf ("Resolved SG (" ++ nm ++ ")") (Just Partial) (reso_sg f) in
    errs1 ++ [err2]

check_wf_f nm f = check_wf_of f nm is_wf_f (errors_fr nm)

errors_tfr::(Eq a, Eq b, Show a, Show b)=>String->Fr a b -> [ErrorTree]
errors_tfr nm f = 
    let errs1 = errors_fra nm f in
    let err2 = if refsLocal f then nile else cons_se $ "Not all references are local: " ++ (showElems' (diff (fRNs f) (fLNs f))) in
    let err3 = check_wf ("Resolved SG (" ++ nm ++ ")") (Just Total) (reso_sg f) in
    errs1 ++ [err2, err3]

check_wf_tf nm f = check_wf_of f nm is_wf_tf (errors_tfr nm)

is_wf_f' Nothing = is_wfz_f
is_wf_f' (Just Total) = is_wf_tf
is_wf_f' _ = is_wf_f

check_wf_f' id (Just Total) = check_wf_tf id
check_wf_f' id _            = check_wf_f id  

instance G_WF_CHK Fr where
   is_wf = is_wf_f'
   check_wf = check_wf_f'

-- morphism resolution operation
mres m (fs, ft) = 
    let mv = (inv $ (cl_override $ res fs) `mktotal_in` (fLNs fs)) `rcomp` ((fV m) `rcomp` ((cl_override $ res ft) `mktotal_in` (fLNs ft))) in
    cons_gm mv (fE m)

-- Checks that a morphism between fragments is well-formed 
is_wf_fgm (fs, m, ft) = fun_total (fV m) (fLNs fs) (fLNs ft) && fun_total (fE m) (fEsC fs) (fEsC ft)
    && is_wf_gm (Just WeakM) (reso_sg fs, mres m (fs, ft), reso_sg ft)

errors_wf_fgm (fs, m, ft) = 
    let err1 = if fun_total (fV m) (fLNs fs) (fLNs ft) then nile 
        else cons_et "Function 'fV' is not total" [check_fun_total (fV m) (fLNs fs) (fLNs ft)] in
    let err2 = if fun_total (fE m) (fEsC fs) (fEsC ft) then nile 
        else cons_et "Function 'fE' is not total" [check_fun_total (fE m) (fEsC fs) (fEsC ft)] in
    let err3 = check_wf_gm "Resolved Morphism between SGs of resolved fragments" (Just WeakM) (reso_sg fs, mres m (fs, ft), reso_sg ft) in
    [err1, err2, err3]

check_wf_fgm nm (fs, m, ft) = check_wf_of (fs, m, ft) nm (is_wf_fgm) (errors_wf_fgm)

-- notion of partial fragment refinement
frefines (fc, m) fa = is_wf_fgm (fc, m, fa) && sg_refinesz (reso_sg fc, mres m (fc, fa)) (reso_sg fa)

errors_frefines nm (fc, m) fa =
    let err1 = check_wf_fgm nm (fc, m, fa) in
    let errs2 = errs_sg_refinesz (reso_sg fc, mres m (fc, fa)) (reso_sg fa) in
    (err1:errs2)

check_frefines nm (fc, m, fa) = check_wf_of (fc, m, fa) nm (appl frefines) (appl $ errors_frefines nm)
    where appl f = (\(fc, m, fa)->f (fc, m) fa)

-- notion of total fragment refinement
tfrefines (fc, m) fa = is_wf_fgm (fc, m, fa) && tsg_refinesz (reso_sg fc, mres m (fc, fa)) (reso_sg fa)

errors_tfrefines nm (fc, m) fa =
    let err1 = check_wf_fgm nm (fc, m, fa) in
    let errs2 = errs_tsg_refinesz (reso_sg fc, mres m (fc, fa)) (reso_sg fa) in
    (err1:errs2)

check_tfrefines nm (fc, m, fa) = check_wf_of (fc, m, fa) nm (appl tfrefines) (appl $ errors_tfrefines nm)
    where appl f = (\(fc, m, fa)->f (fc, m) fa)

is_wf_fgm' Nothing         = is_wf_fgm  
is_wf_fgm' (Just WeakM)    = is_wf_fgm 
is_wf_fgm' (Just PartialM) = (\(fc, m, fa)-> frefines (fc, m) fa)
is_wf_fgm' (Just TotalM)   = (\(fc, m, fa)-> tfrefines (fc, m) fa)

check_wf_fgm' id Nothing         = check_wf_fgm id
check_wf_fgm' id (Just WeakM)    = check_wf_fgm id
check_wf_fgm' id (Just PartialM) = check_frefines id
check_wf_fgm' id (Just TotalM)   = check_tfrefines id

instance GM_CHK Fr Fr where
   is_wf_gm = is_wf_fgm'
   check_wf_gm = check_wf_fgm'

ty_compliesf::(Eq a, Eq b)=>GrwT a b->Fr a b->Bool
ty_compliesf gwt f = is_wf_gm' (Just PartialM) (gwt,  reso_sg f)

check_ty_compliesf::(Eq a, Eq b, Show a, Show b)=>String->GrwT a b->Fr a b->ErrorTree
check_ty_compliesf id gwt f = check_wf_gm' id (Just PartialM) (gwt,  reso_sg f)

is_wf_ty::(Eq a, Eq b)=>(Maybe MK)->(GrwT a b, Fr a b)->Bool
is_wf_ty Nothing (gwt, f)         = is_wf_gm' Nothing (gwt, reso_sg f)
is_wf_ty (Just WeakM) (gwt, f)    = is_wf_gm' (Just WeakM) (gwt,  reso_sg f) 
is_wf_ty (Just PartialM) (gwt, f) = gwt `ty_compliesf` f
is_wf_ty (Just TotalM) (gwt, f)   = gwt  `ty_compliesf` f

check_wf_ty id Nothing (gwt, f) = check_wf_gm' id Nothing (gwt,  reso_sg f)
check_wf_ty id (Just WeakM) (gwt, f) = check_wf_gm' id  (Just WeakM) (gwt,  reso_sg f)
check_wf_ty id (Just PartialM) (gwt, f) = check_ty_compliesf id gwt f
check_wf_ty id (Just TotalM) (gwt, f) = check_ty_compliesf id gwt f

instance GM_CHK' GrwT Fr where
   is_wf_gm' = is_wf_ty
   check_wf_gm' = check_wf_ty

