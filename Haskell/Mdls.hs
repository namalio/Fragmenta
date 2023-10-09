-------------------------
-- Project: PCs/Fragmenta
-- Module: 'Mdls'
-- Description: Fragmenta's models (Mdls)
-- Author: Nuno Amálio
---------------------------
module Mdls (Mdl, consMdl, mgfg, mfd, mufs, from, reso_m)
where

import Gr_Cls
import Grs 
import SGrs 
import GFGrs 
import Frs 
import GrswT ( GrwT )
import GrswET ( GrwET )
import Relations
import Sets 
import ErrorAnalysis 
import Utils
import ShowUtils

data Mdl a b = Mdl {
    gfg_ :: GFGr a b,
    fd_ :: Rel a (Fr a b)
} deriving (Eq, Show)

mgfg :: Mdl a b -> GFGr a b
mgfg Mdl {gfg_ = gfg, fd_ = _} = gfg

mfd :: Mdl a b -> Rel a (Fr a b)
mfd Mdl {gfg_ = _, fd_ = fd} = fd

consMdl :: GFGr a b -> Rel a (Fr a b) -> Mdl a b
consMdl gfg fd = Mdl {gfg_ = gfg, fd_ = fd} 

mufs::(Eq a, Eq b)=>Mdl a b->Fr a b
mufs = unionFs . ran_of . mfd

from' :: (Eq a, Eq b) => a -> Rel a (Fr a b) -> a
from' n (Set (gf, f) mf) 
   | n `elem` (ns . fsg $ f) = gf
   | otherwise = from' n mf

from::(Eq a, Eq b)=>Mdl a b->a->a
from m n = from' n (mfd m)

is_ref_ok m p = (from m p, from m (appl (refs (mufs m)) p)) `elem` (refsOf . mgfg $ m)
complyGFG m = all (\p->is_ref_ok m p) (nsP . fsg . mufs $ m)

errs_complyGFG m = if complyGFG m then nile else consSET ("The following proxies are not complying with the referencing of the model's GFG: " ++ (showElems' ps))
    where ps = filterS (not . is_ref_ok m)(nsP . fsg . mufs $ m)

okayMdl :: (Eq a, Eq b) => Mdl a b -> Bool
okayMdl m = okayG Nothing (mgfg m)  
   && tfun' (mfd m) (ns . mgfg $ m) && (disjFs . toList. ran_of . mfd $ m)
   && okayG (Just Total) (mufs m) && complyGFG m

rep_elems m = ran_of . mfd $ m

errsMdl ::(Eq a, Eq b, Show a, Show b)=>String->Mdl a b->[ErrorTree]
errsMdl id m = 
    let err1 = faultsG id (Nothing) (mgfg m) in
    let err2 = if tfun' (mfd m) (ns . mgfg $ m) then nile else consET "Not all GFG fragment nodes have a corresponding fragment." [reportFT' (mfd m) (ns . mgfg $ m)] in
    let err3 = if disjFs . toList . ran_of . mfd $ m then nile else consSET ("The fragments are not disjoint; the following nodes are repeated:" ++ (showElems' . toList . rep_ns_of_fs . ran_of . mfd $ m)) in
    let err4 = if disjFs . toList . ran_of . mfd $ m then nile else consSET ("The fragments are not disjoint; the following edges are repeated:" ++ (showElems' . toList . rep_es_of_fs . ran_of . mfd $ m)) in
    let err5 = faultsG id (Just Total) (mufs m) in
    let err6 = errs_complyGFG m in
    [err1, err2, err3, err4, err5,err6]

reportMdl::(Eq a, Eq b, Show a, Show b)=>String->Mdl a b->ErrorTree
reportMdl nm m = reportWF m nm okayMdl (errsMdl nm)

--is_wf_f' _ = is_wf_mdl

--check_wf_f' id _   = check_wf_mdl id  

instance G_WF_CHK Mdl where
   okayG _      = okayMdl
   faultsG id _ = reportMdl id  

reso_m::(Eq a, Eq b)=>Mdl a b->Fr a b
reso_m = reso_f . mufs

-- Checks that a morphism between models is well-formed 
okayMGM :: (Eq a, Eq b) => (Mdl a b, GrM a b, Mdl a b) -> Bool
okayMGM (mdls, m, mdlt) = okayGM Nothing (mufs mdls, m, mufs mdlt)

-- Checks that a source model accompanied by a set of morphisms is model-morphism compliant to another model
compliesFGM (mdls, ms) mdlt = okayMGM (mdls, unionGMs ms, mdlt)

errsMGM nm (mdls, m, mdlt) = 
    let err = faultsGM nm (Just WeakM) (mufs mdls, m, mufs mdlt) in
    [err]

reportMGM :: (Eq a, Eq b, Show a, Show b) =>String-> (Mdl a b, GrM a b, Mdl a b) -> ErrorTree
reportMGM nm (mdls, m, mdlt) = reportWF (mdls, m, mdlt) nm okayMGM (errsMGM nm)

-- Checks that one model refines another
mrefines (mdls, ms) mdlt = okayGM (Just TotalM) (mufs mdls, unionGMs ms, mufs mdlt) 

errs_mrefines nm (mdls, ms, mdlt) = 
    let err = faultsGM nm (Just TotalM) (mufs mdls, unionGMs ms, mufs mdlt)  in
    [err]

report_mrefines nm (mdls, ms, mdlt) = reportWF (mdls, ms, mdlt) nm (appl mrefines) (errs_mrefines nm)
    where appl f = (\(fc, m, fa)->f (fc, m) fa)

--is_wf_mgm' Nothing         = is_wf_mgm  
--is_wf_mgm' (Just WeakM)    = is_wf_mgm 
--is_wf_mgm' (Just PartialM) = (\(mdlc, m, mdla)-> (mdlc, [m]) `mrefines` mdla)
--is_wf_mgm' (Just TotalM)   = (\(mdlc, m, mdla)-> (mdlc, [m]) `mrefines` mdla)

--check_wf_mgm' id Nothing         = check_wf_mgm id
--check_wf_mgm' id (Just WeakM)    = check_wf_mgm id
--check_wf_mgm' id (Just PartialM) = (\(mdlc, m, mdla)-> check_mrefines id (mdlc, [m], mdla))
--check_wf_mgm' id (Just TotalM)   = (\(mdlc, m, mdla)-> check_mrefines id (mdlc, [m], mdla))

instance GM_CHK Mdl Mdl where
   okayGM :: (Eq a, Eq b) => Maybe MK -> (Mdl a b, GrM a b, Mdl a b) -> Bool
   okayGM Nothing      = okayMGM
   okayGM (Just WeakM) = okayMGM
   okayGM (Just PartialM) = \(mdlc, m, mdla)-> (mdlc, [m]) `mrefines` mdla
   okayGM (Just TotalM)   = \(mdlc, m, mdla)-> (mdlc, [m]) `mrefines` mdla
   faultsGM :: (Eq a, Eq b, Show a, Show b) =>String -> Maybe MK -> (Mdl a b, GrM a b, Mdl a b) -> ErrorTree
   faultsGM id Nothing         = reportMGM id
   faultsGM id (Just WeakM)    = reportMGM id
   faultsGM id (Just PartialM) = \(mc, m, ma)-> report_mrefines id (mc, [m], ma)
   faultsGM id (Just TotalM) = \(mc, m, ma)-> report_mrefines id (mc, [m], ma)

ty_compliesm::(Eq a, Eq b)=>GrwT a b->Mdl a b->Bool
ty_compliesm gwt mdl = okayGM' (Just PartialM) (gwt, mufs mdl) 

report_compliesm::(Eq a, Eq b, Show a, Show b)=>String->GrwT a b->Mdl a b->ErrorTree
report_compliesm id gwt mdl = faultsGM' id (Just PartialM) (gwt,  mufs mdl)

--is_wf_ty Nothing (gwt, mdl)         = okayGM Nothing (gwt, mufs mdl)
--is_wf_ty (Just WeakM) (gwt, mdl)    = okayGM (Just WeakM) (gwt,  mufs mdl) 
--is_wf_ty (Just PartialM) (gwt, mdl) = gwt `ty_compliesm` mdl
--is_wf_ty (Just TotalM) (gwt, mdl)   = gwt  `ty_compliesm` mdl

--check_wf_ty id Nothing (gwt, mdl)         = check_wf_gm' id Nothing (gwt,  mufs mdl)
--check_wf_ty id (Just WeakM) (gwt, mdl)    = check_wf_gm' id  (Just WeakM) (gwt,  mufs mdl)
--check_wf_ty id (Just PartialM) (gwt, mdl) = check_ty_compliesm id gwt mdl
--check_wf_ty id (Just TotalM) (gwt, mdl)   = check_ty_compliesm id gwt mdl

instance GM_CHK' GrwT Mdl where
   okayGM' Nothing (gwt, mdl)              = okayGM' Nothing (gwt, mufs mdl)
   okayGM' (Just WeakM) (gwt, mdl)         = okayGM' (Just WeakM) (gwt, mufs mdl) 
   okayGM' (Just PartialM) (gwt, mdl)      = gwt `ty_compliesm` mdl
   okayGM' (Just TotalM) (gwt, mdl)        = gwt  `ty_compliesm` mdl
   faultsGM' id Nothing (gwt, mdl)         = faultsGM' id Nothing (gwt, mufs mdl)
   faultsGM' id (Just WeakM) (gwt, mdl)    = faultsGM' id (Just WeakM) (gwt, mufs mdl)
   faultsGM' id (Just PartialM) (gwt, mdl) = report_compliesm id gwt mdl
   faultsGM' id (Just TotalM) (gwt, mdl)   = report_compliesm id gwt mdl

okayETCMdls::(Eq a, Eq b) =>Mdl a b->Mdl a b->Bool
okayETCMdls mdls mdlt = okETC (mufs mdls) (mufs mdlt)

rOkayETCMdls::(Eq a, Eq b, Show a, Show b)=>String->Mdl a b->Mdl a b->ErrorTree
rOkayETCMdls id mdls mdlt = 
    let err = if okETC (mufs mdls) (mufs mdlt) then nile else consET (id ++ " is invalid") [faultsETC id (mufs mdls) (mufs mdlt)] in
    err

etCompliesMdl::(Eq a, Eq b) =>(GrwET a b, Mdl a b)->(GrwT a b, Mdl a b)->Bool
etCompliesMdl (gwet, mdls) (gwt, mdlt) = okayETGM (gwet, mufs mdls) (gwt, mufs mdlt)

rEtCompliesMdl::(Eq a, Eq b, Show a, Show b)=>String->(GrwET a b, Mdl a b)->(GrwT a b, Mdl a b)->ErrorTree
rEtCompliesMdl id (gwet, mdls) (gwt, mdlt) = 
   let err = faultsETGM id (gwet, mufs mdls) (gwt, mufs mdlt) in
   if etCompliesMdl (gwet, mdls) (gwt, mdlt)  then nile else consET ("Errors in model extra typing compliance with " ++ id) [err]

instance ET_GM_CHK GrwET GrwT Mdl where
    okayETGM  = etCompliesMdl 
    faultsETGM = rEtCompliesMdl

instance GET Mdl where
    etc = fet . mufs

instance Ok_ETC_CHK Mdl where
    okETC = okayETCMdls
    faultsETC = rOkayETCMdls