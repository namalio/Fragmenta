--------------------------
-- Project: Fragmenta
-- Module: 'StCs'
-- Description: Handler module of StCs
-- Author: Nuno Amálio
--------------------------
module Statecharts.StCs(StC
   , load_stcs_mmi
   , gStCName
   , gDescInfo
   , gTransitionInfo
   , gDescs
   , gMainDescs
   , nmOfNamed
   , nmOfNamed'
   , isMutableStatewInner
   , gCMMStTy
   , gInnerStart)
where

import Gr_Cls
import Grs
import Sets ( intersec, intoSet, Set )
import SGrs
import GrswT (GrwT)
import Mdls 
import LoadCheckDraw
import Frs
import Statecharts.StCs_MM_Names
import SimpleFuns
import Relations (appl, dom_of, img, rcomp, applM)
import TheNil
import Sets ( intersec )
import MyMaybe
import MMI ( consMMI, MMI )

type StC a b = GrwT a b

load_stcs_amm :: String -> IO (String, Mdl String String)
load_stcs_amm def_path = loadMdl def_path "StCs_AMM"

load_stcs_cmm :: String -> IO (String, Mdl String String)
load_stcs_cmm def_path = loadMdl def_path "StCs_MM"

load_stcs_rm :: String -> IO (GrM String String)
load_stcs_rm def_path = load_rm_cmdl_def def_path "StCs_MM"

nmOfNamed :: (GR gm, GRM gm) => gm String String -> String -> String
nmOfNamed stc = appl (consRelOfEdge stc CMM_ENamed_name)
nmOfNamed' :: (GR gm, GRM gm) => gm String String -> String -> String
nmOfNamed' stc n = 
   if n `elem` (dom_of $ consRelOfEdge stc CMM_ENamed_name) then nmOfNamed stc n else n
   --allButLast $ appl (tgt stc) (the $ img (inv . src $ stc) [n] `intersec` (es_of_ety stc $ show_cmm_e CMM_ENamed_name))

load_stcs_mmi :: String -> IO (MMI String String)
load_stcs_mmi def_path = do
  (_, amm)<-load_stcs_amm def_path
  (_, cmm)<-load_stcs_cmm def_path
  rm<-load_stcs_rm def_path
  return (consMMI cmm amm rm (fsg . reso_m $ cmm))

-- Gives the relation of an edge in a statechart
consRelOfEdge stc e = foldr (\e r->(appl (src stc) e, appl (tgt stc) e) `intoSet` r) nil (es_of_ety stc $ show_cmm_e e)

-- Gets name of given statechart 
gStCName :: (GR gm, GRM gm) => gm String String -> String
gStCName stc = appl (consRelOfEdge stc CMM_ENamed_name) "StCModel_"


-- gDescStart stc dnm = the $ img (consRelOfEdge stc CMM_EStarts) [dnm]

-- gDescEnd stc dnm = toMaybeFrLs $ img (consRelOfEdge stc CMM_EEnds) [dnm]

stc_ns_of_nty sg_mm stc nt = ns_of_ntys stc sg_mm [show_cmm_n nt]

-- Gets descriptions of a 'StCDef'
gDescs stc id = img (consRelOfEdge stc CMM_EHasDesc) [id]

gMainDescs stc = gDescs stc "StCModel_"

isMutableStatewInner sg_mm stc s = s `elem` (stc_ns_of_nty sg_mm stc CMM_MutableState) && (isSomething $ gDescs stc s)

gCMMStTy sg_mm stc s 
   | s `elem` stc_ns_of_nty sg_mm stc CMM_StartState = CMM_StartState
   | s `elem` stc_ns_of_nty sg_mm stc CMM_EndState = CMM_EndState
   | s `elem` stc_ns_of_nty sg_mm stc CMM_HistoryState = CMM_HistoryState
   | s `elem` stc_ns_of_nty sg_mm stc CMM_MutableState = CMM_MutableState

gInnerStart sg_mm stc s = 
   let r = (consRelOfEdge stc CMM_EHasDesc) `rcomp` (consRelOfEdge stc CMM_EContains) in
   the $ (img r [s]) `intersec` (stc_ns_of_nty sg_mm stc CMM_StartState)

-- Gets information about some description of given statechart 
gDescInfo :: (GR gm, GRM gm) =>SGr String String-> gm String String -> String -> (Set String, Set String)
gDescInfo sg_mm stc desc_nm = 
   let elems = img (consRelOfEdge stc CMM_EContains) [desc_nm] in
   let elems_st = elems `intersec` (stc_ns_of_nty sg_mm stc CMM_State) in
   let elems_t = elems `intersec` (stc_ns_of_nty sg_mm stc CMM_Transition) in
   (elems_st, elems_t)

gTransitionInfo stc t = 
    let s = appl (consRelOfEdge stc CMM_ETransition_src) t in
    let t' = appl (consRelOfEdge stc CMM_ETransition_tgt) t in
    let e = applM ((consRelOfEdge stc CMM_ETransition_event) `rcomp` (consRelOfEdge stc CMM_EWExp_exp)) t in
    let g = applM ((consRelOfEdge stc CMM_ETransition_guard) `rcomp` (consRelOfEdge stc CMM_EWExp_exp)) t in
    let a = applM ((consRelOfEdge stc CMM_ETransition_action) `rcomp` (consRelOfEdge stc CMM_EWExp_exp)) t in 
    (s, t', e, g, a)

