--------------------------
-- Project: Fragmenta
-- Module: 'IntoSysML'
-- Description: Handler module of Into SysML
-- Author: Nuno Amálio
--------------------------
module IntoSysML.IntoSysML(ASD, load_asd_mmi, gName, gASDName, gASDBlocks, gASDVTypes, gASDComps, gBlocPs, 
   gCVars, gCKind, gCPKind, gTypedNameTy, gInitialisableExp, gVKind, gOFPDeps, gEnumLs, gDTypePTy, gUTypeUnit, gStrtTypeFields, 
   gCompSrc, gCompTgt, gCompSrcM, gCompTgtM, gMultSMVal, gMultRLb, gMultRUb, gMultValNumN, gInterfaceOps, gOpParams, gOpReturn)
where

import Gr_Cls
import Grs
import SGrs
import GrswT
import Mdls 
import LoadCheckDraw
import Frs
import IntoSysML.ASD_MM_Names
import SimpleFuns
import Relations
import The_Nil
import Sets
import MyMaybe
import MMI

type ASD a = GrwT a

load_asd_amm def_path = do
  mdl<-load_mdl_def def_path "IntoSysML_AAD_MM"
  return mdl

load_asd_cmm def_path = do
  mdl <- load_mdl_def def_path "IntoSysML_ASD_MM"
  return mdl

load_asd_rm def_path = do
    rm<-load_rm_cmdl_def def_path "IntoSysML_ASD_MM"
    return rm

--nmOfNamed stc n = appl (consRelOfEdge stc CMM_ENamed_name) n
--nmOfNamed' stc n = if n `elem` (dom_of $ consRelOfEdge stc CMM_ENamed_name) then nmOfNamed stc n else n
  --allButLast $ appl (tgt stc) (the $ img (inv . src $ stc) [n] `intersec` (es_of_ety stc $ show_cmm_e CMM_ENamed_name))

load_asd_mmi def_path = do
  amm<-load_asd_amm def_path
  cmm<-load_asd_cmm def_path
  rm<-load_asd_rm def_path
  return (cons_mm_info cmm amm rm (fsg . reso_m $ cmm))

-- Gives the relation of an edge in a ASD
consRelOfEdge asd e = foldr (\e r->(appl (src asd) e, appl (tgt asd) e):r) [] (es_of_ety asd . show_asd_mm_e $ e)

-- Gets name of some named node
gName asd n = appl (consRelOfEdge asd ASD_MM_ENamed_name) n

-- Gets name of given ASD
gRoot asd = appl (inv . fV . ty $ asd) "StructureDiagram"
gASDName asd = (gName asd) . gRoot $ asd

-- Gets name of given statechart 
--gStCName stc = appl (consRelOfEdge stc CMM_ENamed_name) "StCModel_"


-- gDescStart stc dnm = the $ img (consRelOfEdge stc CMM_EStarts) [dnm]

-- gDescEnd stc dnm = toMaybeFrLs $ img (consRelOfEdge stc CMM_EEnds) [dnm]

asd_ns_of_nty sg_mm asd nt = ns_of_ntys asd sg_mm [show_asd_mm_n nt]

-- Gets descriptions of a 'StCDef'
--gDescs stc id = img (consRelOfEdge stc CMM_EHasDesc) [id]

-- Gets blocks
gASDBlocks asd = img (consRelOfEdge asd ASD_MM_EHasBlocks) [gRoot asd]

-- Gets value types
gASDVTypes asd = img (consRelOfEdge asd ASD_MM_EHasVTypes) [gRoot asd]

-- Gets compositions
gASDComps asd = img (consRelOfEdge asd ASD_MM_EHasCompositions) [gRoot asd]

-- Gets ports of a block
gBlocPs asd bl = img (consRelOfEdge asd ASD_MM_EBlock_ports) [bl]

-- Gets variables  of a component
gCVars asd c = img (consRelOfEdge asd ASD_MM_EComponent_vars) [c]

-- Gets a component's kind
gCKind asd c = appl (consRelOfEdge asd ASD_MM_EComponent_kind) c

-- Gets a compound's phenomena kind
gCPKind asd c = appl (consRelOfEdge asd ASD_MM_ECompound_phenomena) c

-- Gets type of a typed name
gTypedNameTy asd tn = appl (consRelOfEdge asd ASD_MM_ETypedName_type) tn

-- Gets ITN's initialisation
gInitialisableExp asd itn = applM (consRelOfEdge asd ASD_MM_EInitialisable_init) itn

-- Gets variable's kind
gVKind asd v = appl (consRelOfEdge asd ASD_MM_EVariable_kind) v

-- Gets dependencies of an outflow port
gOFPDeps asd fp = img (consRelOfEdge asd ASD_MM_EOutFlowPort_depends) [fp]

-- Gets literals of an enumeration
gEnumLs asd e = img (consRelOfEdge asd ASD_MM_EHasLiterals) [e]

-- Gets primitive type of a derived type (DTYpe)
gDTypePTy asd dt = appl (consRelOfEdge asd ASD_MM_EDType_base) dt

-- Gets unit of a union type (UType)
gUTypeUnit asd ut = appl (consRelOfEdge asd ASD_MM_EUnitType_unit) ut

-- Gets fields of a structural type
gStrtTypeFields asd st = img (consRelOfEdge asd ASD_MM_EStrtType_fields) [st]

-- Gets operations of an interface
gInterfaceOps asd i = img (consRelOfEdge asd ASD_MM_EInterface_ops) [i]

-- Gets the parameter of an operation
gOpParams asd op = img (consRelOfEdge asd ASD_MM_EOperation_params) [op]

gOpReturn asd op = appl (consRelOfEdge asd ASD_MM_EOperation_return) op

-- Gets source of a composition
gCompSrc asd c = appl (consRelOfEdge asd ASD_MM_EComposition_src) c

-- Gets target of a composition
gCompTgt asd c = appl (consRelOfEdge asd ASD_MM_EComposition_tgt) c

-- Gets source multiplicity
gCompSrcM asd c = appl (consRelOfEdge asd ASD_MM_EComposition_srcM) c

-- Gets target multiplicity
gCompTgtM asd c = appl (consRelOfEdge asd ASD_MM_EComposition_tgtM) c

-- Gets the multiplicity value of a single multiplicity
gMultSMVal asd m = appl (consRelOfEdge asd ASD_MM_EMultSingle_val) m

-- Gets the lower bound of a range multiplicity
gMultRLb asd mr = appl (consRelOfEdge asd ASD_MM_EMultRange_lb) mr

-- Gets the upper bound of a range multiplicity
gMultRUb asd mr = appl (consRelOfEdge asd ASD_MM_EMultRange_ub) mr

-- Gets the number of a multiplicity value number
gMultValNumN asd mv = appl (consRelOfEdge asd ASD_MM_EMultValNum_n) mv

--isMutableStatewInner sg_mm stc s = s `elem` (stc_ns_of_nty sg_mm stc CMM_MutableState) && (isSomething $ gDescs stc s)

--gCMMStTy sg_mm stc s 
--   | s `elem` stc_ns_of_nty sg_mm stc CMM_StartState = CMM_StartState
--   | s `elem` stc_ns_of_nty sg_mm stc CMM_EndState = CMM_EndState
--   | s `elem` stc_ns_of_nty sg_mm stc CMM_HistoryState = CMM_HistoryState
--   | s `elem` stc_ns_of_nty sg_mm stc CMM_MutableState = CMM_MutableState

--gInnerStart sg_mm stc s = 
--   let r = (consRelOfEdge stc CMM_EHasDesc) `rcomp` (consRelOfEdge stc CMM_EContains) in
--   the $ (img r [s]) `intersec` (stc_ns_of_nty sg_mm stc CMM_StartState)

-- Gets information about some description of given statechart 
--gDescInfo sg_mm stc desc_nm = 
--   let elems = img (consRelOfEdge stc CMM_EContains) [desc_nm] in
--   let elems_st = elems `intersec` (stc_ns_of_nty sg_mm stc CMM_State) in
--   let elems_t = elems `intersec` (stc_ns_of_nty sg_mm stc CMM_Transition) in
--   (elems_st, elems_t)

--gTransitionInfo stc t = 
--    let s = appl (consRelOfEdge stc CMM_ETransition_src) t in
--    let t' = appl (consRelOfEdge stc CMM_ETransition_tgt) t in
--    let e = applM ((consRelOfEdge stc CMM_ETransition_event) `rcomp` (consRelOfEdge stc CMM_EWExp_exp)) t in
--    let g = applM ((consRelOfEdge stc CMM_ETransition_guard) `rcomp` (consRelOfEdge stc CMM_EWExp_exp)) t in
--    let a = applM ((consRelOfEdge stc CMM_ETransition_action) `rcomp` (consRelOfEdge stc CMM_EWExp_exp)) t in 
--    (s, t', e, g, a)

