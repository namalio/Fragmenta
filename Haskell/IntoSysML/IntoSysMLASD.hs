--------------------------
-- Project: Fragmenta
-- Module: 'IntoSysML'
-- Description: Handler module of Into SysML ASDs
-- Author: Nuno Amálio
--------------------------
module IntoSysML.IntoSysMLASD(
  ASD
  , load_asd_mmi
  , gName
  , gASDName
  , gASDBlocks
  , gASDVTypes
  , gASDComps
  , gBlocPs
  , gCVars
  , gCKind
  , gCPKind
  , gTypedNameTy
  , gInitialisableExp
  , gVKind
  , gOFPDeps
  , gEnumLs
  , gDTypePTy
  , gUTypeUnit
  , gStrtTypeFields
  , gCompSrc
  , gCompTgt
  , gCompSrcM
  , gCompTgtM
  , gMultSMVal
  , gMultRLb
  , gMultRUb
  , gMultValNumN
  , gInterfaceOps
  , gOpParams
  , gOpReturn)
where

import Gr_Cls
import SGrs
import GrswT
import Mdls 
import LoadCheckDraw
import Frs
import IntoSysML.ASD_MM_Names
import SimpleFuns
import Relations
import TheNil
import Sets
import MyMaybe
import MMI

type ASD a = GrwT a

load_asd_amm :: String -> IO (String, Mdl String String)
load_asd_amm def_path = loadMdl def_path "IntoSysML_AAD_MM"

load_asd_cmm :: String -> IO (String, Mdl String String)
load_asd_cmm def_path = loadMdl def_path "IntoSysML_ASD_MM"

load_asd_rm :: String -> IO (GrM String String)
load_asd_rm def_path = load_rm_cmdl_def def_path "IntoSysML_ASD_MM"

--nmOfNamed stc n = appl (consRelOfEdge stc CMM_ENamed_name) n
--nmOfNamed' stc n = if n `elem` (dom_of $ consRelOfEdge stc CMM_ENamed_name) then nmOfNamed stc n else n
  --allButLast $ appl (tgt stc) (the $ img (inv . src $ stc) [n] `intersec` (es_of_ety stc $ show_cmm_e CMM_ENamed_name))

load_asd_mmi :: String -> IO (MMI String String)
load_asd_mmi def_path = do
  (_, amm)<-load_asd_amm def_path
  (_, cmm)<-load_asd_cmm def_path
  rm<-load_asd_rm def_path
  return $ consMMI cmm amm rm (fsg . reso_m $ cmm)

-- Gives the relation of an edge in a ASD
consRelOfEdge::(GR g, GRM g)=>g String String->IntoSysML_ASD_MM_Es->Rel String String
consRelOfEdge asd e = foldr (\e r->(appl (src asd) e, appl (tgt asd) e) `intoSet` r) nil (es_of_ety asd . show_asd_mm_e $ e)

-- Gets name of some named node
gName::(GR g, GRM g)=>g String String->String->String
gName asd = appl (consRelOfEdge asd ASD_MM_Ename)

-- Gets name of given ASD
gRoot::(GWT g, GR g)=>g String String->String
gRoot asd = appl (inv . fV . ty $ asd) (show_asd_mm_n ASD_MM_StructureDiagram)

gASDName :: (GR g, GRM g, GWT g) => g String String -> String
gASDName asd = gName asd . gRoot $ asd


-- gDescStart stc dnm = the $ img (consRelOfEdge stc CMM_EStarts) [dnm]

-- gDescEnd stc dnm = toMaybeFrLs $ img (consRelOfEdge stc CMM_EEnds) [dnm]

asd_ns_of_nty::(GRM gm) =>SGr String String->gm String String->IntoSysML_ASD_MM_Ns->Set String
asd_ns_of_nty sg_mm asd nt = ns_of_ntys asd sg_mm [show_asd_mm_n nt]

-- Gets descriptions of a 'StCDef'
--gDescs stc id = img (consRelOfEdge stc CMM_EHasDesc) [id]

-- Gets blocks
gASDBlocks :: (GR g, GRM g, GWT g) => g String String -> Set String
gASDBlocks asd = img (consRelOfEdge asd ASD_MM_EHasBlocks) [gRoot asd]

-- Gets value types
gASDVTypes :: (GR g, GRM g, GWT g) => g String String -> Set String
gASDVTypes asd = img (consRelOfEdge asd ASD_MM_EHasVTypes) [gRoot asd]

-- Gets compositions
gASDComps :: (GR g, GRM g, GWT g) => g String String -> Set String
gASDComps asd = img (consRelOfEdge asd ASD_MM_EHasCompositions) [gRoot asd]

-- Gets ports of a block
gBlocPs :: (GR g, GRM g) => g String String -> String -> Set String
gBlocPs asd bl = img (consRelOfEdge asd ASD_MM_EBlock_ports) [bl]

-- Gets variables  of a component
gCVars :: (GR g, GRM g) => g String String -> String -> Set String
gCVars asd c = img (consRelOfEdge asd ASD_MM_EComponent_vars) [c]

-- Gets a component's kind
gCKind :: (GR g, GRM g) => g String String -> String -> String
gCKind asd c = appl (consRelOfEdge asd ASD_MM_EComponent_kind) c

-- Gets a compound's phenomena kind
gCPKind :: (GR g, GRM g) => g String String -> String -> String
gCPKind asd c = appl (consRelOfEdge asd ASD_MM_ECompound_phenomena) c

-- Gets type of a typed name
gTypedNameTy :: (GR g, GRM g) => g String String -> String -> String
gTypedNameTy asd tn = appl (consRelOfEdge asd ASD_MM_ETypedName_type) tn

-- Gets ITN's initialisation
gInitialisableExp asd itn = applM (consRelOfEdge asd ASD_MM_EInitialisable_init) itn

-- Gets variable's kind
gVKind :: (GR g, GRM g) => g String String -> String -> String
gVKind asd v = appl (consRelOfEdge asd ASD_MM_EVariable_kind) v

-- Gets dependencies of an outflow port
gOFPDeps :: (GR g, GRM g) => g String String -> String -> Set String
gOFPDeps asd fp = img (consRelOfEdge asd ASD_MM_EOutFlowPort_depends) [fp]

-- Gets literals of an enumeration
gEnumLs :: (GR g, GRM g) => g String String -> String -> Set String
gEnumLs asd e = img (consRelOfEdge asd ASD_MM_EHasLiterals) [e]

-- Gets primitive type of a derived type (DTYpe)
gDTypePTy :: (GR g, GRM g) => g String String -> String -> String
gDTypePTy asd dt = appl (consRelOfEdge asd ASD_MM_EDType_base) dt

-- Gets unit of a union type (UType)
gUTypeUnit :: (GR g, GRM g) => g String String -> String -> String
gUTypeUnit asd ut = appl (consRelOfEdge asd ASD_MM_EUnitType_unit) ut

-- Gets fields of a structural type
gStrtTypeFields asd st = img (consRelOfEdge asd ASD_MM_EStrtType_fields) [st]

-- Gets operations of an interface
gInterfaceOps asd i = img (consRelOfEdge asd ASD_MM_EInterface_ops) [i]

-- Gets the parameter of an operation
gOpParams asd op = img (consRelOfEdge asd ASD_MM_EOperation_params) [op]

gOpReturn asd op = appl (consRelOfEdge asd ASD_MM_EOperation_return) op

-- Gets source of a composition
gCompSrc :: (GR g, GRM g) => g String String -> String -> String
gCompSrc asd c = appl (consRelOfEdge asd ASD_MM_EComposition_src) c

-- Gets target of a composition
gCompTgt :: (GR g, GRM g) => g String String -> String -> String
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

