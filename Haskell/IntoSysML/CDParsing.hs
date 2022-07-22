---------------------------------------
-- Project: Fragmenta
-- Module: 'CDParsing'
-- Description: Parses SysML configuration diagrams (a subset of SysML internal block diagrams) textual descriptions to produce 
--  a graph with typing
-- Author: Nuno Amálio
---------------------------------------
module IntoSysML.CDParsing(loadCD) where

import Text.ParserCombinators.ReadP
import Control.Applicative
import Control.Monad(when)
import Grs
import SGrs
import Sets
import Relations
import The_Nil
import MyMaybe
import GrswT
import IntoSysML.ASD_MM_Names
import SimpleFuns
import CommonParsing
import ParseUtils
import IntoSysML.ASDCommon


--
-- A block component comprises a kind, a list of flow ports and a list of variables
data BComponent = BComponent ComponentKind [Port] [Variable] 
   deriving(Eq, Show) 

-- A Block is either a system, a compound, or a block element
data Block = BSystem Name [Port] 
   | BCompound Name PhenomenaKind BComponent
   | BElement Name BComponent
   deriving(Eq, Show) 

-- A composition has a source and target block and a source and a target multiplicity
--

data BlockI = 
  
 -- A CD element is either a block instance, a composition instance, or a connector
data ASDElem = ElemB BlockI 
   | ElemCr Connector
   | ElemCn Composition -- A composition has a source and target block (two names) and a source and a target multiplicity
   deriving(Eq, Show)

-- A CD comprises a name followed by a number of elements
data CD = CD Name [CDElem]
   deriving(Eq, Show)

-- Gets ports of a component
gCFps (BComponent _ ps _) = ps

-- Gets variables of a component
gCVs (BComponent _ _ vs) = vs

-- Gets component kind
gCK (BComponent ck _ _) = ck

gVTNm (VTypeEnum nm _) = nm
gVTNm (VTypeStrt nm _) = nm
gVTNm (DType nm _)     = nm
gVTNm (UType nm _ _)   = nm

-- gBlockNm: gets name of a block
gBlockNm (BSystem nm _) = nm
gBlockNm (BCompound nm _ _) = nm
gBlockNm (BElement nm _) = nm

-- gBlockMTy: gets meta-type of a block
gBlockMTy (BSystem _ _) = ASD_MM_System
gBlockMTy (BCompound nm _ _) = ASD_MM_Compound
gBlockMTy (BElement nm _) = ASD_MM_BElement

-- gElemNm: gets name of an ASD element
gElemNm (ElemVT vt) = gVTNm vt
gElemNm (ElemB b) = gBlockNm b
gElemNm (ElemC c) = "C" ++ (gSrc c) ++ "_" ++ (gTgt c)

-- getStates desc = foldr (\e es-> if isState e then (getSt e):es else es) [] (gElems desc)
-- getTransitions desc = foldr (\e es-> if isTransition e then (getT e):es else es) [] (gElems desc)
-- getTheCs elems = foldl (\es e-> if not . isNode $ e then (getC e):es else es) [] elems

parse_ASD :: ReadP ASD
parse_ASD = do
   string "ASD"
   skipSpaces
   nm<-parse_id 
   skipSpaces
   char ':'
   skipSpaces
   es<- manyTill (parse_asd_elem) eof
   skipSpaces
   return (ASD nm es)

parse_venum :: ReadP VTypeDef
parse_venum = do
   string "enum"
   skipSpaces
   nm<-parse_id 
   skipSpaces
   char ':'
   skipSpaces
   ls<-manyTill parse_spc_id (char '\n') 
   skipSpaces
   return (VTypeEnum nm ls)

parse_init_exp :: ReadP String
parse_init_exp = do
   char '\"'
   iexp<-parse_until_chs "\"" -- Parses until terminators
   skipSpaces
   return (iexp)

parse_ptype :: ReadP PType
parse_ptype = do
  pt <- parse_pinterval  <|> parse_pint <|> parse_pnat <|> parse_preal <|> parse_pbool <|> parse_pstring 
  return pt

parse_atype_pty :: ReadP AType
parse_atype_pty= do
   pt <- parse_ptype 
   return (ATypeP pt)

parse_atype_tyid :: ReadP AType
parse_atype_tyid = do
   ty_id <- parse_id
   return (ATypeId ty_id)

parse_atype::ReadP AType
parse_atype = do
   aty<-parse_atype_pty <|> parse_atype_tyid
   return aty

parse_TN_pair :: ReadP (Name, AType)
parse_TN_pair = do
  nm<-parse_id 
  skipSpaces
  vty<-parse_atype
  skipSpaces
  return (nm, vty)

parse_TN_triple :: ReadP (Name, AType, Exp)
parse_TN_triple = do
  (nm, vty)<-parse_TN_pair 
  skipSpaces
  iexp<-parse_init_exp <++ return ""
  skipSpaces
  return (nm, vty, iexp)

parse_TN :: ReadP TypedName
parse_TN = do
  string "typed"
  skipSpaces
  (nm, vty)<-parse_TN_pair
  skipSpaces
  return (TypedName nm vty)

parse_ITN :: ReadP Initialisable
parse_ITN = do
  (nm, vty, iexp) <-parse_TN_triple
  skipSpaces
  return (Initialisable nm vty iexp)

parse_var :: ReadP Variable
parse_var = do
  skipSpaces
  itn <-parse_ITN
  skipSpaces
  vk<-string "Var" <|> string "Parameter" 
  skipSpaces
  return (Variable itn (read vk))

parse_vstrt :: ReadP VTypeDef
parse_vstrt = do
  string "strt"
  skipSpaces
  nm<-parse_id 
  skipSpaces
  char '{'
  skipSpaces
  ts<-manyTill parse_ITN (char '}')
  skipSpaces
  return (VTypeStrt nm $ foldl (\fs itn->(FieldI itn):fs) [] ts)

parse_pint :: ReadP PType
parse_pint = do
   string "Int"
   return (PInt)

parse_pnat :: ReadP PType
parse_pnat = do
   string "Nat"
   return (PNat)

parse_preal :: ReadP PType
parse_preal = do
   string "Real"
   return (PReal)

parse_pbool :: ReadP PType
parse_pbool = do
   string "Bool"
   return (PBool)

parse_pstring :: ReadP PType
parse_pstring = do
   string "String"
   return (PString)

parse_pinterval :: ReadP PType
parse_pinterval = do
  string "Interval" 
  skipSpaces
  n1<-parse_number
  skipSpaces
  n2<-parse_number
  skipSpaces
  return (PInterval (read n1) (read n2))

parse_dtype :: ReadP VTypeDef
parse_dtype = do
   string "dtype"
   skipSpaces
   nm<-parse_id 
   skipSpaces
   pt<-parse_ptype
   skipSpaces
   return (DType nm pt)

parse_utype :: ReadP VTypeDef
parse_utype = do
   string "utype"
   skipSpaces
   nm<-parse_id 
   skipSpaces
   pt<-parse_ptype
   skipSpaces
   idu<-parse_until_chs "\n"
   skipSpaces
   return (UType nm pt idu)

parse_operation :: ReadP Operation
parse_operation = do
   string "operation"
   skipSpaces
   nm<-parse_id 
   skipSpaces
   aty<-parse_atype
   skipSpaces
   char '{'
   skipSpaces
   ps<-manyTill parse_TN_pair (char '}') 
   skipSpaces
   return (Operation nm (foldl (\tns (nm, ty)->(TypedName nm ty):tns) [] ps) aty)

parse_interface :: ReadP VTypeDef
parse_interface = do
   string "interface"
   skipSpaces
   nm<-parse_id 
   skipSpaces
   char '{'
   skipSpaces
   os<-manyTill parse_operation (char '}')
   skipSpaces
   return (Interface nm os)

parse_vtype :: ReadP ASDElem
parse_vtype = do
  vt <-parse_vstrt <|> parse_dtype <|> parse_utype <|> parse_venum <|> parse_interface
  return (ElemVT vt)

parse_inner_prop_info :: ReadP Initialisable
parse_inner_prop_info = do
   (nm, vty, iexp) <-parse_TN_triple
   return (Initialisable nm vty iexp)

parse_infport :: ReadP Port
parse_infport = do
  string "in"
  skipSpaces
  p<-parse_inner_prop_info
  skipSpaces
  return (InFlowPort p)


parse_outfport :: ReadP Port
parse_outfport = do
  string "out"
  skipSpaces
  p<-parse_inner_prop_info
  skipSpaces
  char '{'
  skipSpaces
  ds<-manyTill parse_spc_id (char '}')
  skipSpaces
  return (OutFlowPort p ds)

parse_apiport_requires :: ReadP APIPortKind
parse_apiport_requires = do
  string "requires"
  return Requires

parse_apiport_provides :: ReadP APIPortKind
parse_apiport_provides = do
  string "provides"
  return Provides

parse_apiport :: ReadP Port
parse_apiport = do
  pk<-parse_apiport_requires <|> parse_apiport_provides
  skipSpaces
  p<-parse_inner_prop_info
  skipSpaces
  return (APIPort p pk)

parse_port :: ReadP Port
parse_port = do
  fp<- parse_infport <|> parse_outfport <|> parse_apiport
  return fp

parse_ports :: ReadP [Port]
parse_ports = do
   string "ports"
   skipSpaces
   char '{'
   skipSpaces
   fps<-manyTill parse_port (char '}')
   skipSpaces
   return fps

parse_vars :: ReadP [Variable]
parse_vars = do
   string "vars"
   skipSpaces
   char '{'
   skipSpaces
   vs<-manyTill parse_var (char '}')
   skipSpaces
   return vs

parse_bsys :: ReadP Block
parse_bsys = do
   string "system"
   skipSpaces
   nm<-parse_id 
   skipSpaces
   fps<-parse_ports <++ return []
   skipSpaces
   return (BSystem nm fps)

parse_bphenomena :: ReadP PhenomenaKind
parse_bphenomena = do
  p_str<- string "discrete" <|> string "continuous"
  return (read $ capitalise_fst p_str)

parse_bcomponent :: ReadP BComponent
parse_bcomponent = do
  sck<-string "cyber" <|> string "physical" <|> string "subsystem" 
  skipSpaces
  vs<-parse_vars  <++ return []
  skipSpaces
  fps<-parse_ports <++ return []
  skipSpaces
  return (BComponent (read $ capitalise_fst sck) fps vs)

parse_bcompound :: ReadP Block
parse_bcompound = do
   string "compound"
   skipSpaces
   nm<-parse_id 
   skipSpaces
   pk<-parse_bphenomena
   skipSpaces
   c<-parse_bcomponent
   skipSpaces
   return (BCompound nm pk c)

parse_belement :: ReadP Block
parse_belement = do
   string "element"
   skipSpaces
   nm<-parse_id 
   skipSpaces
   c<-parse_bcomponent
   skipSpaces
   return (BElement nm c)

parse_block :: ReadP Block
parse_block = do
   b<-parse_bcompound <|> parse_belement <|> parse_bsys
   return b

parse_eblock :: ReadP ASDElem
parse_eblock = do
   b<-parse_block
   return (ElemB b)

parse_mult_comp_src :: ReadP MultCompSrc
parse_mult_comp_src = do 
   ms<-string "optional" <|> string "compulsory"
   return (read $ capitalise_fst ms)

parse_mult_many::ReadP MultVal
parse_mult_many = do
   char '*'
   return (MMany)

parse_mult_n::ReadP MultVal
parse_mult_n = do
   n<-parse_number
   return (MultN $ read n)

parse_mult_val::ReadP MultVal
parse_mult_val = do
   m<-parse_mult_many <|> parse_mult_n
   return m

parse_mults::ReadP Mult
parse_mults = do
   m<-parse_mult_val
   skipSpaces
   return (MultS m)

parse_mult_range::ReadP Mult
parse_mult_range = do
   n<-parse_number
   skipSpaces
   string ".."
   skipSpaces
   m<-parse_mult_val
   skipSpaces
   return (MultR (read n) m)

parse_mult::ReadP Mult
parse_mult = do
   m<-parse_mult_range <|> parse_mults
   return m

parse_composition :: ReadP ASDElem
parse_composition = do
   string "composition"
   skipSpaces
   b1<-parse_id 
   skipSpaces
   b2<-parse_id 
   skipSpaces
   srcM<-parse_mult_comp_src 
   skipSpaces
   tgtM<-parse_mult
   skipSpaces
   return (ElemC (Composition b1 b2 srcM tgtM))

parse_asd_elem :: ReadP ASDElem
parse_asd_elem = do
   e<-parse_eblock <|> parse_vtype <|> parse_composition
   return e


loadASDFrFile :: FilePath -> IO (Maybe ASD)
loadASDFrFile fn = do   
    contents <- readFile fn
    --makes sure it is read
    let asd = parseMaybe parse_ASD contents
    return asd

rootId nm = nm ++ "_StructureDiagram"



-- builds id of entity being named along with required edges 
mk_nm_info_q snm nm = ((nm, show_asd_mm_n ASD_MM_Name), ("ENmOf"++snm, show_asd_mm_e ASD_MM_ENamed_name), 
                       ("ENmOf"++snm, snm), ("ENmOf"++snm, nm))

-- Root quadruple of GwT to be constructed
gwt_rootQ nm  = 
   let ns_m = [(rootId nm, show_asd_mm_n ASD_MM_StructureDiagram)] in 
   (mk_nm_info_q (rootId nm) nm) `combineQwInsert` (ns_m, [], [], [])

-- Gets the node and edge type for an element
--gNETyForElem (ElemVT _) = (ASD_MM_ValueType, ASD_MM_EHasVTypes)
--gNETyForElem (ElemB _) = (ASD_MM_Block, ASD_MM_EHasBlocks)
--gNETyForElem (ElemC _ _ _ _) = (ASD_MM_Composition, ASD_MM_EHasCompositions)

-- Identifier of a value type node in a graph
vtyId nm = nm  ++ "_VT"

-- Identifier of an element in a graph
elemId e@(ElemVT _) = vtyId . gElemNm $ e 
elemId e@(ElemB _) = blockId . gElemNm $ e
elemId e@(ElemC _) = (gElemNm e) ++ "_Composition"

-- builds name of an edge from a node
mkenm_frn n = "E"++n

ptId (PInterval n1 n2) = "PInterval" ++ "_" ++ (show n1) ++ "_" ++ (show n2) ++ "_PTy"
ptId pt = (show pt) ++ "_PTy"

atyId (ATypeP pt) = ptId pt
atyId (ATypeId id) = vtyId id

-- Identifiers in a graph
varId cnm nm = cnm ++ "_" ++ nm ++ "_Var"
tnId cnm nm = cnm ++ "_" ++ nm ++ "_TN"
vtnId cnm nm ASD_MM_Variable = varId cnm nm
vtnId cnm nm _ = tnId cnm nm

opId cnm nm = cnm ++ "_" ++ nm ++ "_Op"

-- Identifier of an expression node in a graph
expId e = e++ ":Exp"

-- Identifier of an enumeration literal in a graph
literalId enm vnm = enm ++ "_" ++ vnm ++ "_L"

gwt_ns_es_ptype pt@(PInterval n1 n2) = 
   let pt_nm = ptId pt in
   let ns_m = [(pt_nm, show_asd_mm_n ASD_MM_PInterval)] in
   let es_m = ([(mkenm_frn $ pt_nm ++ "_lb", show_asd_mm_e ASD_MM_EPInterval_lb), 
               (mkenm_frn $ pt_nm ++ "_ub", show_asd_mm_e ASD_MM_EPInterval_ub)],
               [(mkenm_frn $ pt_nm ++ "_lb", pt_nm), (mkenm_frn $ pt_nm ++ "_ub", pt_nm)],
               [(mkenm_frn $ pt_nm ++ "_lb", ptId PInt), (mkenm_frn $ pt_nm ++ "_ub", ptId PInt)]) in
   makeQFrTFst ns_m es_m `combineQwUnion` gwt_ns_es_ptype (PInt)

gwt_ns_es_ptype pt =  
  let pt_nm = ptId pt in
  let ns_m = [(pt_nm, show_asd_mm_n . read_asd_mm . show $ pt)] in
  (ns_m, [], [], [])

--
-- Builds what is required for a typed name (TN), either a variable, a field or a flow port
gwt_TN cnm (TypedName nm nty) n_mm_ty = 
   let nnm = vtnId cnm nm n_mm_ty in
   let enm_t = mkenm_frn $ nnm ++ "_type" in
   let nty_id = atyId nty in 
   let ns_m = [(nnm, show_asd_mm_n n_mm_ty)] in
   let es_m = ([(enm_t, show_asd_mm_e ASD_MM_ETypedName_type)], 
                [(enm_t, nnm)], [(enm_t, nty_id)]) in
   let q = if is_ATy_a_Pty nty then gwt_ns_es_ptype (gATyPTy nty) else nilQl in
   let names_q = (mk_nm_info_q nnm nm) `combineQwInsert` q in
   names_q `combineQwUnion` (makeQFrTFst ns_m es_m)

--
-- Builds what is required for an ITN, either a variable, a field or a flow port
gwt_ITN cnm (Initialisable nm nty ie) n_mm_ty = 
   let nnm = vtnId cnm nm n_mm_ty in
   let iq = gwt_TN cnm (TypedName nm nty) n_mm_ty in
   let enm_i = mkenm_frn $ nnm ++ "_init" in
   let nty_id = atyId nty in 
   let ns_m = if null ie then [] else [(expId ie, show_asd_mm_n ASD_MM_Exp)] in
   let es_m = (if null ie then [] else [(enm_i, show_asd_mm_e ASD_MM_EInitialisable_init)], 
                if null ie then [] else [(enm_i, nnm)], 
                if null ie then [] else [(enm_i, expId ie)]) in
   (makeQFrTFst ns_m es_m) `combineQwUnion` iq

gwt_Port cnm po@(InFlowPort itn) = gwt_ITN cnm itn (gPoMTy po)
gwt_Port cnm po@(OutFlowPort itn deps) = 
  let iqs = gwt_ITN cnm itn (gPoMTy po) in
  let enm d = mkenm_frn $ cnm ++ "_" ++ (gITNNm itn) ++ "_depends_" ++ d in
  let es_m = foldl (\t d->((enm d, show_asd_mm_e ASD_MM_EOutFlowPort_depends), 
                          (enm d, vtnId cnm (gITNNm itn) $ gPoMTy po), 
                          (enm d, tnId cnm d)) `combineTwInsert` t) ([], [], []) deps in
  (makeQFrTFst [] es_m) `combineQwUnion` iqs

gwt_Port cnm po@(APIPort itn k) = 
   let iq = gwt_ITN cnm itn (gPoMTy po) in
   let enm_k = mkenm_frn $ cnm ++ "_" ++ (gITNNm itn) ++ "_kind" in
   let ns_m = [(show k, show_asd_mm_n $ read_asd_mm . lower_fst . show $ k)] in
   let pid = (tnId cnm) . gITNNm $ itn in
   let es_m = ([(enm_k, show_asd_mm_e ASD_MM_EAPIPort_kind)], [(enm_k, pid)], [(enm_k, show k)]) in
   (makeQFrTFst ns_m es_m) `combineQwUnion` iq

-- Builds what is required for a field
gwt_field cnm tn  =
   let iq = gwt_TN cnm tn ASD_MM_Field in
   iq

-- Builds what is required for a variable
gwt_variable cnm (Variable itn vk)  =
  let iq =  gwt_ITN cnm itn ASD_MM_Variable in
  let ns_m = [(show vk, show_asd_mm_n $ read_asd_mm . lower_fst . show $ vk)] in
  let vid = (varId cnm) . gITNNm $ itn in
  let enm_k = mkenm_frn $ vid ++ "_kind" in
  let es_m = ([(enm_k, show_asd_mm_e ASD_MM_EVariable_kind)], [(enm_k, vid)], [(enm_k, show vk)]) in
  (makeQFrTFst ns_m es_m) `combineQwUnion` iq

-- Ports of a block 
gwt_Ports nm_bl ps = 
  let iqs = foldl (\qs p->(gwt_Port nm_bl p) `combineQwUnion` qs) nilQl ps in 
  let enm_l k = mkenm_frn $ nm_bl ++ "_ports" ++ (show k) in
  let es_m = foldl (\esml p->((enm_l ((length . fst_T $ esml) +1), show_asd_mm_e ASD_MM_EBlock_ports), 
                             (enm_l ((length . fst_T $ esml) + 1), nm_bl), 
                             (enm_l ((length . fst_T $ esml) +1), tnId nm_bl $ gPoNm p)) 
                             `combineTwInsert` esml) ([], [], []) ps in
  (makeQFrTFst [] es_m) `combineQwUnion` iqs

-- A block
gwt_Block nmb bl_mty fps = 
  let nnm = blockId nmb in
  let ns_m = [(nnm, show_asd_mm_n bl_mty)] in 
  let es_m = ([], [], []) in
  --let names_q = (mk_nm_info_q nnm nmb) `combineQwInsert` nilQl in
  (mk_nm_info_q nnm nmb) `combineQwInsert` ((makeQFrTFst ns_m es_m) `combineQwUnion` (gwt_Ports nnm fps))

-- A component
gwt_Component nm c bl_mty = 
   let iqs = gwt_Block nm bl_mty (gCFps c) in
   let iqs' = foldl (\qs v->(gwt_variable nm v) `combineQwUnion` qs) iqs $ gCVs c in
   let ns_m = [(show . gCK $ c, show_asd_mm_n $ read_asd_mm . lower_fst  . show . gCK $ c)] in
   let enm_k = mkenm_frn $ (blockId nm) ++ "_kind" in
   let enm_v v = mkenm_frn $ (blockId nm) ++ "_" ++ ((varId nm) . gITNNm . gVarITN $ v) in
   let es_m = ([(enm_k, show_asd_mm_e ASD_MM_EComponent_kind)] , [(enm_k, blockId nm)], [(enm_k, show . gCK $ c)]) in
   let es_m' = foldl (\vs v->((enm_v v, show_asd_mm_e ASD_MM_EComponent_vars), (enm_v v, blockId nm), 
                (enm_v v, (varId nm) . gITNNm . gVarITN $ v)) 
               `combineTwInsert` vs) es_m (gCVs c) in
  (makeQFrTFst ns_m es_m') `combineQwUnion` iqs'

mvalId (MultN n) = "MultN_" ++ (show n)
mvalId (MMany) = "Mult*" 
valId n = (show n) ++ "_Val"

gwt_mult_val mv@(MultN n) =
  let ns_m = [(mvalId mv, show_asd_mm_n ASD_MM_MultValNum), (valId n, show_asd_mm_n ASD_MM_Nat)] in
  let enm = mkenm_frn $ mvalId mv in
  let es_m = ([(enm, show_asd_mm_e ASD_MM_EMultValNum_n)], [(enm, mvalId mv)], [(enm, (show n) ++ "_Val")]) in
  makeQFrTFst ns_m es_m 

multId (MultS mv) = "MultS_" ++ mvalId mv
multId (MultR mvs mvt) = "MultR_" ++ (show mvs) ++ "_" ++  (mvalId mvt)

gwt_mult m@(MultS mv) = 
  let nnm = multId m in
  let ns_m = [(nnm, show_asd_mm_n ASD_MM_MultSingle)] in
  let enm = mkenm_frn $ nnm ++ "_val" in
  let es_m = ([(enm, show_asd_mm_e ASD_MM_EMultSingle_val)], [(enm, nnm)], [(enm, mvalId mv)]) in
  makeQFrTFst ns_m es_m `combineQwUnion` (gwt_mult_val mv)

gwt_mult m@(MultR mvs mvt) = 
  let nnm = multId m in
  let ns_m = [(nnm, show_asd_mm_n ASD_MM_MultRange), (valId mvs, show_asd_mm_n ASD_MM_Nat)] in
  let enm1 = mkenm_frn $ nnm ++ "_lb" in
  let enm2 = mkenm_frn $ nnm ++ "_ub" in
  let es_m = ([(enm1, show_asd_mm_e ASD_MM_EMultRange_lb), (enm2, show_asd_mm_e ASD_MM_EMultRange_ub)], 
              [(enm1, nnm), (enm2, nnm)], [(enm1, valId mvs), (enm2, mvalId mvt)]) in
  makeQFrTFst ns_m es_m `combineQwUnion` (gwt_mult_val mvt)


gwt_Has rnm tnm mty =
  let enm = mkenm_frn $ rnm ++ "_" ++ tnm in
  let ns_m = [] in
  let es_m = ([(enm, show_asd_mm_e mty)],
              [(enm, rnm)],
              [(enm, tnm)]) in
  (makeQFrTFst ns_m es_m) `combineQwUnion` nilQl

gwt_operation inm (Operation nm ps aty) = 
  let nnm = opId inm nm in
  let q = foldl (\ql f->(gwt_field inm f) `combineQwUnion` ql) nilQl ps in 
  let ns_m = [(nnm, show_asd_mm_n ASD_MM_Operation)] in
  let enm_ps k = mkenm_frn $ nnm ++ "_params_" ++ (show k) in
  let enm_ret = mkenm_frn $ nnm ++ "_return" in
  let tq = if is_ATy_a_Pty aty then gwt_ns_es_ptype (gATyPTy aty) else nilQl in
  let es_m_0 = foldl(\ts p->((enm_ps $ (length . fst_T $ ts) + 1, show_asd_mm_e ASD_MM_EOperation_params), 
               (enm_ps $ (length . fst_T $ ts) + 1, nnm), 
               (enm_ps $ (length . fst_T $ ts) + 1, tnId inm $ gTNNm p)) `combineTwInsert` ts) ([], [], []) ps in
  let es_m = ((enm_ret, show_asd_mm_e ASD_MM_EOperation_return), (enm_ret, nnm), (enm_ret, atyId aty)) `combineTwInsert` es_m_0 in
  (makeQFrTFst ns_m es_m) `combineQwUnion` ((mk_nm_info_q nnm nm) `combineQwInsert` q)


gwt_Elem rnm (ElemVT (DType nm pt)) = 
  let nnm = vtyId nm in
  let q0 = gwt_ns_es_ptype pt in
  let ns_m = [(nnm, show_asd_mm_n ASD_MM_DType)]  in 
  let es_m = ([(mkenm_frn $ nnm ++ "_base", show_asd_mm_e ASD_MM_EDType_base)],
              [(mkenm_frn $ nnm ++ "_base", nnm)],
              [(mkenm_frn $ nnm ++ "_base", ptId pt)]) in
  (mk_nm_info_q nnm nm) `combineQwInsert` (((makeQFrTFst ns_m es_m) `combineQwUnion` q0) `combineQwUnion` (gwt_Has rnm nnm ASD_MM_EHasVTypes))

gwt_Elem rnm (ElemVT (UType nm pt unm)) = 
  let nnm = vtyId nm in
  let q0 = gwt_ns_es_ptype pt in
  let ns_m = [(nnm, show_asd_mm_n ASD_MM_UnitType), (unm, show_asd_mm_n ASD_MM_Name)]  in 
  let es_m = ([(mkenm_frn $ nnm ++ "_base_", show_asd_mm_e ASD_MM_EDType_base),
              (mkenm_frn $ nnm ++ "_unit_", show_asd_mm_e ASD_MM_EUnitType_unit)],
              [(mkenm_frn $ nnm ++ "_base_", nnm), (mkenm_frn $ nnm ++ "_unit_", nnm)],
              [(mkenm_frn $ nnm ++ "_base_", ptId pt), (mkenm_frn $ nnm ++ "_unit_", unm)]) in
  (mk_nm_info_q nnm nm) `combineQwInsert` ((makeQFrTFst ns_m es_m `combineQwUnion` q0) `combineQwUnion` (gwt_Has rnm nnm ASD_MM_EHasVTypes))

gwt_Elem rnm (ElemVT (VTypeStrt nm ps)) = 
  let nnm = vtyId nm in
  -- build graph portion for properties
  let qps = foldl (\q (FieldI itn)->(gwt_ITN nm itn ASD_MM_FieldI) `combineQwUnion` q) nilQl ps in
  let enm_f k = mkenm_frn $ nnm ++ "_fields_" ++ (show k) in
  let ns_m = [(nnm, show_asd_mm_n ASD_MM_StrtType)] in
  let es_m = foldl (\t (FieldI itn)->((enm_f $ (length . fst_T $ t) + 1, show_asd_mm_e ASD_MM_EStrtType_fields), 
                            (enm_f $ (length . fst_T $ t) + 1, nnm), (enm_f $ (length . fst_T $ t) + 1, (tnId nm) . gITNNm $ itn)) 
                             `combineTwInsert` t) ([], [], []) ps in
  (mk_nm_info_q nnm nm) `combineQwInsert` (makeQFrTFst ns_m es_m `combineQwUnion` (qps `combineQwUnion` (gwt_Has rnm nnm ASD_MM_EHasVTypes)))

gwt_Elem rnm (ElemVT (VTypeEnum nm ls)) = 
   let nnm = vtyId nm in
   let qls = foldr (\l q->((mk_nm_info_q (literalId nm l) l) 
                   `combineQwInsert` ((makeQFrTFst [(literalId nm l, show_asd_mm_n ASD_MM_Literal)] ([], [], [])) 
                   `combineQwUnion`  q))) nilQl ls in
   let enm_l k = mkenm_frn $ nnm ++ "_literals" ++ (show k) in
   let ns_m = [(nnm, show_asd_mm_n ASD_MM_Enumeration)] in
   let es_m = foldr (\l t->((enm_l (length . fst_T $ t), show_asd_mm_e ASD_MM_EHasLiterals), 
                            (enm_l (length . fst_T $ t), nnm), (enm_l (length . fst_T $ t), literalId nm l)) 
                             `combineTwInsert` t) ([], [], []) ls in
   (mk_nm_info_q nnm nm) `combineQwInsert` ((makeQFrTFst ns_m es_m) `combineQwUnion` (qls `combineQwUnion` (gwt_Has rnm nnm ASD_MM_EHasVTypes)))

gwt_Elem rnm (ElemVT (Interface nm ops)) =
   let nnm = vtyId nm in
   let ns_m = [(nnm, show_asd_mm_n ASD_MM_Interface)] in
   let enm k =  mkenm_frn $ nnm ++ "_ops_" ++ (show k) in
   let iq = foldl (\qs op->(gwt_operation nm op) `combineQwUnion` qs) nilQl ops in
   let es_m = foldl (\lts op->((enm $ (length . fst_T $ lts) + 1, show_asd_mm_e ASD_MM_EInterface_ops), 
                     (enm $ (length . fst_T $ lts) + 1, nnm), (enm $ (length . fst_T $ lts) + 1, opId nm $ gOpNm op)) `combineTwInsert` lts) ([], [], []) ops in 
    (mk_nm_info_q nnm nm) `combineQwInsert` (((makeQFrTFst ns_m es_m) `combineQwUnion` iq) `combineQwUnion` (gwt_Has rnm nnm ASD_MM_EHasVTypes))

-- Compositions
gwt_Elem rnm e@(ElemC c) =
  let nnm = elemId e in 
  let ns_m = [(nnm, show_asd_mm_n ASD_MM_Composition), (show $ gSrcM c, show_asd_mm_n $ read_asd_mm . lower_fst . show . gSrcM $ c)] in 
  let enm_s = mkenm_frn $ (gSrc c) ++ "_" ++ (gTgt c) ++ "_src" in
  let enm_t = mkenm_frn $ (gSrc c) ++ "_" ++ (gTgt c) ++ "_tgt" in
  let enm_sm = mkenm_frn $ (gSrc c) ++ "_" ++ (gTgt c) ++ "_srcM" in
  let enm_tm = mkenm_frn $ (gSrc c) ++ "_" ++ (gTgt c) ++ "_tgtM" in
  let es_m = ([(enm_s, show_asd_mm_e ASD_MM_EComposition_src), (enm_t, show_asd_mm_e ASD_MM_EComposition_tgt),
               (enm_sm, show_asd_mm_e ASD_MM_EComposition_srcM), (enm_tm, show_asd_mm_e ASD_MM_EComposition_tgtM)],
              [(enm_s, nnm), (enm_t, nnm), (enm_sm, nnm), (enm_tm, nnm)], 
              [(enm_s, blockId . gSrc $ c), (enm_t, blockId . gTgt $ c), (enm_sm, show . gSrcM $ c), (enm_tm, multId . gTgtM $ c)]) in
  makeQFrTFst ns_m es_m `combineQwUnion` ((gwt_mult . gTgtM $ c) `combineQwUnion` (gwt_Has rnm nnm ASD_MM_EHasCompositions))

-- Blocks/Systems
gwt_Elem rnm (ElemB (BSystem nm fps)) = 
  (gwt_Block nm ASD_MM_System fps) `combineQwUnion` (gwt_Has rnm (blockId nm) ASD_MM_EHasBlocks)

-- Blocks/Elements
gwt_Elem rnm (ElemB (BElement nm c)) =
   let iqs = gwt_Component nm c ASD_MM_BElement in
   iqs `combineQwUnion` (gwt_Has rnm (blockId nm) ASD_MM_EHasBlocks)

-- Blocks/Elements
gwt_Elem rnm (ElemB (BCompound nm pk c)) =
  let iqs = gwt_Component nm c ASD_MM_Compound in
  let nnm = blockId nm in
  let ns_m = [(show pk, show_asd_mm_n . read_asd_mm . lower_fst  . show  $ pk)] in
  let enm_p = mkenm_frn $ nnm ++ "_phenomena" in
  let es_m = ([(enm_p, show_asd_mm_e ASD_MM_ECompound_phenomena)], [(enm_p, nnm)], [(enm_p, show pk)]) in
  (makeQFrTFst ns_m es_m) `combineQwUnion` (iqs `combineQwUnion` (gwt_Has rnm nnm ASD_MM_EHasBlocks))


-- consGwT_elem rnm elem = 
--   let enm = elemId elem in
--   let (nty, ety) = gNETyForElem elem in
--   let ns_m_i = [(enm, show_asd_mm_n nty)] in 
--   let es_m_i = ([(mkenm_frn $ rnm ++ "_" ++ enm, show_asd_mm_e ety)], 
--                 [(mkenm_frn $ rnm ++ "_" ++ enm, rnm)], 
--                 [(mkenm_frn $ rnm ++ "_" ++ enm, enm)]) in
--   let names_q = (mk_nm_info_q enm (gElemNm elem)) `combineQwInsert` nilQl in
--   names_q `combineQwUnion` (makeQFrTFst ns_m_i es_m_i) `combineQwUnion` (gwT_InnerElem elem)

gwt_elems rnm es = foldr(\e q->(gwt_Elem rnm e) `combineQwUnion` q) nilQl es

-- Constructs the graph with typing for given ASD model
gwt_asd (ASD nm es)  = 
   -- initial set of nodes with type mapping
   let (ns_m, es_m, src_m, tgt_m) = (gwt_rootQ nm) `combineQwUnion` (gwt_elems (rootId nm) es) in
   let asd_g = cons_g (map fst ns_m) (map fst es_m) src_m tgt_m in
   cons_gwt asd_g (cons_gm (ns_m) (es_m))

loadASD fn = do
   oasd <- loadASDFrFile fn
   if (isNil oasd) 
      then do
         putStrLn "The ASD definition could not be parsed."
         return empty_gwt
      else do
         let asd_g = gwt_asd $ the oasd
         return asd_g


def_path = "IntoSysML/Examples/"

test1 = readP_to_S parse_mults "5"
test2 = readP_to_S parse_mults "*"
test3 = readP_to_S parse_ptype "Int"
test4 = readP_to_S parse_ptype "Interval 5 6"
test5a = readP_to_S parse_venum "enum OpenClosed : open closed\n"
test5b = readP_to_S (manyTill parse_spc_id eof) "open closed"
test6a = readP_to_S parse_ITN  "v1 OpenClosed \"closed\""
test6b = readP_to_S parse_port "out v1 OpenClosed \"closed\" {}"
test6c = readP_to_S parse_port "in v2 OpenClosed"
test7 = do
   asd<-loadASDFrFile (def_path ++ "three_water_tanks.asd")
   putStrLn $ show asd
test8 = do
  asd_g<-loadASD $ def_path ++ "three_water_tanks.asd"
  putStrLn $ show asd_g
