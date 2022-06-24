---------------------
-- Project: Fragmenta
-- Module: 'ASDParsing'
-- Description: Parses SysML architecture structure diagrams (a subset of SysML block diagrams) textual descriptions to produce 
--  a graph with typing
-- Author: Nuno Amálio
--------------------
module IntoSysML.ASDParsing where

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
import ParseUtils
import IntoSysML.ASD_MM_Names
import SimpleFuns
import CommonParsing
--import Statecharts.StCsCommon


-- Names are represented as strings
type Name = String

-- Expressions are represented as strings
type Exp = String

-- Primitive types
data PType = PReal | PString | PBool | PNat | PInt | PInterval Int Int
  deriving(Eq, Show, Read) 

-- A mulplicity value is either a natural number or many ('*') 
data MultVal = MultN Int | MMany
   deriving(Eq, Show) 

data Mult =  MultS MultVal | MultR Int MultVal
   deriving(Eq, Show) 

data MultCompSrc = Optional | Compulsory
   deriving(Eq, Show, Read) 

-- Properties, a name, a type id, and an optional initialisation expression
data Property = Property Name Name Exp
   deriving(Eq, Show) 

-- Variable kinds: either plain variables or parameters
data VariableKind = Var | Parameter
   deriving(Eq, Show, Read) 

-- A variable has a kind and an embedded property (a name, a type id, and an optiona initialisation)
data Variable = Variable VariableKind Name Name Exp
   deriving(Eq, Show) 

-- A flowport has a kind, an embedded property and a lists of dependencies (names of other ports)
data FlowPort = InFlowPort Property | OutFlowPort Property [Name]
   deriving(Eq, Show) 

-- Components are either cyber, subsystem or physical
data ComponentKind = Cyber | Subsystem | Physical 
   deriving(Eq, Show, Read) 

-- The phenomena of a compound component can either be discrete or continuous
data PhenomenaKind = Discrete | Continuous
   deriving(Eq, Show, Read) 

--
-- A block component comprises a kind, a list of flow ports and a list of variables
data BComponent = BComponent ComponentKind [FlowPort] [Variable] 
   deriving(Eq, Show) 

-- A Block is either a system, a compound, or a block element
data Block = BSystem Name [FlowPort] 
   | BCompound Name PhenomenaKind BComponent
   | BElement Name BComponent
   deriving(Eq, Show) 

-- A value type definition is either an enumeration, a structural type, a derived type or a unit type
data VTypeDef = VTypeEnum Name [Name] | VTypeStrt Name [Property] | DType Name PType | UType Name PType Name
   deriving(Eq, Show) 

-- A composition has a source and target block and a source and a target multiplicity
--data Composition = Composition Block Block Mult Mult

 -- An ASD element is either a value type definition, a block definition or a composition
data ASDElem = ElemVT VTypeDef 
   | ElemB Block 
   | ElemC Name Name MultCompSrc Mult -- A composition has a source and target block (two names) and a source and a target multiplicity
   deriving(Eq, Show)

-- An ASD comprises a name followed by a number of elements
data ASD = ASD Name [ASDElem]
   deriving(Eq, Show)

-- Functions to retrieve components of a property
gPNm (Property nm _ _) = nm

-- Functions to retrieve components of a composition
gSrc (ElemC s _ _ _) = s
gTgt (ElemC _ t _ _) = t
gSrcM (ElemC _ _ sm _) = sm
gTgtM (ElemC _ _ _ tm) = tm

gVTNm (VTypeEnum nm _) = nm
gVTNm (VTypeStrt nm _) = nm
gVTNm (DType nm _)     = nm
gVTNm (UType nm _ _)   = nm

-- gBlockNm: gets name of a block
gBlockNm (BSystem nm _) = nm
gBlockNm (BCompound nm _ _) = nm
gBlockNm (BElement nm _) = nm

-- gElemNm: gets name of an ASD element
gElemNm (ElemVT vt) = gVTNm vt
gElemNm (ElemB b) = gBlockNm b
gElemNm (ElemC nm1 nm2 _ _ ) = "C" ++ nm1 ++ "_" ++ nm2

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
   ls<-parse_ls_ids "\n" ","
   skipSpaces
   return (VTypeEnum nm ls)

parse_init_exp :: ReadP String
parse_init_exp = do
   char '\"'
   iexp<-parse_until_chs "\"" -- Parses until terminators
   skipSpaces
   return (iexp)

parse_prop_info :: ReadP (Name, Name, Exp)
parse_prop_info = do
  nm<-parse_id 
  skipSpaces
  vty<-parse_id
  skipSpaces
  iexp<-parse_init_exp <++ return ""
  return (nm, vty, iexp)

parse_property :: ReadP Property
parse_property = do
  string "property"
  skipSpaces
  (nm, vty, iexp) <-parse_prop_info
  skipSpaces
  return (Property nm vty iexp)

parse_var :: ReadP Variable
parse_var = do
  skipSpaces
  (nm, vty, iexp) <-parse_prop_info
  skipSpaces
  vk<-string "Var" <|> string "Parameter" 
  skipSpaces
  return (Variable (read vk) nm vty iexp)

parse_vstrt :: ReadP VTypeDef
parse_vstrt = do
  string "strt"
  skipSpaces
  nm<-parse_id 
  skipSpaces
  char '{'
  skipSpaces
  ps<-manyTill parse_property (char '}')
  skipSpaces
  return (VTypeStrt nm ps)

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
   return (PNat)

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

parse_ptype :: ReadP PType
parse_ptype = do
  pt <- parse_pinterval   <|> parse_pint <|> parse_pnat <|> parse_preal <|> parse_pbool <|> parse_pstring 
  return pt

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

parse_vtype :: ReadP ASDElem
parse_vtype = do
  vt <-parse_vstrt <|> parse_dtype <|> parse_utype <|> parse_venum
  return (ElemVT vt)

parse_inner_prop_info :: ReadP Property
parse_inner_prop_info = do
   (nm, vty, iexp) <-parse_prop_info
   return (Property nm vty iexp)

parse_infport :: ReadP FlowPort
parse_infport = do
  string "in"
  skipSpaces
  p<-parse_inner_prop_info
  skipSpaces
  return (InFlowPort p)


parse_outfport :: ReadP FlowPort
parse_outfport = do
  string "out"
  skipSpaces
  p<-parse_inner_prop_info
  skipSpaces
  char '{'
  skipSpaces
  ds<-parse_ls_ids "}" ","
  skipSpaces
  return (OutFlowPort p ds)

parse_fport :: ReadP FlowPort
parse_fport = do
  fp<- parse_infport <|> parse_outfport
  return fp

parse_fports :: ReadP [FlowPort]
parse_fports = do
   string "ports"
   skipSpaces
   char '{'
   skipSpaces
   fps<-manyTill parse_fport (char '}')
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
   fps<-parse_fports <++ return []
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
  fps<-parse_fports <++ return []
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
   return (ElemC b1 b2 srcM tgtM)

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

labelOfRoot = "StructureDiagram_"



-- builds id of entity being named along with required edges 
mk_nm_info_q snm nm = ((nm, show_asd_mm_n ASD_MM_Name), ("ENmOf"++snm, show_asd_mm_e ASD_MM_ENamed_name), 
                       ("ENmOf"++snm, snm), ("ENmOf"++snm, nm))

-- Root quadruple of GwT to be constructed
gwt_rootQ nm  = 
   let ns_m = [(labelOfRoot, show_asd_mm_n ASD_MM_StructureDiagram)] in 
   (mk_nm_info_q labelOfRoot nm) `combineQwInsert` (ns_m, [], [], [])

-- Gets the node and edge type for an element
--gNETyForElem (ElemVT _) = (ASD_MM_ValueType, ASD_MM_EHasVTypes)
--gNETyForElem (ElemB _) = (ASD_MM_Block, ASD_MM_EHasBlocks)
--gNETyForElem (ElemC _ _ _ _) = (ASD_MM_Composition, ASD_MM_EHasCompositions)

-- Identifier of a value type node in a graph
vtyId nm = nm  ++ "_VT"
blockId nm = nm ++ "_Block"
elemId e@(ElemVT _) = vtyId (gElemNm e) 
elemId e@(ElemB _) = blockId $ gElemNm e
elemId e@(ElemC _ _ _ _) = (gElemNm e) ++ "_Composition"

-- builds name of an edge from a node
mkenm_frn n = "E"++n

ptId (PInterval n1 n2) = "PInterval" ++ "_" ++ (show n1) ++ "_" ++ (show n2) ++ "_PTy"
ptId pt = (show pt) ++ "_PTy"

-- Identifier of a property node in a graph
propId nm = nm++ "_Prop"

-- Identifier of an expression node in a graph
expId e = e++ ":Exp"

-- Identifier of an enumeration literal in a graph
literalId enm vnm = enm ++ "_" ++ vnm ++ "_L"

gwt_ns_es_ptype pt@(PInterval n1 n2) = 
   let pt_nm = ptId pt in
   let ns_m = [(pt_nm, 
              show_asd_mm_n ASD_MM_PInterval), (show PInt, show_asd_mm_n ASD_MM_PInt)] in
   let es_m = ([(mkenm_frn $ pt_nm ++ "_lb", show_asd_mm_e ASD_MM_EPInterval_lb), 
               (mkenm_frn $ pt_nm ++ "_ub", show_asd_mm_e ASD_MM_EPInterval_ub)],
               [(mkenm_frn $ pt_nm ++ "_lb", pt_nm), (mkenm_frn $ pt_nm ++ "_ub", pt_nm)],
               [(mkenm_frn $ pt_nm ++ "_lb", ptId PInt), (mkenm_frn $ pt_nm ++ "_ub", ptId PInt)] in
   makeQFrTFst ns_m es_m

gwt_ns_es_ptype pt =  
  let pt_nm = ptId pt in
  let ns_m = [(pt_nm, read_asd_mm pt_nm)] in
  (ns_m, [], [], [])

--
-- Builds what is required for a propery, either a variable, a field or a flow port
gwt_property (Property nm nty ie) n_mm_ty = 
   let nnm = propId nm in
   let enm_i = mkenm_frn $ nnm ++ "_init" in
   let enm_t = mkenm_frn $ nnm ++ "_type" in
   let ns_m = [(nnm, show_asd_mm_n n_mm_ty), (expId ie, show_asd_mm_n ASD_MM_Exp)] in
   let es_m = ([(enm_i, show_asd_mm_e ASD_MM_EProperty_init), (enm_t, ASD_MM_EProperty_type)],
                [(enm_i, gnm), (enm_t, gnm)], 
                [(enm_i, expId ie), (enm_t, vtyId nty)]) in
   let names_q = (mk_nm_info_q nnm nm) `combineQwInsert` nilQl in
   names_q `combineQwUnion` (makeQFrTFst ns_m_i es_m_i)


gwt_InnerElem (ElemVT (DType nm pt)) = 
  let gnm = vtyId nm in
  let q0 = ns_es_ptype pt in
  let ns_m = [(gnm, show_asd_mm_n ASD_MM_DType)]  in 
  let es_m = ([(mkenm_frn $ gnm ++ "_base", show_asd_mm_e ASD_MM_EDType_base)],
              [(mkenm_frn $ gnm ++ "_base", gnm)],
              [(mkenm_frn $ gnm ++ "_base", ptId pt)]) in
  makeQFrTFst ns_m es_m `combineQwUnion` q0

gwt_InnerElem (ElemVT (UType nm pt unm)) = 
  let gnm = vtyId nm in
  let q0 = ns_es_ptype pt in
  let ns_m = [(gnm, show_asd_mm_n ASD_MM_UnitType)]  in 
  let es_m = ([(mkenm_frn $ gnm ++ "_base", show_asd_mm_e ASD_MM_EDType_base),
              (mkenm_frn $ gnm ++ "_unit", show_asd_mm_e ASD_MM_EUnitType_unit)],
              [(mkenm_frn $ gnm ++ "_base", gnm), (mkenm_frn $ gnm ++ "_unit", gnm)],
              [(mkenm_frn $ gnm ++ "_base", ptId pt), (mkenm_frn $ gnm ++ "_unit", unm)]) in
  makeQFrTFst ns_m es_m `combineQwUnion` q0

gwt_InnerElem (ElemVT (VTypeStrt nm ps)) = 
  let nnm = vtyId nm in
  -- build graph portion for properties
  let qps = foldr (\p q->(gwt_property p) `combineQwUnion` q) nilQl ps in
  let enm_f k = mkenm_frn $ nnm ++ "_fields" ++ (show k) in
  let ns_m = [(nnm, show_asd_mm_n ASD_MM_StrtType)] in
  let es_m = (foldr (\p t->((enm_f (length . fst_T $ t), show_asd_mm_e ASD_MM_EStrtType_fields), 
                            (enm_f (length . fst_T $ t), nnm), (enm_f (length . fst_T $ t), gPNm p)) 
                             `combineTwInsert` t) ([], [], []) ps) in
  (mk_nm_info_q nnm nm) `combineQwInsert` (makeQFrTFst ns_m es_m `combineQwUnion` qps)

gwt_InnerElem (ElemVT (VTypeEnum nm ls)) = 
   let nnm = vtyId nm in
   let qls = foldr (\l ->([(mk_nm_info_q (literalId nm l) l) 
                   `combineQwInsert` ((makeQFrTFst (literalId nm l, show_asd_mm_n ASD_MM_Literal)] ([], [], [])) 
                   `combineQwUnion`  q))) [] ls in
   let enm_l k = mkenm_frn $ nnm ++ "_literals" ++ (show k) in
   let ns_m = [(nnm, show_asd_mm_n ASD_MM_Enumeration)] in
   let es_m = (foldr (\l t->((enm_l (length . fst_T $ t), show_asd_mm_e ASD_MM_EHasLiterals), 
                            (enm_l (length . fst_T $ t), nnm), (enm_l (length . fst_T $ t), literalId nm l)) 
                             `combineTwInsert` t) ([], [], []) ls) in
   (makeQFrTFst ns_m es_m) `combineQwUnion` qls


gwt_InnerElem e@(ElemC nms nmt ms mt) =
  let nnm = elemId e in 
  let ns_m = [(nnm, show_asd_mm_n ASD_MM_Composition), (ms, lower_fst $ show ms), (ms, lower_fst $ show mt)] in 
  let enm_s = mkenm_frn $ nnms ++ "_src" in
  let enm_t = mkenm_frn $ nnmt ++ "_tgt" in
  let enm_sm = mkenm_frn $ nnms ++ "_srcM" in
  let enm_tm = mkenm_frn $ nnmt ++ "_tgtM" in
  let es_m = ([(enm_s, show_asd_mm_e ASD_MM_EComposition_src), (enm_t, show_asd_mm_e ASD_MM_EComposition_tgt),
               (enm_sm, show_asd_mm_e ASD_MM_EComposition_srcM), (enm_tm, show_asd_mm_e ASD_MM_EComposition_tgtM)],
              [(enm_s, nnms), (enm_t, nnmt), (enm_sm, nnms), (enm_tm, nnmt)], 
              [(enm_s, blockId nms), (enm_t, blockId nmt), (enm_sm, ms), (enm_sm, mt)]) in
  (makeQFrTFst ns_m es_m) `combineQwUnion` nilQl
  

consGwT_elem rnm elem = 
   let enm = elemId elem in
   let (nty, ety) = gNETyForElem elem in
   let ns_m_i = [(enm, show_asd_mm_n nty)] in 
   let es_m_i = ([(mkenm_frn $ rnm ++ "_" ++ enm, show_asd_mm_e ety)], 
                 [(mkenm_frn $ rnm ++ "_" ++ enm, rnm)], 
                 [(mkenm_frn $ rnm ++ "_" ++ enm, enm)]) in
   let names_q = (mk_nm_info_q enm (gElemNm elem)) `combineQwInsert` nilQl in
   names_q `combineQwUnion` (makeQFrTFst ns_m_i es_m_i) `combineQwUnion` (consGwT_InnerElem elem)

consGwT_elems es  = foldr(\e q->(consGwT_elem labelOfRoot e) `combineQwAppend` q) nilQl es

-- Constructs the graph with typing for given ASD model
consGwT (ASD nm es)  = 
   -- initial set of nodes with type mapping
   let (ns_m, es_m, src_m, tgt_m) = (consGwT_InitQ nm) `combineQwAppend` (consGwT_elems es) in
   let asd_g = cons_g (map fst ns_m) (map fst es_m) src_m tgt_m in
   cons_gwt asd_g (cons_gm (ns_m) (es_m))

loadASD fn = do
   oasd <- loadASDFrFile fn
   if (isNil oasd) 
      then do
         putStrLn "The ASD definition could not be parsed."
         return empty_gwt
      else do
         let asd_g = consGwT $ the oasd
         return asd_g


def_path = "IntoSysML/Examples/"

test1 = readP_to_S parse_mults "5"
test2 = readP_to_S parse_mults "*"
test3 = readP_to_S parse_ptype "Int"
test4 = readP_to_S parse_ptype "Interval 5 6"
test5 = readP_to_S parse_venum "enum OpenClosed : open, closed;"
test6a = readP_to_S parse_prop_info "v1 OpenClosed \"closed\""
test6b = readP_to_S parse_fport "out v1 OpenClosed \"closed\" {}"
test6c = readP_to_S parse_fport "in v2 OpenClosed"
test7 = do
   asd<-loadASDFrFile (def_path ++ "three_water_tanks.asd")
   putStrLn $ show asd
test8 = do
  asd_g<-loadASD $ def_path ++ "three_water_tanks.asd"
  putStrLn $ show asd_g
