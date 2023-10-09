---------------------
-- Project: Fragmenta
-- Module: 'ASDParsing'
-- Description: Parses SysML architecture structure diagrams (a subset of SysML block diagrams) textual descriptions to produce 
--  a graph with typing
-- Author: Nuno Amálio
--------------------
module IntoSysML.ParsingASD(loadASD) where

import Text.ParserCombinators.ReadP
import Control.Applicative ( Alternative((<|>)) )
import Control.Monad(when)
import Gr_Cls
import SGrs
import Sets
import Relations
import TheNil
import MyMaybe
import GrswT
import IntoSysML.ASD_MM_Names
import SimpleFuns
import ParsingCommon
import ParseUtils
import IntoSysML.ASDCommon
import QUR


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

 -- An ASD element is either a value type definition, a block definition or a composition
data ASDElem = ElemVT VTypeDef 
   | ElemB Block 
   | ElemC Composition -- A composition has a source and target block (two names) and a source and a target multiplicity
   deriving(Eq, Show)

-- An ASD comprises a name followed by a number of elements
data ASD = ASD Name [ASDElem]
   deriving(Eq, Show)

-- Gets ports of a component
gCFps :: BComponent -> [Port]
gCFps (BComponent _ ps _) = ps

-- Gets variables of a component
gCVs :: BComponent -> [Variable]
gCVs (BComponent _ _ vs) = vs

-- Gets component kind
gCK :: BComponent -> ComponentKind
gCK (BComponent ck _ _) = ck

gVTNm :: VTypeDef -> Name
gVTNm (VTypeEnum nm _) = nm
gVTNm (VTypeStrt nm _) = nm
gVTNm (DType nm _)     = nm
gVTNm (UType nm _ _)   = nm

-- gBlockNm: gets name of a block
gBlockNm :: Block -> Name
gBlockNm (BSystem nm _) = nm
gBlockNm (BCompound nm _ _) = nm
gBlockNm (BElement nm _) = nm

-- gBlockMTy: gets meta-type of a block
gBlockMTy :: Block -> IntoSysML_ASD_MM_Ns
gBlockMTy (BSystem _ _) = ASD_MM_System
gBlockMTy (BCompound nm _ _) = ASD_MM_Compound
gBlockMTy (BElement nm _) = ASD_MM_BElement

-- gElemNm: gets name of an ASD element
gElemNm :: ASDElem -> Name
gElemNm (ElemVT vt) = gVTNm vt
gElemNm (ElemB b) = gBlockNm b
gElemNm (ElemC c) = gCNm c

-- getStates desc = foldr (\e es-> if isState e then (getSt e):es else es) [] (gElems desc)
-- getTransitions desc = foldr (\e es-> if isTransition e then (getT e):es else es) [] (gElems desc)
-- getTheCs elems = foldl (\es e-> if not . isNode $ e then (getC e):es else es) [] elems

parse_venum :: ReadP VTypeDef
parse_venum = do
   string "enum"
   skipSpaces
   nm<-parse_id 
   skipSpaces
   char ':'
   skipSpaces
   ls<-manyTill (skipSpaces >> parse_id) (char '\n') 
   return (VTypeEnum nm ls)

parse_init_exp :: ReadP String
parse_init_exp = do
   iexp<-between (char '\"') (char '\"') (munch (/= '\"')) -- Parses until terminators
   skipSpaces
   return (iexp)

parse_ptype :: ReadP PType
parse_ptype = do
  pt <- parse_pinterval <|> parse_pint <|> parse_pnat <|> parse_preal <|> parse_pbool <|> parse_pstring 
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
  itn<-parse_ITN
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
  return (InFlowPort p)

--parse_DS::ReadP [String]
--parse_DS = do
--   between (char '{') (char '}') (skipSpaces >> many parse_spc_id)

parse_outfport :: ReadP Port
parse_outfport = do
  string "out"
  skipSpaces
  p<-parse_inner_prop_info
  skipSpaces
  ds<-between (char '{') (char '}') (sepBy (skipSpaces>>parse_id) (char ','))
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
  return (APIPort p pk)

parse_port :: ReadP Port
parse_port = do
  fp<- parse_infport <|> parse_outfport <|> parse_apiport
  return fp

parse_ports :: ReadP [Port]
parse_ports = do
   string "ports"
   skipSpaces
   fps<-between (char '{') (char '}') (many1 (skipSpaces>>parse_port>>=(\ps->skipSpaces>>return ps)))
   return fps

parse_vars :: ReadP [Variable]
parse_vars = do
   string "vars"
   skipSpaces
   vs<-between (char '{') (char '}') (many1 (skipSpaces >> parse_var)) --manyTill parse_var (char '}')
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

parse_eblock::ReadP ASDElem
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

parse_composition ::ReadP ASDElem
parse_composition = do
   string "composition"
   skipSpaces
   nm<-parse_id
   skipSpaces
   b1<-parse_id 
   skipSpaces
   string "->"
   skipSpaces
   b2<-parse_id 
   skipSpaces
   char ':'
   skipSpaces
   srcM<-parse_mult_comp_src 
   skipSpaces
   tgtM<-parse_mult
   skipSpaces
   return (ElemC (Composition nm b1 b2 srcM tgtM))

parse_asd_elem ::ReadP ASDElem
parse_asd_elem = do
   parse_eblock <|> parse_vtype <|> parse_composition

parse_ASD :: ReadP ASD
parse_ASD = do
   string "ASD"
   skipSpaces
   nm<-parse_id 
   skipSpaces
   char ':'
   skipSpaces
   es<- manyTill (skipSpaces>>parse_asd_elem) (skipSpaces>>eof)
   skipSpaces
   return (ASD nm es)


loadASDFrFile :: FilePath -> IO (Maybe ASD)
loadASDFrFile fn = 
    --contents <- readFile fn
    --let asd = parseMaybe parse_ASD contents
    --return asd
    readFile fn >>= return . parseMaybe parse_ASD
    

rootId :: String -> String
rootId nm = nm ++ "_StructureDiagram"

-- builds id of entity being named along with required edges 
qurNm :: String->String->QuadURel String
qurNm snm nm = singleQUR ((nm, show_asd_mm_n ASD_MM_Name)
               , ("ENmOf"++snm, show_asd_mm_e ASD_MM_Ename)
               , ("ENmOf"++snm, snm), ("ENmOf"++snm, nm))

-- Root quadruple of GwT to be constructed
qurRoot :: String->QuadURel String
qurRoot nm  = 
   let ns_m = (rootId nm, show_asd_mm_n ASD_MM_StructureDiagram) in 
   (qurNm (rootId nm) nm) `join` singleQURFrFst ns_m

-- Gets the node and edge type for an element
--gNETyForElem (ElemVT _) = (ASD_MM_ValueType, ASD_MM_EHasVTypes)
--gNETyForElem (ElemB _) = (ASD_MM_Block, ASD_MM_EHasBlocks)
--gNETyForElem (ElemC _ _ _ _) = (ASD_MM_Composition, ASD_MM_EHasCompositions)

-- Identifier of a value type node in a graph
vtyId :: String -> String
vtyId nm = nm  ++ "_VT"

-- Identifier of an element in a graph
elemId :: ASDElem -> String
elemId e@(ElemVT _) = vtyId . gElemNm $ e 
elemId e@(ElemB _) = blockId . gElemNm $ e
elemId (ElemC c) = compositionId (gCNm c ++ "_" ++ (gCSrc c) ++ "_" ++ (gCTgt c)) 

-- builds name of an edge from a node
mkenm_frn::String->String
mkenm_frn n = "E"++n

ptId::PType->String
ptId (PInterval n1 n2) = "PInterval" ++ "_" ++ (show n1) ++ "_" ++ (show n2) ++ "_PTy"
ptId pt = show pt ++ "_PTy"

atyId::AType->String
atyId (ATypeP pt) = ptId pt
atyId (ATypeId id) = vtyId id

opId :: String -> String -> String
opId cnm nm = cnm ++ "_" ++ nm ++ "_Op"

-- Identifier of an expression node in a graph
expId :: String -> String
expId e = e++ ":Exp"

-- Identifier of an enumeration literal in a graph
literalId :: String -> String -> String
literalId enm vnm = enm ++ "_" ++ vnm ++ "_L"

qur_ns_es_ptype::PType->QuadURel String
qur_ns_es_ptype pt@(PInterval n1 n2) = 
   let pt_nm = ptId pt 
       ns_m = singles (pt_nm, show_asd_mm_n ASD_MM_PInterval) 
       es_m = (set [(mkenm_frn $ pt_nm ++ "_lb", show_asd_mm_e ASD_MM_EPInterval_lb), 
               (mkenm_frn $ pt_nm ++ "_ub", show_asd_mm_e ASD_MM_EPInterval_ub)],
               set [(mkenm_frn $ pt_nm ++ "_lb", pt_nm), (mkenm_frn $ pt_nm ++ "_ub", pt_nm)],
               set [(mkenm_frn $ pt_nm ++ "_lb", ptId PInt), (mkenm_frn $ pt_nm ++ "_ub", ptId PInt)]) in
   (qurOneTpl ns_m es_m) `join` qur_ns_es_ptype (PInt)
qur_ns_es_ptype pt =  
  let pt_nm = ptId pt 
      ns_m = (pt_nm, show_asd_mm_n . read_asd_mm . show $ pt) in
  singleQURFrFst ns_m

--
-- Builds what is required for a typed name (TN), either a variable, a field or a flow port
qurTN :: String->TypedName->IntoSysML_ASD_MM_Ns->QuadURel String
qurTN cnm (TypedName nm nty) n_mm_ty = 
   let nnm = vtnId cnm nm n_mm_ty 
       enm_t = mkenm_frn $ nnm ++ "_type"
       nty_id = atyId nty 
       ns_m = (nnm, show_asd_mm_n n_mm_ty)
       es_m = (enm_t, show_asd_mm_e ASD_MM_ETypedName_type)
       src_m = (enm_t, nnm)
       tgt_m = (enm_t, nty_id)
       --es_m = (singles (enm_t, show_asd_mm_e ASD_MM_ETypedName_type), 
       --         singles (enm_t, nnm), singles (enm_t, nty_id)) 
       q = if is_ATy_a_Pty nty then qur_ns_es_ptype (gATyPTy nty) else nilQUR in
       --names_q = (nmQUR nnm nm) `combineQwIntoS` q in
   (qurNm nnm nm) `join` (q `join` (singleQUR (ns_m, es_m, src_m, tgt_m)))

--
-- Builds what is required for an ITN, either a variable, a field or a flow port
qurITN :: String-> Initialisable-> IntoSysML_ASD_MM_Ns->QuadURel String
qurITN cnm (Initialisable nm nty ie) n_mm_ty = 
   let nnm = vtnId cnm nm n_mm_ty
       iq = qurTN cnm (TypedName nm nty) n_mm_ty
       enm_i = mkenm_frn $ nnm ++ "_init" 
       nty_id = atyId nty
       ns_m = if null ie then nil else singles (expId ie, show_asd_mm_n ASD_MM_Exp) 
       es_m = (if null ie then nil else singles (enm_i, show_asd_mm_e ASD_MM_EInitialisable_init), 
                if null ie then nil else singles (enm_i, nnm), 
                if null ie then nil else singles (enm_i, expId ie)) in
   (qurOneTpl ns_m es_m) `join` iq

qurPort :: String -> Port -> QuadURel String
qurPort cnm po@(InFlowPort itn) = qurITN cnm itn (gPoMTy po)
qurPort cnm po@(OutFlowPort itn deps) = 
  let iqs = qurITN cnm itn (gPoMTy po) 
      enm d = mkenm_frn $ cnm ++ "_" ++ (gITNNm itn) ++ "_depends_" ++ d 
      es_m = foldl (\t d->((enm d, show_asd_mm_e ASD_MM_EOutFlowPort_depends), 
                          (enm d, vtnId cnm (gITNNm itn) $ gPoMTy po), 
                          (enm d, tnId cnm d)) `combineTwIntoS` t) (nil, nil, nil) deps in
  (qurOneTpl nil es_m) `join` iqs
qurPort cnm po@(APIPort itn k) = 
   let iq = qurITN cnm itn (gPoMTy po) 
       enm_k = mkenm_frn $ cnm ++ "_" ++ (gITNNm itn) ++ "_kind" 
       ns_m = (show k, show_asd_mm_n $ read_asd_mm . lower_fst . show $ k)
       pid = (tnId cnm) . gITNNm $ itn 
       es_m = ((enm_k, show_asd_mm_e ASD_MM_EAPIPort_kind), (enm_k, pid), (enm_k, show k)) in
   (singleQUR $ makeQFrTFst ns_m es_m) `join` iq

-- Builds what is required for a field
qurField::String->TypedName->QuadURel String
qurField cnm tn  = qurTN cnm tn ASD_MM_Field

-- Builds what is required for a variable
qurVariable::String-> Variable->QuadURel String
qurVariable cnm (Variable itn vk)  =
  let iq =  qurITN cnm itn ASD_MM_Variable 
      ns_m = (show vk, show_asd_mm_n $ read_asd_mm . lower_fst . show $ vk) 
      vid = varId cnm . gITNNm $ itn 
      enm_k = mkenm_frn $ vid ++ "_kind" 
      es_m = ((enm_k, show_asd_mm_e ASD_MM_EVariable_kind), (enm_k, vid), (enm_k, show vk)) in
  singleQUR (makeQFrTFst ns_m es_m) `join` iq

-- Ports of a block 
qurPorts :: Foldable t =>String-> t Port->QuadURel String
qurPorts nmBl ps = 
  let iqs = foldl (\qur p->qurPort nmBl p `join` qur) nilQUR ps
      enm_l p = mkenm_frn $ tnId nmBl (gPoNm p) ++ "_port" 
      es_m = foldl (\esml p->((enm_l p, show_asd_mm_e ASD_MM_EBlock_ports), 
                             (enm_l p, nmBl), 
                             (enm_l p, tnId nmBl $ gPoNm p)) 
                             `combineTwIntoS` esml) (nil, nil, nil) ps in
  (qurOneTpl nil es_m) `join` iqs

-- A block
qurBlock::Foldable t =>String->IntoSysML_ASD_MM_Ns->t Port->QuadURel String
qurBlock nmb bl_mty fps = 
  let nnm = blockId nmb 
      ns_m = (nnm, show_asd_mm_n bl_mty) in
  gJoin [qurNm nnm nmb, singleQURFrFst ns_m, qurPorts nnm fps]

-- A component
qurComponent::String->BComponent->IntoSysML_ASD_MM_Ns->QuadURel String
qurComponent nm c bl_mty = 
   let iqs = qurBlock nm bl_mty (gCFps c) 
       iqs' = foldl (\qs v->qurVariable nm v `join` qs) iqs $ gCVs c 
       ns_m = singles (show . gCK $ c, show_asd_mm_n $ read_asd_mm . lower_fst  . show . gCK $ c) 
       enm_k = mkenm_frn $ (blockId nm) ++ "_kind" 
       enm_v v = mkenm_frn $ (blockId nm) ++ "_" ++ ((varId nm) . gITNNm . gVarITN $ v)
       es_m = (singles (enm_k, show_asd_mm_e ASD_MM_EComponent_kind), 
               singles (enm_k, blockId nm), singles (enm_k, show . gCK $ c)) 
       es_m' = foldl (\vs v->((enm_v v, show_asd_mm_e ASD_MM_EComponent_vars), (enm_v v, blockId nm), 
                (enm_v v, (varId nm) . gITNNm . gVarITN $ v)) 
               `combineTwIntoS` vs) es_m (gCVs c) in
  (qurOneTpl ns_m es_m') `join` iqs'

mvalId :: MultVal -> String
mvalId (MultN n) = "MultN_" ++ (show n)
mvalId MMany = "Mult*" 
valId :: Show a => a -> String
valId n = (show n) ++ "_Val"

qurMultVal :: MultVal -> QuadURel String
qurMultVal mv@(MultN n) =
  let ns_m = set [(mvalId mv, show_asd_mm_n ASD_MM_MultValNum), (valId n, show_asd_mm_n ASD_MM_Nat)] in
  let enm = mkenm_frn $ mvalId mv in
  let es_m = (singles (enm, show_asd_mm_e ASD_MM_EMultValNum_n), singles (enm, mvalId mv), singles (enm, (show n) ++ "_Val")) in
  qurOneTpl ns_m es_m 

multId :: Mult -> String
multId (MultS mv) = "MultS_" ++ mvalId mv
multId (MultR mvs mvt) = "MultR_" ++ (show mvs) ++ "_" ++  (mvalId mvt)

qurMult :: Mult-> QuadURel String
qurMult m@(MultS mv) = 
  let nnm = multId m 
      ns_m = (nnm, show_asd_mm_n ASD_MM_MultSingle) 
      enm = mkenm_frn $ nnm ++ "_val" 
      es_m = ((enm, show_asd_mm_e ASD_MM_EMultSingle_val), (enm, nnm), (enm, mvalId mv)) in
  singleQUR (makeQFrTFst ns_m es_m) `join` (qurMultVal mv)
qurMult m@(MultR mvs mvt) = 
  let nnm = multId m 
      ns_m = set [(nnm, show_asd_mm_n ASD_MM_MultRange), (valId mvs, show_asd_mm_n ASD_MM_Nat)]
      enm1 = mkenm_frn $ nnm ++ "_lb" 
      enm2 = mkenm_frn $ nnm ++ "_ub" 
      es_m = (set [(enm1, show_asd_mm_e ASD_MM_EMultRange_lb), (enm2, show_asd_mm_e ASD_MM_EMultRange_ub)], 
              set [(enm1, nnm), (enm2, nnm)], set [(enm1, valId mvs), (enm2, mvalId mvt)]) in
  (qurOneTpl ns_m es_m) `join` (qurMultVal mvt)

qurHas ::String->String->IntoSysML_ASD_MM_Es->QuadURel String
qurHas rnm tnm mty =
  let enm = mkenm_frn $ rnm ++ "_" ++ tnm 
      q = (nil, singles (enm, show_asd_mm_e mty)
         , singles (enm, rnm)
         , singles (enm, tnm)) in
  QuadURel q

qurOperation ::String->Operation->QuadURel String
qurOperation inm (Operation nm ps aty) = 
  let nnm = opId inm nm 
      q = foldl (\qur f->(qurField inm f) `join` qur) nilQUR ps 
      ns_m = singles (nnm, show_asd_mm_n ASD_MM_Operation) 
      enm_ps k = mkenm_frn $ nnm ++ "_params_" ++ (show k) 
      enm_ret = mkenm_frn $ nnm ++ "_return" 
      tq = if is_ATy_a_Pty aty then qur_ns_es_ptype (gATyPTy aty) else nilQUR 
      es_m_0 = foldl(\ts p->((enm_ps $ (length . fstT $ ts) + 1, show_asd_mm_e ASD_MM_EOperation_params), 
               (enm_ps $ (length . fstT $ ts) + 1, nnm), 
               (enm_ps $ (length . fstT $ ts) + 1, tnId inm $ gTNNm p)) `combineTwIntoS` ts) (nil, nil, nil) ps 
      es_m = ((enm_ret, show_asd_mm_e ASD_MM_EOperation_return), (enm_ret, nnm), (enm_ret, atyId aty)) `combineTwIntoS` es_m_0 in
  gJoin [qurOneTpl ns_m es_m, qurNm nnm nm, q]


qurElem :: String-> ASDElem->QuadURel String
qurElem rnm (ElemVT (DType nm pt)) = 
  let nnm = vtyId nm 
      q0 = qur_ns_es_ptype pt
      ns_m = (nnm, show_asd_mm_n ASD_MM_DType)
      es_m = ((mkenm_frn $ nnm ++ "_base", show_asd_mm_e ASD_MM_EDType_base),
              (mkenm_frn $ nnm ++ "_base", nnm),
              (mkenm_frn $ nnm ++ "_base", ptId pt)) in
  gJoin [qurNm nnm nm, singleQUR $ makeQFrTFst ns_m es_m, q0
            , qurHas rnm nnm ASD_MM_EHasVTypes]
qurElem rnm (ElemVT (UType nm pt unm)) = 
  let nnm = vtyId nm in
  let q0 = qur_ns_es_ptype pt in
  let ns_m = set [(nnm, show_asd_mm_n ASD_MM_UnitType), (unm, show_asd_mm_n ASD_MM_Name)]  in 
  let es_m = (set [(mkenm_frn $ nnm ++ "_base_", show_asd_mm_e ASD_MM_EDType_base),
              (mkenm_frn $ nnm ++ "_unit_", show_asd_mm_e ASD_MM_EUnitType_unit)],
              set [(mkenm_frn $ nnm ++ "_base_", nnm), (mkenm_frn $ nnm ++ "_unit_", nnm)],
              set [(mkenm_frn $ nnm ++ "_base_", ptId pt), (mkenm_frn $ nnm ++ "_unit_", unm)]) in
  gJoin [qurNm nnm nm, qur $ makeQFrTFst ns_m es_m, q0, qurHas rnm nnm ASD_MM_EHasVTypes]
qurElem rnm (ElemVT (VTypeStrt nm ps)) = 
  let nnm = vtyId nm in
  -- build graph portion for properties
  let qps = foldl (\q (FieldI itn)->(qurITN nm itn ASD_MM_FieldI) `join` q) nilQUR ps 
      enm_f k = mkenm_frn $ nnm ++ "_fields_" ++ (show k) 
      ns_m = singles (nnm, show_asd_mm_n ASD_MM_StrtType) 
      es_m = foldl (\t (FieldI itn)->((enm_f $ (length . fstT $ t) + 1, show_asd_mm_e ASD_MM_EStrtType_fields), 
                            (enm_f $ (length . fstT $ t) + 1, nnm), (enm_f $ (length . fstT $ t) + 1, (tnId nm) . gITNNm $ itn)) 
                             `combineTwIntoS` t) (nil, nil, nil) ps in
  gJoin [qurNm nnm nm, qurOneTpl ns_m es_m, qps, qurHas rnm nnm ASD_MM_EHasVTypes]
qurElem rnm (ElemVT (VTypeEnum nm ls)) = 
   let nnm = vtyId nm
       qls = foldr (\l q->gJoin [qurNm (literalId nm l) l
                            , qur $ makeQFrTFst (singles (literalId nm l, show_asd_mm_n ASD_MM_Literal)) (nil, nil, nil)
                            , q]) nilQUR ls 
       enm_l k = mkenm_frn $ nnm ++ "_literals" ++ (show k) 
       ns_m = singles (nnm, show_asd_mm_n ASD_MM_Enumeration) 
       es_m = foldr (\l t->((enm_l (length . fstT $ t), show_asd_mm_e ASD_MM_EHasLiterals), 
                            (enm_l (length . fstT $ t), nnm), (enm_l (length . fstT $ t), literalId nm l)) 
                             `combineTwIntoS` t) (nil, nil, nil) ls in
   gJoin [qurNm nnm nm, qurOneTpl ns_m es_m, qls, qurHas rnm nnm ASD_MM_EHasVTypes]
qurElem rnm (ElemVT (Interface nm ops)) =
   let nnm = vtyId nm 
       ns_m = singles (nnm, show_asd_mm_n ASD_MM_Interface) 
       enm k =  mkenm_frn $ nnm ++ "_ops_" ++ (show k)
       iq = foldl (\qs op->qurOperation nm op `join` qs) nilQUR ops
       es_m = foldl (\lts op->((enm $ (length . fstT $ lts) + 1, show_asd_mm_e ASD_MM_EInterface_ops), 
                  (enm $ (length . fstT $ lts) + 1, nnm), (enm $ (length . fstT $ lts) + 1, opId nm $ gOpNm op)) `combineTwIntoS` lts) (nil, nil, nil) ops in 
    gJoin [qurNm nnm nm, qurOneTpl ns_m es_m, iq, qurHas rnm nnm ASD_MM_EHasVTypes]
-- Compositions
qurElem rnm e@(ElemC c) =
  let nnm = elemId e 
      ns_m = set [(nnm, show_asd_mm_n ASD_MM_Composition), (show $ gCSrcM c, show_asd_mm_n $ read_asd_mm . lower_fst . show . gCSrcM $ c)]
      enm_s = mkenm_frn $ (gCSrc c) ++ "_" ++ (gCTgt c) ++ "_src" 
      enm_t = mkenm_frn $ (gCSrc c) ++ "_" ++ (gCTgt c) ++ "_tgt" 
      enm_sm = mkenm_frn $ (gCSrc c) ++ "_" ++ (gCTgt c) ++ "_srcM"
      enm_tm = mkenm_frn $ (gCSrc c) ++ "_" ++ (gCTgt c) ++ "_tgtM"
      es_m = (set [(enm_s, show_asd_mm_e ASD_MM_EComposition_src), 
               (enm_t, show_asd_mm_e ASD_MM_EComposition_tgt),
               (enm_sm, show_asd_mm_e ASD_MM_EComposition_srcM), 
               (enm_tm, show_asd_mm_e ASD_MM_EComposition_tgtM)],
              set [(enm_s, nnm), (enm_t, nnm), (enm_sm, nnm), (enm_tm, nnm)], 
              set [(enm_s, blockId . gCSrc $ c), (enm_t, blockId . gCTgt $ c), (enm_sm, show . gCSrcM $ c), (enm_tm, multId . gCTgtM $ c)]) in
  gJoin [qurNm nnm $ gCNm c, qurOneTpl ns_m es_m, qurMult . gCTgtM $ c
         , qurHas rnm nnm ASD_MM_EHasCompositions]
-- Blocks/Systems
qurElem rnm (ElemB (BSystem nm fps)) = 
  qurBlock nm ASD_MM_System fps `join` qurHas rnm (blockId nm) ASD_MM_EHasBlocks
-- Blocks/Elements
qurElem rnm (ElemB (BElement nm c)) =
   let iqs = qurComponent nm c ASD_MM_BElement in
   iqs `join` (qurHas rnm (blockId nm) ASD_MM_EHasBlocks)
-- Blocks/Elements
qurElem rnm (ElemB (BCompound nm pk c)) =
  let iqs = qurComponent nm c ASD_MM_Compound in
  let nnm = blockId nm in
  let ns_m = singles (show pk, show_asd_mm_n . read_asd_mm . lower_fst  . show  $ pk) in
  let enm_p = mkenm_frn $ nnm ++ "_phenomena" in
  let es_m = (singles (enm_p, show_asd_mm_e ASD_MM_ECompound_phenomena), singles (enm_p, nnm), singles (enm_p, show pk)) in
  gJoin [qurOneTpl ns_m es_m, iqs, qurHas rnm nnm ASD_MM_EHasBlocks]

-- consGwT_elem rnm elem = 
--   let enm = elemId elem in
--   let (nty, ety) = gNETyForElem elem in
--   let ns_m_i = [(enm, show_asd_mm_n nty)] in 
--   let es_m_i = ([(mkenm_frn $ rnm ++ "_" ++ enm, show_asd_mm_e ety)], 
--                 [(mkenm_frn $ rnm ++ "_" ++ enm, rnm)], 
--                 [(mkenm_frn $ rnm ++ "_" ++ enm, enm)]) in
--   let names_q = (mk_nm_info_q enm (gElemNm elem)) `combineQwInsert` nilQl in
--   names_q `combineQwUnion` (makeQFrTFst ns_m_i es_m_i) `combineQwUnion` (gwT_InnerElem elem)

qurElems::Foldable t=>String->t ASDElem-> QuadURel String
qurElems rnm es = foldr(\e qur->(qurElem rnm e) `join` qur) nilQUR es

-- Constructs the graph with typing for given ASD model
gwt_asd :: ASD->GrwT String String
gwt_asd (ASD nm es)  = 
   -- initial set of nodes with type mapping
   let QuadURel (ns_m, es_m, src_m, tgt_m) = (qurRoot nm) `join` (qurElems (rootId nm) es) in
   let asd_g = consG (fmap fst ns_m) (fmap fst es_m) src_m tgt_m in
   consGWT asd_g (consGM (ns_m) (es_m))

loadASD :: FilePath -> IO (GrwT String String)
loadASD fn = do
   oasd <- loadASDFrFile fn
   if isNil oasd
      then do
         putStrLn "The ASD definition could not be parsed."
         return Gr_Cls.empty
      else do
         let asd_g = gwt_asd $ the oasd
         return asd_g


def_path = "IntoSysML/Examples/"

test1 :: [(Mult, String)]
test1 = readP_to_S parse_mults "5"
test2 :: [(Mult, String)]
test2 = readP_to_S parse_mults "*"
test3 = readP_to_S parse_ptype "Int"
test4 = readP_to_S parse_ptype "Interval 5 6"
test5a = readP_to_S parse_venum "enum OpenClosed : open closed\n"
test5b = readP_to_S (manyTill (skipSpaces>>parse_id) eof) "open closed"
test6a = readP_to_S parse_ITN  "v1 OpenClosed \"closed\""
test6b = readP_to_S parse_port "out v1 OpenClosed \"closed\" {}"
test6c = readP_to_S parse_port "out v1 OpenClosed \"closed\" {v2}"
test6d :: [(Port, String)]
test6d = readP_to_S parse_port "in v2 OpenClosed"
test7 = readP_to_S parse_port "out WOUT FlowRate {WIN, VIN}"

test8a :: IO ()
test8a = do
   asd<-loadASDFrFile (def_path ++ "water_tanks.asd")
   print asd

test8b :: IO [(ASD, String)]
test8b = do
   contents <- readFile (def_path ++ "water_tanks.asd")
   return $ readP_to_S parse_ASD contents

test8c :: IO ()
test8c = do
  asd_g<-loadASD $ def_path ++ "three_water_tanks.asd"
  print asd_g

test9 :: IO [(ASD, String)]
test9 = do
   contents <- readFile (def_path ++ "test_asd.asd")
   return $ readP_to_S parse_ASD contents