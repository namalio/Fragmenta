-----------------------------
-- Project: PCs/Fragmenta
-- Module: 'PCsParsing'
-- Description: Parses PC textual descriptions
-- Author: Nuno Amálio
-----------------------------
module PCs.PCsParsing(loadPC) where

import Text.ParserCombinators.ReadP
import Control.Applicative
import Control.Monad(when, unless)
import Grs
import SGrs
import Sets
import Relations
import TheNil
import MyMaybe
import GrswT
import ParseUtils
import PCs.PCs_MM_Names
import SimpleFuns ( nilQl )
import ParsingCommon(
   parseId
   , parseMaybe
   , parse_until_chs
   , parse_strings
   , parseWord
   , parseAnyStr)
import Gr_Cls
import SimpleFuns
import QUR

-- A node has a name a type and possibly an associated operator
-- A reference may be inner
type Guard = Maybe String 
data OpKind = OpChoice | OpIntChoice | OpInterleave | OpThrow | OpIf
   deriving(Eq, Show, Read) 
data NodeInfo = Atom (Maybe String) (Maybe (String, String)) Guard
              | Compound String [String] 
              | Operator OpKind [String] 
              | Reference Bool String Guard [String] [(String,String)]
              | Stop
              | Skip 
              | Import 
   deriving(Eq, Show) 

data Node = Node String NodeInfo 
   deriving(Eq, Show)
-- A ref connector may have parameters and be hidden or not; an op connector may have a guard 
data ConnectorInfo = After Bool | Ref [String] Bool | Op | OpIfB Guard | OpElse | OpJump 
   deriving(Eq, Show) 
-- An connector has a name, a type and source and target nodes
data Connector = Connector ConnectorInfo String String 
   deriving(Eq, Show) 
data Elem = ElemN Node | ElemC Connector 
   deriving(Eq, Show) 
 -- A PC definition has a name, a start node, and list of elements
data PCDef = PCDef String String [Elem] 
   deriving(Eq, Show)

isNode :: Elem -> Bool
isNode (ElemN _) = True
isNode _ = False
getN :: Elem -> Node
getN (ElemN n) = n
getC :: Elem -> Connector
getC (ElemC c) = c

getTheNodes :: Foldable t => t Elem -> [Node]
getTheNodes = foldl (\es e-> if isNode e then (getN e):es else es) []

getTheCs :: Foldable t => t Elem -> [Connector]
getTheCs = foldl (\es e-> if not . isNode $ e then (getC e):es else es) [] 

pcStart :: ReadP(String, String)
pcStart = do
   string "PC"
   skipSpaces
   pcnm<-parse_until_chs "@" -- (many1 . satisfy) (/= '@')
   char '@'
   st<- str_until_end_of_stm
   skipSpaces
   return (pcnm, st)

str_until_end_of_stm::ReadP String
str_until_end_of_stm = do
   s<-parse_until_chs "\n "
   return s

pcParams::Char->ReadP [String]
pcParams ch = do
   char ch
   parse_strings "," (parseAnyStr ",[")
   --parse_ls_ids ","

pcCompound :: ReadP Node
pcCompound = do
   string "compound"
   skipSpaces
   cnm<-parse_until_chs "@."
   ps<- pcParams '.' <++ return []
   char '@'
   start<-parseWord 
   skipSpaces
   return (Node cnm $ Compound start ps)

pc_atom_atSet:: ReadP String
pc_atom_atSet = do
   char ':'
   s<-parse_until_chs ">"
   return s

pc_atom_rnm :: ReadP (Maybe String)
pc_atom_rnm = do
   char '.' 
   s<-parseId
   return (Just s)

pc_atom_exp :: ReadP (Maybe (String, String))
pc_atom_exp = do
   char '<' 
   s1<-parseId <++ return ""
   skipSpaces
   s2<-pc_atom_atSet 
   char '>'
   return (Just (s1, s2))

pc_guard0 :: ReadP (Maybe String)
pc_guard0 = do
   char '{'
   g <- parse_until_chs "}"
   char '}'
   return (Just g)

pc_guard :: ReadP (Maybe String)
pc_guard = do
   g<-pc_guard0 <++ return Nothing
   return g

pc_atom :: ReadP Node
pc_atom = do
   string "atom"
   skipSpaces
   anm<-parseId
   skipSpaces 
   rnm<-pc_atom_rnm<++ return Nothing
   skipSpaces 
   aexp<-pc_atom_exp <++ return Nothing
   skipSpaces 
   g<-pc_guard
   skipSpaces 
   return (Node anm $ Atom rnm aexp g)

pc_OpKind :: ReadP OpKind
pc_OpKind = parseWord >>= return . read
--   do
--   ops<-parseWord
--   let op = read ops
--   return op

pc_operator :: ReadP Node
pc_operator = do
   string "operator"
   skipSpaces
   o_nm<-parseId
   char '.'
   op<-pc_OpKind
   ps<-(pcParams ':')<++return []
   skipSpaces
   return (Node o_nm $ Operator op ps)

pcRenaming :: ReadP (String, String)
pcRenaming = do
   fr<-parse_until_chs "/"
   char '/'
   to<-parse_until_chs ",]"
   return (fr, to)

pcRenamings :: ReadP [(String, String)]
pcRenamings = do
   char '['
   rs<-sepBy pcRenaming (satisfy (\ch->any (ch==) ","))
   char ']'
   return rs

pcRefToP::ReadP (String, [String], [(String, String)])
pcRefToP = do
   char ':'
   rnm<-parseId
   ps<-pcParams '.' <++ return []
   skipSpaces
   rs<- pcRenamings <++ return []
   return (rnm, ps, rs)


pcReference :: ReadP Node
pcReference = do
   string "reference"
   skipSpaces
   sinner <- string "inner" <++ return ""
   let inner = sinner == "inner"
   skipSpaces
   rnm<-parseId
   skipSpaces
   g<-pc_guard
   skipSpaces
   (pnm, ps, rs)<-pcRefToP<++ return ("", [], []) 
   skipSpaces
   --ps<-pcParams '.' <++ return []
   --skipSpaces
   --let hp = if null ps then "" else head ps
   --let ps' = if null ps then [] else tail ps
   return (Node rnm $ Reference inner pnm g ps rs)

pc_stop :: ReadP Node
pc_stop = do
   string "stop"
   skipSpaces
   nm<-str_until_end_of_stm 
   skipSpaces
   return (Node nm $ Stop)

pc_skip :: ReadP Node
pc_skip = do
   string "skip"
   skipSpaces
   nm<-str_until_end_of_stm 
   skipSpaces
   return (Node nm $ Skip)

pc_import :: ReadP Node
pc_import = do
   string "import"
   skipSpaces
   nm<-str_until_end_of_stm
   skipSpaces
   return (Node nm $ Import)

pcAfterC :: ReadP Connector
pcAfterC  = do
   string "after_connector"
   skipSpaces
   sopen <- string "open " <++ return ""
   let open = sopen == "open "
   skipSpaces
   from<-parse_until_chs " -" 
   skipSpaces
   string "->"
   skipSpaces
   to<-parseWord 
   skipSpaces
   return (Connector (After open) from to)

pc_C_fr_to :: ReadP (String, String)
pc_C_fr_to = do
   fr<-parseId
   skipSpaces
   string "->"
   skipSpaces
   to<-parseId
   skipSpaces
   return (fr, to)

pc_opB :: ReadP Connector
pc_opB  = do
   string "op_connector"
   skipSpaces
   (fr, to)<-pc_C_fr_to
   skipSpaces
   return (Connector Op fr to)

pc_opBG :: ReadP Connector
pc_opBG  = do
   string "op_connector_g"
   skipSpaces
   (fr, to)<-pc_C_fr_to
   skipSpaces
   g <- pc_guard 
   skipSpaces
   return (Connector (OpIfB g) fr to)

pc_opElseB :: ReadP Connector
pc_opElseB  = do
   string "op_else_connector"
   skipSpaces
   (fr, to)<-pc_C_fr_to
   skipSpaces
   return (Connector OpElse fr to)

pc_opJumpB :: ReadP Connector
pc_opJumpB = do
   string "op_jump_connector"
   skipSpaces
   (fr, to)<-pc_C_fr_to
   skipSpaces
   return (Connector OpJump fr to)

pc_referenceC :: ReadP Connector
pc_referenceC  = do
   string "ref_connector"
   skipSpaces
   shidden <- string "hidden" <++ return ""
   let hidden = shidden == "hidden"
   skipSpaces
   (proxy, ref)<-pc_C_fr_to
   ps<-(pcParams '.') <++ return []
   skipSpaces
   return (Connector (Ref ps hidden) proxy ref)

pc_elemN :: ReadP Elem
pc_elemN = do
   n<-pcCompound <|> pc_atom <|> pc_operator <|> pcReference <|> pc_stop <|> pc_skip <|> pc_import
   return (ElemN n)

pc_elemC :: ReadP Elem
pc_elemC = do
   c<-pcAfterC <|> pc_opB <|> pc_referenceC <|> pc_opBG <|> pc_opElseB <|> pc_opJumpB
   return (ElemC c)

pc_elem :: ReadP Elem
pc_elem  = do
   e<- pc_elemN <|> pc_elemC 
   return e

pc_def :: ReadP PCDef
pc_def = do
   (pcnm, start)<-pcStart
   es<-manyTill pc_elem eof
   return (PCDef pcnm start es)

loadPCFrFile :: FilePath -> IO (Maybe PCDef)
loadPCFrFile fn = do   
    contents <- readFile fn
    --makes sure it is read
    let pc = parseMaybe pc_def contents
    return pc

combineQAsConcat :: ([a1], [a2], [a3], [a4]) -> ([a1], [a2], [a3], [a4]) -> ([a1], [a2], [a3], [a4])
combineQAsConcat (x, y, z, w) (x', y', z', w') = (x++x', y++y', z++z', w++w')
combineQAsUnion :: (Eq a1, Eq a2, Eq a3, Eq a4) => (Set a1, Set a2, Set a3, Set a4) -> (Set a1, Set a2, Set a3, Set a4) -> (Set a1, Set a2, Set a3, Set a4)
combineQAsUnion (x, y, z, w) (x', y', z', w') = (x `union` x', y `union` y', z `union` z', w `union` w')
-- combineQAsInsert (x, y, z, w) (x', y', z', w') = (insert x x', insert y y', insert z z', insert w w')
combineQwUnionOfFst::Eq a=>Set a->(Set a, b, c, d) ->(Set a, b, c, d)
combineQwUnionOfFst x (x', y', z', w') = (x `union` x', y', z', w')
--combineQAsUnionLs qs = foldr (\q qs->q `combineQAsUnion` qs) nilQl qs

extractInfo :: NodeInfo -> (String, [String])
extractInfo (Atom rnm aexp g) = (show_cmm_n CMM_Atom, (maybeToLs rnm)++(maybeToLs g)++(if isNil aexp then [] else [fst . the $ aexp] ++ [snd . the $ aexp]))
extractInfo (Compound _ ps) = (show_cmm_n CMM_Compound, ps)
--extractInfo (Reference rn ps _) = pair_up (show_cmm_n CMM_Reference) $ if null rn then [] else (rn:ps)
extractInfo (Operator op ps) = (show_cmm_n CMM_Operator, ps)
extractInfo Stop = (show_cmm_n CMM_Stop, [])
extractInfo Skip = (show_cmm_n CMM_Skip, [])
extractInfo Import = (show_cmm_n CMM_Import, [])

-- constructs name of parameter
mkParamNm::String->String->Int->String
mkParamNm nm p k = nm ++ "_param_"++ show k ++ "_" ++ p

-- builds parameters of edges
mkEPNm :: String -> String ->String
mkEPNm nm p = "EParam" ++ nm ++ "_" ++ p 
cNm :: String -> String
cNm nm = nm ++ "_"

mkEnmQ ::String-> String -> QuadURel String
mkEnmQ enm nm = 
   let eNm enm = "ENmOf"++enm in
   singleQUR ((cNm nm, show_cmm_n CMM_Name), (eNm enm, show_cmm_e CMM_Ename), 
      (eNm enm, enm), (eNm enm, cNm nm))

-- builds node and edges for start of compound 
mkConnForCompound ::String ->String -> QuadURel String
mkConnForCompound nm st = 
   let cnNm = "Def" ++ nm in -- name of connector node
   let eSrcNm = "E" ++ cnNm ++ "Src" in
   let eTgtNm = "E" ++ cnNm ++ "Tgt" in
   qurOneTpl (singles (cnNm, show_cmm_n CMM_DefinesC)) ((eSrcNm, show_cmm_e CMM_EDefinesCSrc) `intoSet` singles (eTgtNm, show_cmm_e CMM_EDefinesCTgt), (eSrcNm, cnNm) `intoSet` singles (eTgtNm, cnNm), (eSrcNm, nm) `intoSet` singles (eTgtNm, st))

mkAEnnm :: String -> String
mkAEnnm nm = nm ++ "_anyExp"

mk_st_AnyExp :: String -> QuadURel String
mk_st_AnyExp nm = singleQUR ((mkAEnnm nm, show_cmm_n CMM_AnyExp), (mkenm, show_cmm_e CMM_EAtomExp), (mkenm, nm), (mkenm, mkAEnnm nm))
    where mkenm = "EAE_"++nm

mk_P_lq ::Show a=>String ->String->Int->a->QuadURel String
mk_P_lq nm p k e_ty_ps = 
   singleQUR ((mkParamNm nm p k, show_cmm_n CMM_Parameter), 
      (mkEPNm nm p, show_cmm_e e_ty_ps), 
      (mkEPNm nm p, mkAEnnm nm), 
      (mkEPNm nm p, mkParamNm nm p k))

mkAnyExpQ ::String->Pair String->QuadURel String
mkAnyExpQ nm (enm, ats) = 
    (mk_st_AnyExp nm) `join` (mk_P_lq nm enm 1 CMM_EatVal) `join` (mk_P_lq nm ats 1 CMM_EatSet)

mk_ren_nm ::String->String->String->String
mk_ren_nm nm fr to = nm ++ "_renaming_"++fr++"_"++to

mk_e_Ren::String->String->String ->String
mk_e_Ren nm fr to  = "ERen"++nm++"_"++fr++"_"++to

mkRenamingQUR::String->String->String->QuadURel String
mkRenamingQUR nm fr to = singleQUR ((mk_ren_nm nm fr to, show_cmm_n CMM_Renaming)
    , (mk_e_Ren nm fr to, show_cmm_e CMM_ERenamings)
    , (mk_e_Ren nm fr to, nm)
    , (mk_e_Ren nm fr to, mk_ren_nm nm fr to))

mkHasParamQ::String->String->Int->QuadURel String
mkHasParamQ nm p k = 
   singleQUR ((mkParamNm nm p k, show_cmm_n CMM_Parameter)
      , (mkEPNm nm p, show_cmm_e CMM_EHasParams)
      , (mkEPNm nm p, nm), (mkEPNm nm p, mkParamNm nm p k))

--consHasPs :: String -> [String] -> QuadURel String
--consHasPs _ [] = nilQUR
--consHasPs nm (p:ps) = mkHasParamQ nm p `join` (consHasPs nm ps)

consHasPs :: String -> [String] -> QuadURel String
consHasPs nm ps = foldr (\(p, k) qs->mkHasParamQ nm p k `join` qs) nilQUR (zip ps [1..length ps])

mkGuardQ :: String -> Maybe String -> QuadURel String
mkGuardQ nm Nothing = nilQUR
mkGuardQ nm (Just g) =
   let gnm =  nm ++ "_guard_"++g in
   singleQUR ((gnm, show_cmm_n CMM_Guard), ("E"++nm++"_g", show_cmm_e CMM_EHasGuard), ("E"++nm++"_g", nm), ("E"++nm++"_g", gnm))

nodeOfOp::OpKind->String
nodeOfOp OpChoice = show_cmm_n CMM_VOpChoice
nodeOfOp OpIntChoice = show_cmm_n CMM_VOpIntChoice
nodeOfOp OpInterleave = show_cmm_n CMM_VOpInterleave
nodeOfOp OpThrow = show_cmm_n CMM_VOpThrow
nodeOfOp OpIf = show_cmm_n CMM_VOpIf

nmOfOp::OpKind->String
nmOfOp op = let op' = show op in op'++"_Val"

getNodesInfo ::Foldable t=>t Node -> QuadURel String
getNodesInfo ns = 
   let fQ (x, _, _, _) = x 
       yesV = ("YesV", show_cmm_n CMM_VYes) 
       noV = ("NoV", show_cmm_n CMM_VNo) 
       yn_vals = yesV `intoSet` singles noV in
   foldl (\ns' n-> (cons n (dom_of . fstQUR $ ns') `join` ns')) (qurOneTpl yn_vals (nil, nil, nil)) ns
   where --cQ p = (singles p, nil, nil, nil)
         mkOpP op = let op' = show op in (nmOfOp op, nodeOfOp op)
         mkQ nm op ns_m = qurOneTpl ns_m (singles ("E"++nm++"_op", show_cmm_e CMM_ECombination_op), singles ("E"++nm++"_op", nm), singles ("E"++nm++"_op", nmOfOp op))
         cons (Node nm (Compound start ps)) _ = consForC nm start `join` consHasPs nm ps
         cons (Node nm (Operator op ps)) ns = consForOp nm op ps ns
         cons (Node nm (Reference i rn g ps rs)) _ = gJoin [(if null rn then (singleQURFrFst $ rP nm) else consForRef nm rn ps rs), mkGuardQ nm g, consRenamings nm rs, consRIQ nm i]
         cons (Node nm (Atom rnm aexp g)) _ = (mkEnmQ nm $ atNm nm rnm) `join` (gJoin [mkGuardQ nm g, atPs nm aexp, singleQURFrFst (nm, show_cmm_n CMM_Atom)])
         cons (Node nm Import) _ = let p = (nm, show_cmm_n CMM_Import) in (mkEnmQ nm nm) `join` singleQURFrFst p
         cons (Node nm ni) _ = let (ty, _) = extractInfo ni in singleQURFrFst (nm, ty)
         consRenamings nm rs = foldr (\(fr, to) rqs->(mkRenamingQUR nm fr to) `join` rqs) nilQUR rs
         consForC nm start = (mkEnmQ nm nm) `join` (singleQURFrFst (nm, show_cmm_n CMM_Compound) `join` mkConnForCompound nm start)
         mkQURForRNm nm rn = singleQUR ((cNm rn, show_cmm_n CMM_Name), ("ERNmOf"++nm, show_cmm_e CMM_EReference_name), ("ERNmOf"++nm, nm), ("ERNmOf"++nm, cNm rn))
         consRIQ nm i = let iv = if i then "YesV" else "NoV" in qurOneTpl nil (singles ("E"++nm++"_inner", show_cmm_e CMM_EReference_inner), singles ("E"++nm++"_inner", nm), singles ("E"++nm++"_inner", iv))
         consForRef nm rn ps rs = foldr(\(p, k) qs->mkHasParamQ nm p k `join` qs) ((mkQURForRNm nm rn) `join` (singleQURFrFst $ rP nm)) (zip ps [1..length ps]) 
         consForOp_ nm op ns = let p = (nm, show_cmm_n CMM_Combination) in if (nmOfOp op) `elem` ns then mkQ nm op (singles p) else mkQ nm op (p `intoSet` singles (mkOpP op))
         consForOp nm op ps ns = foldr(\(p, k) qs-> qs `join` (singleQUR ((mkParamNm nm p k, show_cmm_n CMM_Parameter), (mkEPNm nm p, show_cmm_e CMM_EHasParams), (mkEPNm nm p, nm), (mkEPNm nm p, mkParamNm nm p k)))) (consForOp_ nm op ns) (zip ps [1..length ps]) 
         atNm nm rnm = if isNil rnm then nm else the rnm
         atPs nm aexp = if isNil aexp then nilQUR else mkAnyExpQ nm (the aexp)
         rP nm = (nm, show_cmm_n CMM_Reference) 

takeCInfo ::ConnectorInfo->String->String->(PCs_CMM_Ns, String, [String])
takeCInfo (After o) bnm _  = (CMM_AfterC, "AfterC_" ++ bnm, (if o then "o" else "c"):[])
takeCInfo Op bnm tgt   = (CMM_BranchC, "C" ++ bnm ++ "_" ++ tgt, [])
takeCInfo (OpIfB g) bnm _= (CMM_BMainIfC, (show_cmm_n CMM_BMainIfC) ++ bnm, maybeToLs g)
takeCInfo OpElse bnm _   = (CMM_BElseC, (show_cmm_n CMM_BElseC) ++ bnm, [])
takeCInfo OpJump bnm _   = (CMM_BJumpC, (show_cmm_n CMM_BJumpC) ++ bnm, [])
takeCInfo (Ref ps h) bnm _ = (CMM_ReferenceC, "C"++ bnm, (if h then "h" else "v"):ps)

getConnectorsInfo::Foldable t=>t Connector ->Rel String String->Rel String String->Rel String String
   ->Rel String String->QuadURel String
getConnectorsInfo cs ns_m es_m src_m tgt_m = 
   let eNmS nm = "E" ++ nm ++ "Src" in
   let eNmT nm = "E" ++ nm ++ "Tgt" in
   let etNmS ty = "E" ++ (show_cmm_n ty) ++ "Src" in
   let etNmT ty = "E" ++ (show_cmm_n ty) ++ "Tgt" in
   let oty ty = if ty `elem` [CMM_BElseC, CMM_BJumpC, CMM_BMainIfC] then CMM_BranchC else ty in
   let consConn nm ty src tgt = qur (singles (nm, show_cmm_n ty), set [(eNmS nm, etNmS $ oty ty), (eNmT nm, etNmT $ oty ty)], set [(eNmS nm, nm), (eNmT nm, nm)], set [(eNmS nm,src), (eNmT nm,tgt)]) in
   let cons (Connector cty src tgt) = let (ty, nm, ps) = takeCInfo cty src tgt in let q = consConn nm ty src tgt in q `join` (consOther nm ty ps) in
   foldr (\c cs'-> (cons c) `join` cs') (qur (ns_m, es_m, src_m, tgt_m)) cs 
   where mkGNm nm g =  nm ++ "_guard_"++g
         consOther nm CMM_BMainIfC [g] = singleQUR ((mkGNm nm g, show_cmm_n CMM_Guard), ("E"++nm++"_g", show_cmm_e CMM_EHasGuard), ("E"++nm++"_g", nm), ("E"++nm++"_g", mkGNm nm g))
         consOther nm CMM_ReferenceC ps = consRCHQ nm (head ps) `join` consHasPs nm (tail ps)
         consOther nm CMM_AfterC ps = let ov = if head ps == "o" then "YesV" else "NoV" in singleQURFrSndTrpl ((eac_co nm, show_cmm_e CMM_EAfterC_copen), (eac_co nm, nm), (eac_co nm, ov))
         consOther _ _ _ =  nilQUR
         consRCHQ nm h = let hv = if h == "h" then "YesV" else "NoV" in singleQURFrSndTrpl (("E"++nm++"_hidden", show_cmm_e CMM_EReferenceC_hidden), ("E"++nm++"_hidden", nm), ("E"++nm++"_hidden", hv))
         --consForRefC nm [] = ([], [], [], [])
         --consForRefC nm (p:ps) = ([(mkPNm nm p, show_cmm_n CMM_Parameter)], [(mkEPNm nm p, show_cmm_e CMM_EHasParams)], [(mkEPNm nm p, nm)], [(mkEPNm nm p, mkPNm nm p)]) `combineQAsConcat` (consForRefC nm ps)
         eac_co nm = "E"++nm++"_copen"

--consOtherEdges :: String -> [NodeDef] -> [EdgeDef] -> [a]
consOtherEdges::Eq b=> SGr String b -> String ->String->Rel String String ->Rel String String->Rel String String->Rel String String->(Rel String String, Rel String String, Rel String String)
consOtherEdges sg_mm nm start ns_t es_m src_m tgt_m = 
   let ess = (set [("EPCSt", "EStarts"), ("EStCSrc_", show_cmm_e CMM_EStartSrc), ("EStCTgt_", show_cmm_e CMM_EStartTgt)], 
             set [("EPCSt", nm), ("EStCSrc_", "StartC_"), ("EStCTgt_",  "StartC_")], 
             set [("EPCSt", "StartN_"), ("EStCSrc_",  "StartN_"), ("EStCTgt_", start)]) in
   let (x, y, z) `combine` (x', y', z') = (x `union` x', y `union` y', z `union` z') in 
   let mkEdgeNm n = "EContains" ++ n in
   let typesOf n = let nt = appl ns_t n in img (inhst sg_mm) [nt] in 
   let mkETy n = let ts = typesOf n in if "Node" `elem` ts then (show_cmm_e CMM_EContainsNs) else if (show_cmm_n CMM_Connector) `elem` ts then (show_cmm_e CMM_EContainsCs) else "" in
   let combineWith n ct (es_m, src_m, tgt_m) = let e = mkEdgeNm n in ((e, ct) `intoSet` es_m, (e, nm) `intoSet` src_m, (e, n) `intoSet` tgt_m) in
   let mkTupleAndCombine n es_i = let ct = mkETy n in if null ct then es_i else combineWith n ct es_i in
   let es_cs = foldl (\es n->mkTupleAndCombine (fst n) es) (nil, nil, nil) ns_t in
   (es_m, src_m, tgt_m) `combine` (ess `combine` es_cs) --`combine` es_ops))

consPCAndTyMorph :: SGr String String -> PCDef -> GrwT String String
consPCAndTyMorph sg_mm (PCDef nm start elems) = 
   -- initial set of nodes with the mapping
   let ns_m_i = set [(nm, "PCDef"), ("StartN_", show_cmm_n CMM_StartN), ("StartC_", show_cmm_n CMM_StartC)] in 
   let (ns_m, es_m, src_m, tgt_m) = quadQUR $ (mkEnmQ "StartN_" "StartN_") `join` getNodesInfo (getTheNodes elems) in
   let (ns_m_c, es_c, src_m_c, tgt_m_c) = quadQUR $ getConnectorsInfo (getTheCs elems) (ns_m_i `union` ns_m) es_m src_m tgt_m in
   let (es_m_f, src_m_f, tgt_m_f) = consOtherEdges sg_mm nm start ns_m_c es_c src_m_c tgt_m_c in
   let pcg = consG (dom_of ns_m_c) (dom_of es_m_f) src_m_f tgt_m_f in
   --let pcg = cons_g (map fst ns_m_c) (map fst es_m) [] [] in
   consGWT pcg (consGM (ns_m_c) es_m_f)

is_wf_pcdef :: PCDef -> Bool
is_wf_pcdef (PCDef _ start elems) = start `elem` (map (\(Node nm _)->nm) (getTheNodes elems))


loadPC'::SGr String String->PCDef->IO (GrwT String String)
loadPC' sg_mm pc = do
   let b = is_wf_pcdef pc
   let pc_g = if b then consPCAndTyMorph sg_mm pc else Gr_Cls.empty
   unless b $ do putStrLn "The PC is not well-formed."
   return pc_g

loadPC :: SGr String String -> FilePath -> IO (Maybe(GrwT String String))
loadPC sg_mm fn = do
   opc <- loadPCFrFile fn
   if isNil opc
      then do
         putStrLn "The PC definition could not be parsed."
         return Nothing
      else do
         Just <$> loadPC' sg_mm (the opc)

process_pc_def :: FilePath -> IO ()
process_pc_def fn = do
   pc<-loadPCFrFile fn
   putStrLn $ show pc

tb_pc_def :: String
tb_pc_def = "PC PC_HouseAttacker@HouseAttacker\n"
   ++ "compound HouseAttacker.ges,mes,ses@someoneEnters\n"
   ++ "atom someoneEnters<:ges>\n"
 
def_path :: String
def_path = "PCs/Examples/"

test1 :: [(PCDef, String)]
test1 = readP_to_S pc_def tb_pc_def
test2 :: IO ()
test2 = process_pc_def (def_path ++ "PC_CashMachine.pc")
test3 :: IO ()
test3 = process_pc_def (def_path ++ "PC_CashMachineOps.pc")
test4a :: [([String], String)]
test4a = readP_to_S (pcParams '.') ".abc1,abc2@"
test4b :: [([String], String)]
test4b = readP_to_S (pcParams '.') ".x@"
test5 :: [(Node, String)]
test5 = readP_to_S pc_atom "atom someoneEnters<:ges>\n"

test6a :: [(Node, String)]
test6a = readP_to_S pcReference "reference RefTimer:Timer.3[timeout/mute]"
test6b :: [(Node, String)]
test6b = readP_to_S pcReference "reference RefTimer"

test7a :: [(Connector, String)]
test7a = readP_to_S pc_referenceC "ref_connector RefHouseAttacker->HouseAttacker.bes,mes,ses"
test7b :: [(Connector, String)]
test7b = readP_to_S pc_referenceC "ref_connector RefJarOpenedTake->JarOpened.n-1,m"
test7c :: [(Connector, String)]
test7c = readP_to_S pc_referenceC "ref_connector RefHouseAlarm0->HouseAlarm0.False,False"
test7d :: [(Connector, String)]
test7d = readP_to_S pc_referenceC "ref_connector RefGetandGive->GetandGive.0"
test7e :: [(Connector, String)]
test7e = readP_to_S pc_referenceC "ref_connector RefTimer->PC_Timer"

test8 :: [(Connector, String)]
test8 = readP_to_S pcAfterC "after_connector open a->b"

test9 :: [(Connector, String)]
test9 = readP_to_S pc_opBG "op_connector_g OpAuthenticate->OpAuthenticateChoice{n>0}\n"

test10a :: [(Node, String)]
test10a = readP_to_S pcCompound "compound GetandGive.x@OpGetandGive"
test10b :: [(Node, String)]
test10b = readP_to_S pcCompound "compound Clock@tick"
test10c :: [(Node, String)]
test10c = readP_to_S pcCompound "compound JarOpened.n,m@OpJarOpenedIf"

test11 :: [(Node, String)]
test11 = readP_to_S pc_atom "atom timeout{t==0}\n"
test12 = readP_to_S pc_atom "atom someoneMoves<:eas>{active and (not triggered)}\n"
test13 = readP_to_S pc_atom "atom grab<:{grabLaptop,grabJewels}>\n"
test14 :: [(Node, String)]
test14 = readP_to_S pc_operator "operator OpCashMachine2.OpThrow:cancel,deny\n"



--test9 = loadPC get_sg_pcs_mm def_path "../pcs/PC_SimpleLife.pc"