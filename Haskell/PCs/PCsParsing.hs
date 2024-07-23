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
   , parseTokens
   , parseWord
   , parseAnyStr
   , satisfyWLook)
import Gr_Cls
import SimpleFuns
import QUR

-- A node has a name a type and possibly an associated operator
-- A reference may be inner
type Guard = Maybe String 
type Name = String
type ABinding = String
data Binding = BSet [ABinding] | BVal ABinding
   deriving(Eq, Show, Read)
data PCType = Event | Integer | Boolean | SetT PCType
   deriving(Eq, Show, Read) 
data OpKind = Choice | IntChoice | Interleave | Throw | If | Parallel
   deriving(Eq, Show, Read) 
data NodeInfo = Atom (Maybe String) (Maybe (Name, Binding)) Guard
              | Compound String [(Name, Maybe PCType)] 
              | Operator OpKind [Binding] 
              | Reference Bool String Guard [Binding] [(String,String)]
              | Stop
              | Skip 
              | Import 
   deriving(Eq, Show) 

data Node = Node String NodeInfo 
   deriving(Eq, Show)
-- A ref connector may have parameters and be hidden or not; an op connector may have a guard 
data ConnectorInfo = After Bool | Ref [Binding] Bool | Op | OpIfB Guard | OpElse | OpJump 
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


getTy::NodeInfo->PCs_CMM_Ns
getTy (Atom {}) = CMM_Atom
getTy (Compound {}) = CMM_Compound
getTy (Operator {}) = CMM_Combination
getTy (Reference {}) = CMM_Reference
getTy Stop = CMM_Stop
getTy Skip = CMM_Skip
getTy Import = CMM_Import

frPCTypeToMM::PCType->PCs_CMM_Ns
frPCTypeToMM Event = CMM_Event 
frPCTypeToMM Integer = CMM_Integer
frPCTypeToMM Boolean = CMM_Boolean
frPCTypeToMM (SetT _) = CMM_Set


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

--parseSet::ReadP String
--parseSet = do
--   char '{'
--   s<-parse_until_chs "}"
--   char '}'
--   return s

--parseParam::ReadP String
--parseParam = do
--   s<-(parseSet <|> (parseAnyStr ",["))
--   return s

parseInt::ReadP PCType
parseInt = string "int" >> skipSpaces >> return Integer

parseBool::ReadP PCType
parseBool = string "bool" >> skipSpaces >> return Boolean

parseEvent::ReadP PCType
parseEvent = string "event" >> skipSpaces >> return Event

parseSet::ReadP PCType
parseSet = string "set" >> skipSpaces >> parsePCType0 >>= return . SetT

parsePCType0::ReadP PCType
parsePCType0 = char ':' >> parseInt <|> parseBool <|> parseEvent <|> parseSet

parsePCType::ReadP (Maybe PCType)
parsePCType = 
   (parsePCType0 >>= return . Just) <++ return Nothing

parseParam::ReadP (Name, Maybe PCType)
parseParam = do
   nm <- parseWord
   skipSpaces
   oty <- parsePCType
   return (nm, oty)


pcParams::Char->ReadP [(Name, Maybe PCType)]
pcParams ch = do
   char ch
   parseTokens "," parseParam
   --parse_ls_ids ","

parseBindingSingle::ReadP Binding
parseBindingSingle = do
   char '\''
   b<-parseAnyStr "'" 
   char '\''
   return . BVal $ b

parseBindingSet::ReadP Binding
parseBindingSet = do
   char '{'
   bs<-parseTokens "," (parseAnyStr "},")
   char '}'
   return . BSet $ bs

parseBinding::ReadP Binding
parseBinding = parseBindingSet <|> parseBindingSingle

pcBindings::Char->ReadP [Binding]
pcBindings ch = do
   char ch
   parseTokens "," parseBinding
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

pc_atom_atSet:: ReadP Binding
pc_atom_atSet = 
   char ':' >> parseBinding

pc_atom_rnm :: ReadP (Maybe String)
pc_atom_rnm = do
   char '.' 
   s<-parseId
   return (Just s)

pc_atom_aexp :: ReadP (Name, Binding)
pc_atom_aexp = do
   char '<' 
   s1<-parseId <++ return ""
   skipSpaces
   s2<-pc_atom_atSet 
   skipSpaces
   char '>'
   return (s1, s2)

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
   rnm<-pc_atom_rnm <++ return Nothing
   skipSpaces 
   aexp<-(pc_atom_aexp >>= return . Just) <++ return Nothing
   skipSpaces 
   g<-pc_guard
   skipSpaces 
   return (Node anm $ Atom rnm aexp g)

pc_OpChoice :: ReadP OpKind
pc_OpChoice = do
   string "Choice"
   return Choice

pc_OpIntChoice :: ReadP OpKind
pc_OpIntChoice = do
   string "IntChoice"
   return IntChoice

pc_OpInterleave :: ReadP OpKind
pc_OpInterleave = do
   string "Interleave"
   return Interleave

pc_OpParallel :: ReadP OpKind
pc_OpParallel = do
   string "Parallel"
   return Parallel

pc_OpThrow :: ReadP OpKind
pc_OpThrow = do
   string "Throw"
   return Throw

pc_OpIf :: ReadP OpKind
pc_OpIf = do
   string "If"
   return If

pc_OpKind :: ReadP OpKind
pc_OpKind = 
   pc_OpChoice <|> pc_OpIntChoice <|> pc_OpInterleave <|> pc_OpParallel <|> pc_OpThrow <|> pc_OpIf
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
   skipSpaces
   bs<-(pcBindings ':')<++return []
   skipSpaces
   return (Node o_nm $ Operator op bs)

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

pcRefToP::ReadP (String, [Binding], [(String, String)])
pcRefToP = do
   char ':'
   rnm<-parseId
   bs<-pcBindings '.' <++ return []
   skipSpaces
   rs<- pcRenamings <++ return []
   return (rnm, bs, rs)


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
   (pnm, bs, rs)<-pcRefToP<++ return ("", [], []) 
   skipSpaces
   --ps<-pcParams '.' <++ return []
   --skipSpaces
   --let hp = if null ps then "" else head ps
   --let ps' = if null ps then [] else tail ps
   return (Node rnm $ Reference inner pnm g bs rs)

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
   skipSpaces
   bs<-(pcBindings '.') <++ return []
   skipSpaces
   return (Connector (Ref bs hidden) proxy ref)

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

--extractInfo :: NodeInfo -> (String, [String])
--extractInfo (Atom rnm aexp g) = (show_cmm_n CMM_Atom, (maybeToLs rnm)++(maybeToLs g)++(if isNil aexp then [] else (fst . the $ aexp):[snd . the $ aexp]))
--extractInfo (Compound _ _) = (show_cmm_n CMM_Compound, [])
--extractInfo (Reference rn ps _) = pair_up (show_cmm_n CMM_Reference) $ if null rn then [] else (rn:ps)
--extractInfo (Operator op bs) = (show_cmm_n CMM_Operator, bs)
--extractInfo Stop = (show_cmm_n CMM_Stop, [])
--extractInfo Skip = (show_cmm_n CMM_Skip, [])
--extractInfo Import = (show_cmm_n CMM_Import, [])

-- constructs name of parameter
mkParamNm::String->String->Int->String
mkParamNm nm p k = nm ++ "_param_"++ show k ++ "_" ++ p

mkBindingNm::String->Int->String
mkBindingNm nm k = nm ++ "_binding_"++ show k

-- builds parameters of edges
mkEPNm :: String -> String ->String
mkEPNm nm p = "EParam" ++ nm ++ "_" ++ p 

mkEBindingNm :: String -> String ->String
mkEBindingNm nm b = "EBinding" ++ nm ++ "_" ++ b

mkEBindingVal :: String -> String ->Int->Int->String
mkEBindingVal nm b k j= "EBVal_" ++ nm ++ "_" ++ b++ "_" ++ (show k) ++ "_" ++ (show j) 

-- Constructs a name
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
mk_st_AnyExp nm = singleQUR ((mkAEnnm nm, show_cmm_n CMM_AnyExp)
   , (mkenm, show_cmm_e CMM_Eaexp)
   , (mkenm, nm)
   , (mkenm, mkAEnnm nm))
    where mkenm = "EAE_"++nm

bvalNm::String->Int->Int->String
bvalNm b k j = "BV_" ++ b ++  "_" ++ (show k) ++ "_" ++ (show j)

mkBindingValQ::String->String->Int->Int->PCs_CMM_Es->QuadURel String
mkBindingValQ nm b k j et = singleQUR ((bvalNm b k j, show_cmm_n CMM_BValue),
    (mkEBindingVal nm b k j, show_cmm_e et),
    (mkEBindingVal nm b k j, mkBindingNm nm k),
    (mkEBindingVal nm b k j, bvalNm b k j))

mkBindingQ::String->String->Int->PCs_CMM_Ns->PCs_CMM_Es->PCs_CMM_Ns->QuadURel String
mkBindingQ nm b k bty e_ty_ps nty = singleQUR ((mkBindingNm nm k, show_cmm_n bty),
    (mkEBindingNm nm b, show_cmm_e e_ty_ps),
    (mkEBindingNm nm b, tnm),(mkEBindingNm nm b, mkBindingNm nm k))
    where tnm = if nty == CMM_AnyExp then mkAEnnm nm else nm

mk_QFrBindingVal ::String ->String->Int->PCs_CMM_Es->PCs_CMM_Ns->QuadURel String
mk_QFrBindingVal nm b k e_ty_ps nty = 
    mkBindingQ nm b k CMM_BindingSingle e_ty_ps nty `join` mkBindingValQ nm b k 1 CMM_Eval
--
--    qur (set [(mkBindingNm nm k, show_cmm_n CMM_BindingSingle), (bvalNm b j, show_cmm_n CMM_BValue)], 
--      set [(mkEBindingNm nm b, show_cmm_e e_ty_ps), (mkEBindingVal nm b j, show_cmm_e CMM_Eval)], 
--      set [(mkEBindingNm nm b, tnm), (mkEBindingVal nm b j, mkBindingNm nm k)], 
--      set [(mkEBindingNm nm b, mkBindingNm nm k), (mkEBindingVal nm b j, bvalNm b j)])
--    where tnm = if nty == CMM_AnyExp then mkAEnnm nm else nm

mk_QsFrBindingVals ::String ->[String]->Int->Int->PCs_CMM_Es->PCs_CMM_Ns->QuadURel String
mk_QsFrBindingVals _ [] _ _ _ _ = nilQUR
mk_QsFrBindingVals nm (b:bs) k j e_ty_ps nty = 
   mkBindingQ nm b k CMM_BindingSet e_ty_ps nty `join` mkBindingValQ nm b k j CMM_Evals
   `join` mk_QsFrBindingVals nm bs k (j+1) e_ty_ps nty
--   where tnm = if nty == CMM_AnyExp then mkAEnnm nm else nm

mk_BindingQ ::String ->Binding->Int->PCs_CMM_Es->PCs_CMM_Ns->QuadURel String
mk_BindingQ nm (BVal b) k e_ty_ps nty = mk_QFrBindingVal nm b k e_ty_ps nty
mk_BindingQ nm (BSet bs) k e_ty_ps nty = mk_QsFrBindingVals nm bs k 1 e_ty_ps nty
--   singleQUR ((mkBindingNm nm b k, show_cmm_n CMM_Binding), 
--      (mkEBindingNm nm b, show_cmm_e e_ty_ps), 
--      (mkEBindingNm nm b, tnm), 
--      (mkEBindingNm nm b, mkBindingNm nm b k))
--   where tnm = if nty == CMM_AnyExp then mkAEnnm nm else nm

mkAnyExpQ ::String->(Name, Binding)->QuadURel String
mkAnyExpQ nm (enm, ats) = 
   let eNm e = "EVar_"++e
       varQ v = singleQUR ((cNm v, show_cmm_n CMM_Name), (eNm v, show_cmm_e CMM_Evar), 
            (eNm v, mkAEnnm nm), (eNm v, cNm v))
       q = if null enm then nilQUR else varQ enm in
   (mk_st_AnyExp nm) `join` q `join` (mk_BindingQ nm ats 1 CMM_Eof CMM_AnyExp)

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
      , (mkEPNm nm p, show_cmm_e CMM_Eparams)
      , (mkEPNm nm p, nm)
      , (mkEPNm nm p, mkParamNm nm p k))

mkParamTyQ::String->PCType->QuadURel String
mkParamTyQ nm t = 
   let eTyNm = "E_" ++ nm ++ "_ty" in
   singleQUR ((show t, show_cmm_n . frPCTypeToMM $ t)
      , (eTyNm, show_cmm_e CMM_Etype)
      , (eTyNm, nm)
      , (eTyNm, show t))

--consHasPs :: String -> [String] -> QuadURel String
--consHasPs _ [] = nilQUR
--consHasPs nm (p:ps) = mkHasParamQ nm p `join` (consHasPs nm ps)

consParams :: String -> [(Name, Maybe PCType)] -> QuadURel String
consParams nm ps = 
   let enmQ pnm k = mkEnmQ (mkParamNm nm pnm k) pnm 
       tyQ pnm k t = if isNil t then nilQUR else mkParamTyQ (mkParamNm nm pnm k) (the t) in
   foldr (\((pnm, pty), k) qs->enmQ pnm k `join` mkHasParamQ nm pnm k `join` tyQ pnm k pty `join` qs) nilQUR (zip ps [1..length ps])

consBindings :: String -> [Binding] -> QuadURel String
consBindings nm bs = 
   foldr (\(b, k) qs->mk_BindingQ nm b k CMM_Ebindings CMM_Bindable `join` qs) nilQUR (zip bs [1..length bs])

mkGuardQ :: String -> Maybe String -> QuadURel String
mkGuardQ nm Nothing = nilQUR
mkGuardQ nm (Just g) =
   let gnm =  nm ++ "_guard_" ++ g in
   singleQUR ((gnm, show_cmm_n CMM_Guard), ("E"++nm++"_g", show_cmm_e CMM_Eguard), 
      ("E"++nm++"_g", nm), ("E"++nm++"_g", gnm))

nodeOfOp::OpKind->String
nodeOfOp Choice = show_cmm_n CMM_VOpChoice
nodeOfOp IntChoice = show_cmm_n CMM_VOpIntChoice
nodeOfOp Interleave = show_cmm_n CMM_VOpInterleave
nodeOfOp Throw = show_cmm_n CMM_VOpThrow
nodeOfOp If = show_cmm_n CMM_VOpIf
nodeOfOp Parallel = show_cmm_n CMM_VOpParallel

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
         cons (Node nm (Compound start ps)) _ = consForC nm start `join` consParams nm ps
         cons (Node nm (Operator op bs)) ns = consForOp nm op bs ns
         cons (Node nm (Reference i rn g bs rs)) _ = gJoin [(if null rn then singleQURFrFst $ rP nm else consForRef nm rn bs rs), mkGuardQ nm g, consRenamings nm rs, consRIQ nm i]
         cons (Node nm (Atom rnm aexp g)) _ = (mkEnmQ nm $ atNm nm rnm) `join` (gJoin [mkGuardQ nm g, atPs nm aexp, singleQURFrFst (nm, show_cmm_n CMM_Atom)])
         cons (Node nm Import) _ = let p = (nm, show_cmm_n CMM_Import) in (mkEnmQ nm nm) `join` singleQURFrFst p
         cons (Node nm ni) _ = singleQURFrFst (nm, show_cmm_n . getTy $ ni)
         consRenamings nm rs = foldr (\(fr, to) rqs->(mkRenamingQUR nm fr to) `join` rqs) nilQUR rs
         consForC nm start = (mkEnmQ nm nm) `join` (singleQURFrFst (nm, show_cmm_n CMM_Compound) `join` mkConnForCompound nm start)
         mkQURForRNm nm rn = singleQUR ((cNm rn, show_cmm_n CMM_Name), ("ERNmOf"++nm, show_cmm_e CMM_EReference_name), ("ERNmOf"++nm, nm), ("ERNmOf"++nm, cNm rn))
         consRIQ nm i = let iv = if i then "YesV" else "NoV" in qurOneTpl nil (singles ("E"++nm++"_inner", show_cmm_e CMM_EReference_inner), singles ("E"++nm++"_inner", nm), singles ("E"++nm++"_inner", iv))
         consForRef nm rn bs rs = foldr(\(b, k) qs->mk_BindingQ nm b k CMM_Ebindings CMM_Binding `join` qs) ((mkQURForRNm nm rn) `join` (singleQURFrFst $ rP nm)) (zip bs [1..length bs]) 
         consForOp_ nm op ns = let p = (nm, show_cmm_n CMM_Combination) in if (nmOfOp op) `elem` ns then mkQ nm op (singles p) else mkQ nm op (p `intoSet` singles (mkOpP op))
         consForOp nm op bs ns = foldr(\(b, k) qs-> qs `join` mk_BindingQ nm b k CMM_Ebindings CMM_Binding) (consForOp_ nm op ns) (zip bs [1..length bs]) 
         atNm nm rnm = if isNil rnm then nm else the rnm
         atPs nm aexp = if isNil aexp then nilQUR else mkAnyExpQ nm (the aexp)
         rP nm = (nm, show_cmm_n CMM_Reference) 

takeCInfo ::ConnectorInfo->String->String->(PCs_CMM_Ns, String, [Binding])
takeCInfo (After o) bnm _  = (CMM_AfterC, "AfterC_" ++ bnm, [BVal $ if o then "o" else "c"])
takeCInfo Op bnm tgt   = (CMM_BranchC, "C" ++ bnm ++ "_" ++ tgt, [])
takeCInfo (OpIfB g) bnm _= (CMM_BMainIfC, (show_cmm_n CMM_BMainIfC) ++ bnm, map BVal $ maybeToLs g)
takeCInfo OpElse bnm _   = (CMM_BElseC, (show_cmm_n CMM_BElseC) ++ bnm, [])
takeCInfo OpJump bnm _   = (CMM_BJumpC, (show_cmm_n CMM_BJumpC) ++ bnm, [])
takeCInfo (Ref bs h) bnm _ = (CMM_ReferenceC, "C"++ bnm, (BVal $ if h then "h" else "v"):bs)

getConnectorsInfo::Foldable t=>t Connector ->Rel String String->Rel String String->Rel String String
   ->Rel String String->QuadURel String
getConnectorsInfo cs ns_m es_m src_m tgt_m = 
   let eNmS nm = "E" ++ nm ++ "Src" in
   let eNmT nm = "E" ++ nm ++ "Tgt" in
   let etNmS ty = "E" ++ (show_cmm_n ty) ++ "Src" in
   let etNmT ty = "E" ++ (show_cmm_n ty) ++ "Tgt" in
   let oty ty = if ty `elem` [CMM_BElseC, CMM_BJumpC, CMM_BMainIfC] then CMM_BranchC else ty in
   let consConn nm ty src tgt = qur (singles (nm, show_cmm_n ty), set [(eNmS nm, etNmS $ oty ty), (eNmT nm, etNmT $ oty ty)], set [(eNmS nm, nm), (eNmT nm, nm)], set [(eNmS nm,src), (eNmT nm,tgt)]) in
   let cons (Connector cty src tgt) = let (ty, nm, bs) = takeCInfo cty src tgt in let q = consConn nm ty src tgt in q `join` (consOther nm ty bs) in
   foldr (\c cs'-> (cons c) `join` cs') (qur (ns_m, es_m, src_m, tgt_m)) cs 
   where mkGNm nm g =  nm ++ "_guard_"++g
         consOther nm CMM_BMainIfC [BVal g] = singleQUR ((mkGNm nm g, show_cmm_n CMM_Guard), ("E"++nm++"_g", show_cmm_e CMM_Eguard), ("E"++nm++"_g", nm), ("E"++nm++"_g", mkGNm nm g))
         consOther nm CMM_ReferenceC bs = consRCHQ nm (val . head $ bs) `join` consBindings nm (tail bs)
         consOther nm CMM_AfterC bs = let ov = if (val . head $ bs) == "o" then "YesV" else "NoV" in singleQURFrSndTrpl ((eac_co nm, show_cmm_e CMM_EAfterC_copen), (eac_co nm, nm), (eac_co nm, ov))
         consOther _ _ _ =  nilQUR
         consRCHQ nm h = let hv = if h == "h" then "YesV" else "NoV" in singleQURFrSndTrpl (("E"++nm++"_hidden", show_cmm_e CMM_EReferenceC_hidden), ("E"++nm++"_hidden", nm), ("E"++nm++"_hidden", hv))
         --consForRefC nm [] = ([], [], [], [])
         --consForRefC nm (p:ps) = ([(mkPNm nm p, show_cmm_n CMM_Parameter)], [(mkEPNm nm p, show_cmm_e CMM_EHasParams)], [(mkEPNm nm p, nm)], [(mkEPNm nm p, mkPNm nm p)]) `combineQAsConcat` (consForRefC nm ps)
         eac_co nm = "E"++nm++"_copen"
         val (BVal v) = v

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

test2a :: IO ()
test2a = process_pc_def (def_path ++ "PC_CashMachine.pc")

test2b :: IO ()
test2b = process_pc_def (def_path ++ "PC_CashMachineOps.pc")

--test3a :: [((Maybe Name, Binding), String)]
test3a :: [((Name, Binding), String)]
test3a = readP_to_S pc_atom_aexp "<e:ges>"

test4a :: [([(Name, Maybe PCType)], String)]
test4a = readP_to_S (pcParams '.') ".abc1,abc2@"
test4b :: [([(Name, Maybe PCType)], String)]
test4b = readP_to_S (pcParams '.') ".x@"
test4c :: [([Binding], String)]
test4c = readP_to_S (pcBindings '.') ".{intoHall},{mainDoor,roomWindow},{intoRoom,intoKitchen,intoLivingRoom,grabTV,grabJewels,grabLaptop}"
test4d :: [(Binding, String)]
test4d = readP_to_S parseBinding "'diff(ges, {e})'"

test5a :: [(Node, String)]
test5a = readP_to_S pc_atom "atom someoneEnters<:ges>"
test5b :: [(Node, String)]
test5b = readP_to_S pc_atom "atom timeout{t==0}"
test5c :: [(Node, String)]
test5c = readP_to_S pc_atom "atom someoneMoves<:eas>{active and (not triggered)}"
test5d :: [(Node, String)]
test5d = readP_to_S pc_atom "atom grab<:{grabLaptop,grabJewels}>"

test6a :: [(Node, String)]
test6a = readP_to_S pcReference "reference RefTimer:Timer.3[timeout/mute]"
test6b :: [(Node, String)]
test6b = readP_to_S pcReference "reference RefTimer"
test6c :: [(Node, String)]
test6c = readP_to_S pcReference "reference RefHouseUnderAttack:HouseUnderAttack"
test6d :: [(Node, String)]
test6d = readP_to_S pcReference "reference RefHouseAlarm:HouseAlarm.{intoHall},{mainDoor,roomWindow},{intoRoom,intoKitchen,intoLivingRoom,grabTV,grabJewels,grabLaptop}"
test6e :: [(Node, String)]
test6e = readP_to_S pcReference "reference RefIntoRoom:IntoRoom"

test7a :: [(Connector, String)]
test7a = readP_to_S pc_referenceC "ref_connector RefHouseAttacker->HouseAttacker.'bes','mes','ses'"
test7b :: [(Connector, String)]
test7b = readP_to_S pc_referenceC "ref_connector RefJarOpenedTake->JarOpened.'n-1','m'"
test7c :: [(Connector, String)]
test7c = readP_to_S pc_referenceC "ref_connector RefHouseAlarm0->HouseAlarm0.'False','False'"
test7d :: [(Connector, String)]
test7d = readP_to_S pc_referenceC "ref_connector RefGetandGive->GetandGive.'0'"
test7e :: [(Connector, String)]
test7e = readP_to_S pc_referenceC "ref_connector RefTimer->PC_Timer"
test7f :: [(Connector, String)]
test7f = readP_to_S pc_referenceC "ref_connector hidden RefIntoHall->IntoHall"
test7g :: [(Connector, String)]
test7g = readP_to_S pc_referenceC "ref_connector RefSeizeControl2->SeizeControl.'diff(ges, {e})'"

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

test11a :: [(Node, String)]
test11a = readP_to_S pc_operator "operator OpCashMachine2.Throw:'cancel','deny'"
test11b :: [(Node, String)]
test11b = readP_to_S pc_operator "operator OpProtectedHouse.Parallel:'intoHall','mainDoor','roomWindow','intoRoom','intoKitchen','intoLivingRoom','grabTV','grabJewels','grabLaptop'"
test11c :: [(Node, String)]
test11c = readP_to_S pc_operator "operator OpStoppableTimer1.Throw:'arrete'"

--test9 = loadPC get_sg_pcs_mm def_path "../pcs/PC_SimpleLife.pc"