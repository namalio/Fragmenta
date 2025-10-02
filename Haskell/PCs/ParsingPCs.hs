-----------------------------
-- Project: PCs/Fragmenta
-- Module: 'PCsParsing'
-- Description: Parses PC textual descriptions
-- Author: Nuno Amálio
-----------------------------
module PCs.ParsingPCs(loadPC) where

import Text.ParserCombinators.ReadP
import Control.Applicative ( Alternative((<|>)) )
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
   , parseIds
   , parseMaybe
   , parse_until_chs
   , parseTokens
   , parseWord
   , parseAnyStr
   , satisfyWLook)
import Gr_Cls
import SimpleFuns
import QUR
import PCs.PCsCommon ( OpKind(..), toMMOp )

-- A node has a name a type and possibly an associated operator
-- A reference may be inner
type Guard = Maybe String 
type Name = String
type ExpVal = String
data TxtExp = BSet [ExpVal] | BVal ExpVal
   deriving(Eq, Show, Read)
data PCType = Event | Integer | Boolean | SetT PCType
   deriving(Eq, Show, Read) 
data NodeDetails = Atom (Maybe Name) (Maybe TxtExp) Guard 
              | Compound String [(Name, Maybe PCType)] 
              | Operator OpKind [TxtExp] 
              | Reference Bool String Guard [TxtExp] [(String,String)]
              | QuantifiedOp OpKind Name TxtExp Guard
              | Stop
              | Skip 
              | Import 
   deriving(Eq, Show) 

data Node = Node String NodeDetails 
   deriving(Eq, Show)
-- A ref connector may have parameters and be hidden or not; an op connector may have a guard 
data ConnectorInfo = After Bool | Ref [TxtExp] Bool | Op | OpIfB Guard | OpElse | OpJump 
   deriving(Eq, Show) 
-- An connector has a name, a type and source and target nodes
data Connector = Connector ConnectorInfo Name Name 
   deriving(Eq, Show) 
-- A definition: An enumerated type has a name and a list of literals
data Definition = DefEnum Name [Name]
   deriving(Eq, Show) 
data Elem = ElemN Node | ElemC Connector | ElemD Definition
   deriving(Eq, Show) 
 -- A PC definition has a name, a start node, and list of elements
data PCDef = PCDef String String [Elem] 
   deriving(Eq, Show)

isNode :: Elem -> Bool
isNode (ElemN _) = True
isNode _ = False

isConnector :: Elem -> Bool
isConnector (ElemC _) = True
isConnector _ = False

isDefinition :: Elem -> Bool
isDefinition (ElemD _) = True
isDefinition _ = False

getN :: Elem -> Node
getN (ElemN n) = n

getC :: Elem -> Connector
getC (ElemC c) = c

getD :: Elem -> Definition
getD (ElemD d) = d

gDefName::Definition->Name
gDefName (DefEnum nm _) = nm

gDefLiterals::Definition->[Name]
gDefLiterals (DefEnum _ ls) = ls


getTy::NodeDetails->PCs_CMM_Ns
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

getElemsOfKind:: Foldable t => (Elem->Bool)->t Elem -> [Elem]
getElemsOfKind p = foldl (\es e-> if p e then e:es else es) []

getENodes :: Foldable t => t Elem -> [Node]
getENodes es = map getN $ getElemsOfKind isNode es

getECs :: Foldable t => t Elem -> [Connector]
getECs es = map getC $ getElemsOfKind isConnector es

getEDefs :: Foldable t => t Elem -> [Definition]
getEDefs es = map getD $ getElemsOfKind isDefinition es

--getTheCs :: Foldable t => t Elem -> [Connector]
--getTheCs = foldl (\es e-> if not . isNode $ e then (getC e):es else es) [] 

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
parseSet = 
   string "set" >> skipSpaces >> parsePCType0 >>= return . SetT

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

parseSingleExp::ReadP TxtExp
parseSingleExp = do
   char '\''
   b<-parseAnyStr "'" 
   char '\''
   return . BVal $ b

parseSetExp::ReadP TxtExp
parseSetExp = do
   char '{'
   bs<-parseTokens "," (parseAnyStr "},")
   char '}'
   return . BSet $ bs

parseTxtExp::ReadP TxtExp
parseTxtExp = parseSetExp <|> parseSingleExp

pcExps::Char->ReadP [TxtExp]
pcExps ch = do
   char ch
   parseTokens "," parseTxtExp
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

pcQuantifiedOp :: ReadP Node
pcQuantifiedOp = do
   string "quantifiedOp "
   skipSpaces
   nm<-parseId
   char '.'
   op <- pcOpChoice <|> pcOpIntChoice
   skipSpaces
   v<-parseId
   skipSpaces
   char ':' 
   skipSpaces
   e<-parseTxtExp
   skipSpaces
   g<-pc_guard
   skipSpaces
   return (Node nm $ QuantifiedOp op v e g)

--pcAtomPack :: ReadP Node
--pcAtomPack = do
--   string "atomPack " 
--   skipSpaces
--   nm<-parseId
--   char '.'
--   op <- pcOpChoice <|> pcOpIntChoice
--   skipSpaces
--   v<-parseId
--   skipSpaces
--   char ':' 
--   skipSpaces
--   b<-parseBinding
--   skipSpaces
--   g<-pc_guard
--   skipSpaces
--   char '@'
--   skipSpaces
--   be<-parseBinding
--   skipSpaces
--   return (Node nm $ AtomPack op v b g be)

pc_atom_atSet:: ReadP TxtExp
pc_atom_atSet = 
   char ':' >> parseTxtExp

pc_atom_rnm :: ReadP (Maybe String)
pc_atom_rnm = do
   string "->"
   skipSpaces 
   Just <$> parseId

pcAatomExp :: ReadP (Maybe TxtExp)
pcAatomExp = 
   char '.' >> parseTxtExp >>= return . Just

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

pcAtom :: ReadP Node
pcAtom = do
   string "atom"
   skipSpaces
   anm<-parseId
   skipSpaces 
   rnm<-pc_atom_rnm <++ return Nothing
   skipSpaces 
   e<- pcAatomExp <++ return Nothing
   skipSpaces 
   g<-pc_guard
   skipSpaces 
   return (Node anm $ Atom rnm e g)

pcOpChoice :: ReadP OpKind
pcOpChoice = string "Choice" >> return Choice

pcOpIntChoice :: ReadP OpKind
pcOpIntChoice = string "IntChoice" >> return IntChoice

pcOpInterleave :: ReadP OpKind
pcOpInterleave = string "Interleave" >> return Interleave

pcOpParallel :: ReadP OpKind
pcOpParallel = string "Parallel" >> return Parallel

pcOpThrow :: ReadP OpKind
pcOpThrow = string "Throw" >> return Throw

pcOpIf :: ReadP OpKind
pcOpIf = string "If" >> return If

pcOpKind :: ReadP OpKind
pcOpKind = 
   pcOpChoice <|> pcOpIntChoice <|> pcOpInterleave <|> pcOpParallel <|> pcOpThrow <|> pcOpIf
--   do
--   ops<-parseWord
--   let op = read ops
--   return op

pcOperator :: ReadP Node
pcOperator = do
   string "operator"
   skipSpaces
   o_nm<-parseId
   char '.'
   op<-pcOpKind
   skipSpaces
   bs<-(pcExps ':')<++return []
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

pcRefToP::ReadP (String, [TxtExp], [(String, String)])
pcRefToP = do
   char ':'
   rnm<-parseId
   bs<-pcExps '.' <++ return []
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

pcStop :: ReadP Node
pcStop = do
   string "stop"
   skipSpaces
   nm<-str_until_end_of_stm 
   skipSpaces
   return (Node nm Stop)

pcSkip :: ReadP Node
pcSkip = do
   string "skip"
   skipSpaces
   nm<-str_until_end_of_stm 
   skipSpaces
   return (Node nm Skip)

pcImport :: ReadP Node
pcImport = do
   string "import"
   skipSpaces
   nm<-str_until_end_of_stm
   skipSpaces
   return (Node nm Import)

pcAfterC :: ReadP Connector
pcAfterC  = do
   string "after"
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
   bs<-(pcExps '.') <++ return []
   skipSpaces
   return (Connector (Ref bs hidden) proxy ref)

pcElemN :: ReadP Elem
pcElemN = 
   ElemN <$> (pcCompound <|> pcAtom <|> pcOperator <|> pcReference <|> pcStop <|> pcSkip <|> pcImport <|> pcQuantifiedOp)

pcElemC :: ReadP Elem
pcElemC = 
   ElemC <$> (pcAfterC <|> pc_opB <|> pc_referenceC <|> pc_opBG <|> pc_opElseB <|> pc_opJumpB)
   --return (ElemC c)

pcEnumT::ReadP Elem
pcEnumT = do
   string "enum"
   skipSpaces
   id<-parseId
   skipSpaces
   char ':'
   skipSpaces
   ls<-parseIds ","
   skipSpaces
   return (ElemD $ DefEnum id ls)

pcElem :: ReadP Elem
pcElem  = pcElemN <|> pcElemC <|> pcEnumT


pcDef :: ReadP PCDef
pcDef = do
   (pcnm, start)<-pcStart
   es<-manyTill pcElem eof
   return (PCDef pcnm start es)

loadPCFrFile :: FilePath -> IO (Maybe PCDef)
loadPCFrFile fn = do   
    contents <- readFile fn
    --makes sure it is read
    let pc = parseMaybe pcDef contents
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

mkTxtExpNm::String->Int->String
mkTxtExpNm nm k = nm ++ "_txtExp_"++ show k

-- builds parameters of edges
mkEPNm :: String -> String ->String
mkEPNm nm p = "EParam" ++ nm ++ "_" ++ p 

mkETxtExpNm :: String -> String ->Int->String
mkETxtExpNm nm b k = "ETxtExp_" ++ nm ++ "_" ++ b ++ "_" ++ (show k)

mkEExpVal :: String -> String ->Int->Int->String
mkEExpVal nm b k j= "EExpVal_" ++ nm ++ "_" ++ b++ "_" ++ (show k) ++ "_" ++ (show j) 

-- Constructs a name
cNm :: String -> String
cNm nm = nm ++ "_"

qurName ::String-> String -> QuadURel String
qurName enm nm = 
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

--mkAEnnm :: String -> String
--mkAEnnm nm = nm ++ "_anyExp"

--mk_st_AnyExp :: String -> QuadURel String
--mk_st_AnyExp nm = singleQUR ((mkAEnnm nm, show_cmm_n CMM_AnyExp)
--   , (mkenm, show_cmm_e CMM_Eaexp)
--   , (mkenm, nm)
--   , (mkenm, mkAEnnm nm))
--    where mkenm = "EAE_"++nm

expValNm::String->Int->Int->String
expValNm b k j = "EV_" ++ b ++  "_" ++ (show k) ++ "_" ++ (show j)

qurValExpQ::String->String->Int->Int->PCs_CMM_Es->QuadURel String
qurValExpQ nm b k j et = singleQUR ((expValNm b k j, show_cmm_n CMM_ValueExp),
    (mkEExpVal nm b k j, show_cmm_e et),
    (mkEExpVal nm b k j, mkTxtExpNm nm k),
    (mkEExpVal nm b k j, expValNm b k j))

qurTxtExp::String->String->Int->PCs_CMM_Ns->PCs_CMM_Es->QuadURel String
qurTxtExp nm b k bty e_ty_ps = singleQUR ((mkTxtExpNm nm k, show_cmm_n bty),
    (mkETxtExpNm nm b k, show_cmm_e e_ty_ps),
    (mkETxtExpNm nm b k, nm), (mkETxtExpNm nm b k, mkTxtExpNm nm k))
    --where tnm = if nty == CMM_AnyExp then mkAEnnm nm else nm

qurExpSingle ::String ->String->Int->PCs_CMM_Es->QuadURel String
qurExpSingle nm b k e_ty_ps = 
    qurTxtExp nm b k CMM_ExpSingle e_ty_ps `join` qurValExpQ nm b k 1 CMM_EvExp
--
--    qur (set [(mkBindingNm nm k, show_cmm_n CMM_BindingSingle), (bvalNm b j, show_cmm_n CMM_BValue)], 
--      set [(mkEBindingNm nm b, show_cmm_e e_ty_ps), (mkEBindingVal nm b j, show_cmm_e CMM_Eval)], 
--      set [(mkEBindingNm nm b, tnm), (mkEBindingVal nm b j, mkBindingNm nm k)], 
--      set [(mkEBindingNm nm b, mkBindingNm nm k), (mkEBindingVal nm b j, bvalNm b j)])
--    where tnm = if nty == CMM_AnyExp then mkAEnnm nm else nm

qurFrTxtExps ::String ->[String]->Int->Int->PCs_CMM_Es->QuadURel String
qurFrTxtExps _ [] _ _ _ = nilQUR
qurFrTxtExps nm (b:bs) k j e_ty_ps = 
   qurTxtExp nm b k CMM_ExpSet e_ty_ps `join` qurValExpQ nm b k j CMM_EvExps
   `join` qurFrTxtExps nm bs k (j+1) e_ty_ps
--   where tnm = if nty == CMM_AnyExp then mkAEnnm nm else nm

qurTextExp ::String ->TxtExp->Int->PCs_CMM_Es->QuadURel String
qurTextExp nm (BVal b) k e_ty_ps = qurExpSingle nm b k e_ty_ps
qurTextExp nm (BSet bs) k e_ty_ps = qurFrTxtExps nm bs k 1 e_ty_ps
--   singleQUR ((mkBindingNm nm b k, show_cmm_n CMM_Binding), 
--      (mkEBindingNm nm b, show_cmm_e e_ty_ps), 
--      (mkEBindingNm nm b, tnm), 
--      (mkEBindingNm nm b, mkBindingNm nm b k))
--   where tnm = if nty == CMM_AnyExp then mkAEnnm nm else nm

--mkAnyExpQ ::String->(Name, BindingExp)->QuadURel String
--mkAnyExpQ nm (enm, ats) = 
--   let eNm e = "EVar_"++e
--       varQ v = singleQUR ((cNm v, show_cmm_n CMM_Name), (eNm v, show_cmm_e CMM_Evar), 
--            (eNm v, mkAEnnm nm), (eNm v, cNm v))
--       q = if null enm then nilQUR else varQ enm in
--   (mk_st_AnyExp nm) `join` q `join` (mk_BindingQ nm ats 1 CMM_Eof CMM_AnyExp)

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
   let enmQ pnm k = qurName (mkParamNm nm pnm k) pnm 
       tyQ pnm k t = if isNil t then nilQUR else mkParamTyQ (mkParamNm nm pnm k) (the t) in
   foldr (\((pnm, pty), k) qs->enmQ pnm k `join` mkHasParamQ nm pnm k `join` tyQ pnm k pty `join` qs) nilQUR (zip ps [1..length ps])

consExps :: String -> [TxtExp] -> QuadURel String
consExps nm bs = 
   foldr (\(b, k) qs->qurTextExp nm b k CMM_Eexps `join` qs) nilQUR (zip bs [1..length bs])

qurGuard :: String -> Maybe String -> QuadURel String
qurGuard nm Nothing = nilQUR
qurGuard nm (Just g) =
   let gnm =  nm ++ "_guard_" ++ g in
   singleQUR ((gnm, show_cmm_n CMM_Guard), ("E"++nm++"_g", show_cmm_e CMM_Eguard), 
      ("E"++nm++"_g", nm), ("E"++nm++"_g", gnm))

nodeOfOp::OpKind->String
nodeOfOp = show_cmm_n . toMMOp 

nmOfOp::OpKind->String
nmOfOp op = let op' = show op in op'++"_Val"

qurOp::String->OpKind->PCs_CMM_Es->QuadURel String
qurOp nm op ety = singleQUR ((nmOfOp op, nodeOfOp op), ("E"++nm++"_op", show_cmm_e ety), 
                             ("E"++nm++"_op", nm), ("E"++nm++"_op", nmOfOp op)) 

qurNodeNTy::String->PCs_CMM_Ns->QuadURel String
qurNodeNTy nm nty = singleQURFrFst (nm, show_cmm_n nty) 

qurNode::Foldable t=>Node->t String->QuadURel String
qurNode (Node nm (Compound start ps)) _ = 
   qurName nm nm `join` qurNodeNTy nm CMM_Compound `join` mkConnForCompound nm start `join` consParams nm ps
qurNode (Node nm (Operator op bs)) ns = 
   let q1 = qurOp nm op CMM_ECombination_op
       q2 = if nmOfOp op `elem` ns then nilQUR else singleQURFrFst (nmOfOp op, nodeOfOp op)
       qbs = foldr(\(b, k) qs-> qs `join` qurTextExp nm b k CMM_Eexps) nilQUR (zip bs [1..length bs]) in
   gJoin [qurNodeNTy nm CMM_Combination, q1, q2, qbs]
qurNode (Node nm (Reference i rn g bs rs)) _ = 
   let qurRNm = gJoin [qurNodeNTy nm CMM_Reference, qurNodeNTy (cNm rn) CMM_Name, singleQURFrSndTrpl (("ERNmOf"++nm, show_cmm_e CMM_EReference_name), ("ERNmOf"++nm, nm), ("ERNmOf"++nm, cNm rn))]
       consQ = foldr(\(b, k) qs->qurTextExp nm b k CMM_Eexps `join` qs) qurRNm  (zip bs [1..length bs]) 
       consRIQ = let iv = if i then "YesV" else "NoV" in singleQURFrSndTrpl (("E"++nm++"_inner", show_cmm_e CMM_EReference_inner), ("E"++nm++"_inner", nm), ("E"++nm++"_inner", iv)) 
       consRs = foldr (\(fr, to) rqs->(mkRenamingQUR nm fr to) `join` rqs) nilQUR rs in
   gJoin [if null rn then qurNodeNTy nm CMM_Reference else consQ, qurGuard nm g, consRs, consRIQ]
qurNode (Node nm (Atom rnm e g)) _ = 
   gJoin [qurName nm $ if isNil rnm then nm else the rnm, qurGuard nm g, qurNodeNTy nm CMM_Atom
         , if isNil e then nilQUR else qurTextExp nm (the e) 1 CMM_Eexps]
qurNode (Node nm Import) _ = gJoin [qurName nm nm, qurNodeNTy nm CMM_Import]
qurNode (Node nm (QuantifiedOp op v e g)) _ = 
   let eNm e = "EVar_"++e
       qv = singleQUR ((cNm v, show_cmm_n CMM_Name), (eNm v, show_cmm_e CMM_Evar), (eNm v, nm), (eNm v, cNm v)) in
   gJoin [qurNodeNTy nm CMM_QuantifiedOp, qurName nm nm, qv, 
      qurTextExp nm e 1 CMM_Eexps, qurOp nm op CMM_EopOfQuantifiedOp, qurGuard nm g]
qurNode (Node nm ni) _ = qurNodeNTy nm (getTy ni)

qurNodes ::Foldable t=>t Node -> QuadURel String
qurNodes ns = 
   let yesV = ("YesV", show_cmm_n CMM_VYes) 
       noV = ("NoV", show_cmm_n CMM_VNo) 
       yn_vals = yesV `intoSet` singles noV in
   foldl (\ns' n-> qurNode n (dom_of . fstQUR $ ns') `join` ns') (consQUR yn_vals nil nil nil) ns
--   where --cQ p = (singles p, nil, nil, nil)
--         mkOpP op = (nmOfOp op, nodeOfOp op)
--         mkQ nm op ns_m = qurOneTpl ns_m (singles ("E"++nm++"_op", show_cmm_e CMM_ECombination_op), singles ("E"++nm++"_op", nm), singles ("E"++nm++"_op", nmOfOp op))
--         cons (Node nm (Compound start ps)) _ = consForC nm start `join` consParams nm ps
--         cons (Node nm (Operator op bs)) ns = consForOp nm op bs ns
--         cons (Node nm (Reference i rn g bs rs)) _ = gJoin [(if null rn then singleQURFrFst $ rP nm else consForRef nm rn bs rs), mkGuardQ nm g, consRenamings nm rs, consRIQ nm i]
--         cons (Node nm (Atom rnm aexp g)) _ = (mkEnmQUR nm $ atNm nm rnm) `join` (gJoin [mkGuardQ nm g, atPs nm aexp, singleQURFrFst (nm, show_cmm_n CMM_Atom)])
--         cons (Node nm Import) _ = let p = (nm, show_cmm_n CMM_Import) in (mkEnmQUR nm nm) `join` singleQURFrFst p
--         cons (Node nm ni) _ = singleQURFrFst (nm, show_cmm_n . getTy $ ni)
--         consRenamings nm rs = foldr (\(fr, to) rqs->(mkRenamingQUR nm fr to) `join` rqs) nilQUR rs
         --consForC nm start = (mkEnmQUR nm nm) `join` (singleQURFrFst (nm, show_cmm_n CMM_Compound) `join` mkConnForCompound nm start)
--         mkQURForRNm nm rn = singleQUR ((cNm rn, show_cmm_n CMM_Name), ("ERNmOf"++nm, show_cmm_e CMM_EReference_name), ("ERNmOf"++nm, nm), ("ERNmOf"++nm, cNm rn))
--         consRIQ nm i = let iv = if i then "YesV" else "NoV" in qurOneTpl nil (singles ("E"++nm++"_inner", show_cmm_e CMM_EReference_inner), singles ("E"++nm++"_inner", nm), singles ("E"++nm++"_inner", iv))
--         consForRef nm rn bs rs = foldr(\(b, k) qs->mk_BindingQ nm b k CMM_Ebindings CMM_Binding `join` qs) ((mkQURForRNm nm rn) `join` (singleQURFrFst $ rP nm)) (zip bs [1..length bs]) 
--         consForOp_ nm op ns = let p = (nm, show_cmm_n CMM_Combination) in if (nmOfOp op) `elem` ns then mkQ nm op (singles p) else mkQ nm op (p `intoSet` singles (mkOpP op))
--         consForOp nm op bs ns = foldr(\(b, k) qs-> qs `join` mk_BindingQ nm b k CMM_Ebindings CMM_Binding) (consForOp_ nm op ns) (zip bs [1..length bs]) 
--         atNm nm rnm = if isNil rnm then nm else the rnm
--         atPs nm aexp = if isNil aexp then nilQUR else mkAnyExpQ nm (the aexp)
--         rP nm = (nm, show_cmm_n CMM_Reference) 

takeCInfo ::ConnectorInfo->String->String->(PCs_CMM_Ns, String, [TxtExp])
takeCInfo (After o) bnm _  = (CMM_AfterC, "AfterC_" ++ bnm, [BVal $ if o then "o" else "c"])
takeCInfo Op bnm tgt   = (CMM_BranchC, "C" ++ bnm ++ "_" ++ tgt, [])
takeCInfo (OpIfB g) bnm _= (CMM_BMainIfC, (show_cmm_n CMM_BMainIfC) ++ bnm, map BVal $ maybeToLs g)
takeCInfo OpElse bnm _   = (CMM_BElseC, (show_cmm_n CMM_BElseC) ++ bnm, [])
takeCInfo OpJump bnm _   = (CMM_BJumpC, (show_cmm_n CMM_BJumpC) ++ bnm, [])
takeCInfo (Ref bs h) bnm _ = (CMM_ReferenceC, "C"++ bnm, (BVal $ if h then "h" else "v"):bs)

qurConnectors::Foldable t=>t Connector ->QuadURel String
qurConnectors cs  = 
   let eNmS nm = "E" ++ nm ++ "Src" 
       eNmT nm = "E" ++ nm ++ "Tgt" 
       etNmS ty = "E" ++ show_cmm_n ty ++ "Src" 
       etNmT ty = "E" ++ show_cmm_n ty ++ "Tgt" 
       oty ty = if ty `elem` [CMM_BElseC, CMM_BJumpC, CMM_BMainIfC] then CMM_BranchC else ty 
       consConn nm ty src tgt = qur (singles (nm, show_cmm_n ty), set [(eNmS nm, etNmS $ oty ty), (eNmT nm, etNmT $ oty ty)], set [(eNmS nm, nm), (eNmT nm, nm)], set [(eNmS nm,src), (eNmT nm,tgt)]) 
       cons (Connector cty src tgt) = let (ty, nm, bs) = takeCInfo cty src tgt in let q = consConn nm ty src tgt in q `join` (consOther nm ty bs) in
   foldr (\c qur->cons c `join` qur) nilQUR cs 
   where mkGNm nm g =  nm ++ "_guard_"++g
         consOther nm CMM_BMainIfC [BVal g] = singleQUR ((mkGNm nm g, show_cmm_n CMM_Guard), ("E"++nm++"_g", show_cmm_e CMM_Eguard), ("E"++nm++"_g", nm), ("E"++nm++"_g", mkGNm nm g))
         consOther nm CMM_ReferenceC bs = consRCHQ nm (val . head $ bs) `join` consExps nm (tail bs)
         consOther nm CMM_AfterC bs = let ov = if (val . head $ bs) == "o" then "YesV" else "NoV" in singleQURFrSndTrpl ((eac_co nm, show_cmm_e CMM_EAfterC_copen), (eac_co nm, nm), (eac_co nm, ov))
         consOther _ _ _ =  nilQUR
         consRCHQ nm h = let hv = if h == "h" then "YesV" else "NoV" in singleQURFrSndTrpl (("E"++nm++"_hidden", show_cmm_e CMM_EReferenceC_hidden), ("E"++nm++"_hidden", nm), ("E"++nm++"_hidden", hv))
         --consForRefC nm [] = ([], [], [], [])
         --consForRefC nm (p:ps) = ([(mkPNm nm p, show_cmm_n CMM_Parameter)], [(mkEPNm nm p, show_cmm_e CMM_EHasParams)], [(mkEPNm nm p, nm)], [(mkEPNm nm p, mkPNm nm p)]) `combineQAsConcat` (consForRefC nm ps)
         eac_co nm = "E"++nm++"_copen"
         val (BVal v) = v

qurEnumVals::String->[String]->QuadURel String
qurEnumVals nm ls = 
   let eNM s = "E" ++ nm ++ "_" ++ s
       cons_e s = singleQURFrSndTrpl ((eNM s, show_cmm_e CMM_EenumVals), (eNM s, nm), (eNM s, s))
       cons s = qurName s s `join` singleQURFrFst (s, show_cmm_n CMM_EnumVal) `join` cons_e s in
   foldr (\s qur->cons s `join` qur) nilQUR ls

qurDef::Definition ->QuadURel String
qurDef (DefEnum nm ls) = 
   (qurName nm nm) `join` singleQURFrFst (nm, show_cmm_n CMM_EnumType) `join` qurEnumVals nm ls

qurDefs::Foldable t=>t Definition ->QuadURel String
qurDefs = foldr (\d qur->qurDef d `join` qur) nilQUR
   
--consOtherEdges :: String -> [NodeDef] -> [EdgeDef] -> [a]
consOtherEdges::Eq b=> SGr String b -> String ->String->Rel String String ->QuadURel String
consOtherEdges sg_mm nm start ns_t = 
   let ess = (set [("EPCSt", "EStarts"), ("EStCSrc_", show_cmm_e CMM_EStartSrc), ("EStCTgt_", show_cmm_e CMM_EStartTgt)], 
             set [("EPCSt", nm), ("EStCSrc_", "StartC_"), ("EStCTgt_",  "StartC_")], 
             set [("EPCSt", "StartN_"), ("EStCSrc_",  "StartN_"), ("EStCTgt_", start)]) 
       (x, y, z) `combine` (x', y', z') = (x `union` x', y `union` y', z `union` z') 
       mkEdgeNm n = "EContains" ++ n 
       combineWith n ct (es_m, src_m, tgt_m) = let e = mkEdgeNm n in ((e, ct) `intoSet` es_m, (e, nm) `intoSet` src_m, (e, n) `intoSet` tgt_m)
       mkTupleAndCombine n es_i = let ct = mkETy n in if null ct then es_i else combineWith n ct es_i
       es_cs = foldl (\es n->mkTupleAndCombine (fst n) es) (nil, nil, nil) ns_t 
       mkQUR (x, y, z) = consQUR nil x y z in
   mkQUR (ess `combine` es_cs) --`combine` es_ops))
       where mkETy n
                | (show_cmm_n CMM_Node) `elem` (typesOf n) = show_cmm_e CMM_EContainsNs
                | (show_cmm_n CMM_Connector) `elem` (typesOf n) = show_cmm_e CMM_EContainsCs
                | (show_cmm_n CMM_Definition) `elem` (typesOf n) = show_cmm_e CMM_EContainsDs
                | otherwise = ""
             typesOf n = let nt = appl ns_t n in img (inhst sg_mm) [nt] 

consPCAsGrwT :: SGr String String -> PCDef -> GrwT String String
consPCAsGrwT sg_mm (PCDef nm start elems) = 
   -- initial set of nodes with the mapping
   let ns_m_i_q = consQUR (set [(nm, "PCDef"), ("StartN_", show_cmm_n CMM_StartN), ("StartC_", show_cmm_n CMM_StartC)]) nil nil nil
       --(ns_m, es_m, src_m, tgt_m) 
       qur1 = ns_m_i_q `join` qurName "StartN_" "StartN_" `join` qurNodes (getENodes elems)
       cs = getECs elems
       ds = getEDefs elems
       qur2 = qur1 `join` qurConnectors cs `join` qurDefs ds
       (ns_m, es_m, src_m, tgt_m) = quad $ qur2 `join` consOtherEdges sg_mm nm start (fstQUR qur2)
       pcg = consG (dom_of ns_m) (dom_of es_m) src_m tgt_m in
   consGWT pcg (consGM ns_m es_m)

is_wf_pcdef :: PCDef -> Bool
is_wf_pcdef (PCDef _ start elems) = 
   start `elem` (map (\(Node nm _)->nm) (getENodes elems))

loadPC'::SGr String String->PCDef->IO (GrwT String String)
loadPC' sg_mm pc = do
   let b = is_wf_pcdef pc
   let pc_g = if b then consPCAsGrwT sg_mm pc else Gr_Cls.empty
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
tb_pc_def = "PC PC_BreakStealHouse2@BreakAndStealHouse\n"
   ++ "enum Stealable : Laptop,TV,Other\n"
   ++ "compound BreakAndStealHouse@GetInside\n"
 
def_path :: String
def_path = "PCs/Examples/"

test1 :: [(PCDef, String)]
test1 = readP_to_S pcDef tb_pc_def

test2a :: IO ()
test2a = process_pc_def (def_path ++ "PC_CashMachine.pc")

test2b :: IO ()
test2b = process_pc_def (def_path ++ "PC_CashMachineOps.pc")

test3a :: [([(Name, Maybe PCType)], String)]
test3a = readP_to_S (pcParams '.') ".abc1,abc2@"
test3b :: [([(Name, Maybe PCType)], String)]
test3b = readP_to_S (pcParams '.') ".x@"
test3c :: [([TxtExp], String)]
test3c = readP_to_S (pcExps '.') ".{intoHall},{mainDoor,roomWindow},{intoRoom,intoKitchen,intoLivingRoom,grabTV,grabJewels,grabLaptop}"
test3d :: [(TxtExp, String)]
test3d = readP_to_S parseTxtExp "'diff(ges, {e})'"

test4a :: [(Node, String)]
test4a = readP_to_S pcQuantifiedOp "quantifiedOp bop.Choice e:'ges'"
test4b :: [(Node, String)]
test4b = readP_to_S pcQuantifiedOp "quantifiedOp someoneMoves.Choice e :'eas' {active and (not triggered)}"
test4c :: [(Node, String)]
test4c = readP_to_S pcQuantifiedOp "quantifiedOp grab.Choice e :{grabLaptop,grabJewels}"

test4d :: [(Node, String)]
test4d = readP_to_S pcQuantifiedOp "quantifiedOp stealO.IntChoice x : 'Stealable'"
test4e :: [(Node, String)]
test4e = readP_to_S pcQuantifiedOp "quantifiedOp BreakIn.IntChoice x : 'MeansBreakIn'"

test4d' = qurNode (fst . head $ test4d) []
   --let n = head  . (readP_to_S pcAtomPack "atomPack stealO.IntChoice x : 'Stealable' @ 'steal.x'") in
  -- qurNode n

test5a :: [(Node, String)]
test5a = readP_to_S pcAtom "atom someoneEnters"
test5b :: [(Node, String)]
test5b = readP_to_S pcAtom "atom timeout{t==0}"
test5c :: [(Node, String)]
test5c = readP_to_S pcAtom "atom steal.'x'"
test5d = qurNode (fst . head $ test5c) []


test6a :: [(Node, String)]
test6a = readP_to_S pcReference "reference RefTimer:Timer.'3'[timeout/mute]"
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
test7c = readP_to_S pc_referenceC "ref_connector RefHouseAlarm0->HouseAlarm0.'false','false'"
test7d :: [(Connector, String)]
test7d = readP_to_S pc_referenceC "ref_connector RefGetandGive->GetandGive.'0'"
test7e :: [(Connector, String)]
test7e = readP_to_S pc_referenceC "ref_connector RefTimer->PC_Timer"
test7f :: [(Connector, String)]
test7f = readP_to_S pc_referenceC "ref_connector hidden RefIntoHall->IntoHall"
test7g :: [(Connector, String)]
test7g = readP_to_S pc_referenceC "ref_connector RefSeizeControl2->SeizeControl.'diff(ges, {e})'"

test8 :: [(Connector, String)]
test8 = readP_to_S pcAfterC "after open a->b"

test9 :: [(Connector, String)]
test9 = readP_to_S pc_opBG "op_connector_g OpAuthenticate->OpAuthenticateChoice{n>0}\n"

test10a :: [(Node, String)]
test10a = readP_to_S pcCompound "compound GetandGive.x@OpGetandGive"
test10b :: [(Node, String)]
test10b = readP_to_S pcCompound "compound Clock@tick"
test10c :: [(Node, String)]
test10c = readP_to_S pcCompound "compound JarOpened.n,m@OpJarOpenedIf"

test11a :: [(Node, String)]
test11a = readP_to_S pcOperator "operator OpCashMachine2.Throw:'cancel','deny'"
test11b :: [(Node, String)]
test11b = readP_to_S pcOperator "operator OpProtectedHouse.Parallel:'intoHall','mainDoor','roomWindow','intoRoom','intoKitchen','intoLivingRoom','grabTV','grabJewels','grabLaptop'"
test11c :: [(Node, String)]
test11c = readP_to_S pcOperator "operator OpStoppableTimer1.Throw:'arrete'"

test12a :: [(Elem, String)]
test12a = readP_to_S pcElem "enum Stealable : Laptop,TV,Other"
--test9 = loadPC get_sg_pcs_mm def_path "../pcs/PC_SimpleLife.pc"