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
import PCs.MM_Names
import SimpleFuns ( nilQl )
import ParsingCommon
   ( parseId
   , parseIds
   , parseMaybe
   , parse_until_chs
   , parseTokens
   , parseWord
   , parseAnyStr
   , satisfyWLook)
import Gr_Cls
import SimpleFuns
   ( replace
   , replaceAll
   )
import QUR
import PCs.Common ( OpKind(..), toMMOp )
import PCs.TxtExpAST (leadingId)
import PCs.ParsingTxtExp

-- A node has a name a type and possibly an associated operator
-- A reference may be inner
type TxtExp = String
type Guard = Maybe TxtExp 
type Name = String
--data TxtExp = BSet [ExpVal] | BVal ExpVal
--   deriving(Eq, Show, Read)
data PCType = Event | Integer | Boolean | Dt Name | SetT PCType
   deriving(Eq, Show, Read) 
data NodeDetails = 
   Atom (Maybe Name) TxtExp Guard 
   | Process String [(Name, Maybe PCType)] 
   | Operator OpKind [TxtExp] 
   | Reference Bool String Guard [TxtExp] [(String,String)]
   | QuantifiedOp OpKind Name TxtExp Guard
   | Stop
   | Skip 
   | Import (Maybe Name) (Maybe Name)
   deriving(Eq, Show) 

data Node = Node String NodeDetails 
   deriving(Eq, Show)
-- A ref connector may have parameters and be hidden or not; an op connector may have a guard 
data ConnectorInfo = 
   After Bool 
   | Ref [TxtExp] Bool 
   | Op 
   | OpIfB Guard 
   | OpElse 
   | OpJump 
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
getTy (Process {}) = CMM_Process
getTy (Operator {}) = CMM_Combination
getTy (Reference {}) = CMM_Reference
getTy Stop = CMM_Stop
getTy Skip = CMM_Skip
getTy (Import {}) = CMM_Import

frPCTypeToMM::PCType->PCs_CMM_Ns
frPCTypeToMM Event = CMM_Event 
frPCTypeToMM Integer = CMM_Integer
frPCTypeToMM Boolean = CMM_Boolean
frPCTypeToMM (Dt _)   = CMM_Custom
frPCTypeToMM (SetT _) = CMM_Set

show_t::PCType->String
show_t (Dt id)  = "Dt_" ++ id
show_t (SetT t) = "Set_" ++ show_t t
show_t t        = show t

--toPCTypeFrMMCustom::String->PCType
--toPCTypeFrMMCustom id = Dt id 
--toPCTypeFrMM CMM_Event Nothing Nothing = Event
--toPCTypeFrMM CMM_Integer Nothing Nothing = Integer
--toPCTypeFrMM CMM_Boolean Nothing Nothing = Boolean
--toPCTypeFrMM CMM_Set Nothing (Just t) = SetT t

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

parseIdTy::ReadP PCType
parseIdTy = parseId >>= (\id->skipSpaces >> return (Dt id))

parseInt::ReadP PCType
parseInt = string "Int" >> skipSpaces >> return Integer

parseBool::ReadP PCType
parseBool = string "Bool" >> skipSpaces >> return Boolean

parseEvent::ReadP PCType
parseEvent = string "Event" >> skipSpaces >> return Event

parseSet::ReadP PCType
parseSet = 
   string "set" >> skipSpaces >> parsePCType0 >>= return . SetT

parsePCType0::ReadP PCType
parsePCType0 = parseInt <|> parseBool <|> parseEvent <|> parseIdTy <|> parseSet

parsePCType::ReadP (Maybe PCType)
parsePCType = 
   (char ':' >> parsePCType0 >>= return . Just) <++ return Nothing

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

--parseSingleExp::ReadP TxtExp
--parseSingleExp = do
--   char '\''
--   b<-parseAnyStr "'" 
--   char '\''
--   return . BVal $ b

--parseSetExp::ReadP TxtExp
--parseSetExp = do
--   char '{'
--   bs<-parseTokens "," (parseAnyStr "},")
--   char '}'
--   return . BSet $ bs

parseTxtExp::Char->Char->ReadP TxtExp
parseTxtExp l r = between (char l) (char r)  (parseAnyStr (r:""))

parseTxtExp'::ReadP TxtExp
parseTxtExp' = parseTxtExp '\'' '\''

--   parseSetExp <|> parseSingleExp

pcExps::Char->ReadP [TxtExp]
pcExps ch = do
   char ch
   parseTokens "," (parseTxtExp '\'' '\'')

pcProcess :: ReadP Node
pcProcess = do
   string "process"
   skipSpaces
   cnm<-parse_until_chs "@."
   ps<- pcParams '.' <++ return []
   char '@'
   start<-parseWord 
   skipSpaces
   return (Node cnm $ Process start ps)

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
   e<-parseTxtExp '\'' '\''
   skipSpaces
   g<-pc_guard
   skipSpaces
   return (Node nm $ QuantifiedOp op v e g)

pc_atom_atSet:: ReadP TxtExp
pc_atom_atSet = 
   char ':' >> parseTxtExp '\'' '\''

pc_atom_rnm :: ReadP (Maybe String)
pc_atom_rnm = do
   string "->"
   skipSpaces 
   Just <$> parseId

pc_guard0 :: ReadP (Maybe String)
pc_guard0 = do
   g<-parseTxtExp '{' '}'
   return (Just g)

pc_guard :: ReadP (Maybe String)
pc_guard = do
   g<-pc_guard0 <++ return Nothing
   return g

pcAtom :: ReadP Node
pcAtom = do
   string "atom"
   skipSpaces
   anm<-parseId <++ return ""
   skipSpaces
   char ':'
   skipSpaces
   e<- parseTxtExp '\'' '\'' 
   anm<-if (null anm) then do
         return $ leadingId . parse $ e
      else 
         return anm 
   skipSpaces
   rnm<-pc_atom_rnm <++ return Nothing
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
   nm1<-parseId
   skipSpaces
   as<-string "as" <++ return "">>=(\s->return $ s == "as")
   skipSpaces
   nid<-if as then do 
      fmap Just parseId
   else 
      return Nothing
   skipSpaces
   for<-string "for" <++ return "">>=(\s->return $ s == "for")
   skipSpaces
   nm_for<-if for then do
            fmap Just parseId
         else do
            return Nothing
   skipSpaces
   let (nid', fn) = if isNil nid then (nm1, Nothing) else (the nid, Just nm1)
   return (Node nid' $ Import fn nm_for)

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
   ElemN <$> (pcProcess <|> pcAtom <|> pcOperator <|> pcReference <|> pcStop <|> pcSkip <|> pcImport <|> pcQuantifiedOp)

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
   ts<-sepBy1 (parseTxtExp '\'' '\'') (skipSpaces>>satisfy (== ',') >> skipSpaces)
   skipSpaces
   return (ElemD $ DefEnum id ts)

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

--combineQAsConcat :: ([a1], [a2], [a3], [a4]) -> ([a1], [a2], [a3], [a4]) -> ([a1], [a2], [a3], [a4])
--combineQAsConcat (x, y, z, w) (x', y', z', w') = (x++x', y++y', z++z', w++w')
combineQAsUnion :: (Eq a1, Eq a2, Eq a3, Eq a4) => (Set a1, Set a2, Set a3, Set a4) -> (Set a1, Set a2, Set a3, Set a4) -> (Set a1, Set a2, Set a3, Set a4)
combineQAsUnion (x, y, z, w) (x', y', z', w') = (x `union` x', y `union` y', z `union` z', w `union` w')
-- combineQAsInsert (x, y, z, w) (x', y', z', w') = (insert x x', insert y y', insert z z', insert w w')
combineQwUnionOfFst::Eq a=>Set a->(Set a, b, c, d) ->(Set a, b, c, d)
combineQwUnionOfFst x (x', y', z', w') = (x `union` x', y', z', w')
--combineQAsUnionLs qs = foldr (\q qs->q `combineQAsUnion` qs) nilQl qs

-- constructs name of parameter
mkParamNm::String->String->Int->String
mkParamNm nm p k = nm ++ "_param_"++ show k ++ "_" ++ p

mkTxtExpNm::String->String->String
mkTxtExpNm nm e = nm ++ "_txtExp_" ++ e

mkTxtExpNm_k::String->String->Int->String
mkTxtExpNm_k nm e k = nm ++ "_txtExp_" ++ (show k) ++ "_" ++ e

-- builds edge names for parameters
mkEPNm :: String -> String ->String
mkEPNm nm p = "EParam" ++ nm ++ "_" ++ p 

mkETxtExpNm :: String -> Int->String
mkETxtExpNm nm k = "ETxtExp_" ++ nm ++ "_" ++ (show k)

mkEExpVal :: String -> String ->Int->Int->String
mkEExpVal nm b k j= "EExpVal_" ++ nm ++ "_" ++ b++ "_" ++ (show k) ++ "_" ++ (show j) 

-- Constructs a name
cNm :: String -> String
cNm nm = nm ++ "_"

qurName ::String-> String -> QuadURel String
qurName enm nm = 
   let eNm enm = "ENmOf"++enm in
   singleQUR ((cNm nm, show_cmm_n CMM_Name),
      (eNm enm, show_cmm_e CMM_Ename), 
      (eNm enm, enm), 
      (eNm enm, cNm nm))

qurPCName ::String->String-> QuadURel String
qurPCName nm nnm = 
   let enm = "EPCNmOf"++nm in
   singleQUR ((cNm nnm, show_cmm_n CMM_Name), 
      (enm, show_cmm_e CMM_Epc_name), 
      (enm, nm), 
      (enm, cNm nnm))

qurIFName ::String->String-> QuadURel String
qurIFName nm fnm = 
   let enm = "EIFNmOf"++nm in
   singleQUR ((cNm fnm, show_cmm_n CMM_Name), 
      (enm, show_cmm_e CMM_Efname), 
      (enm, nm), 
      (enm, cNm fnm))

qurRefName ::String->String-> QuadURel String
qurRefName nm rn = 
   let enm = "ERNmOf"++nm in
   singleQUR ((cNm rn, show_cmm_n CMM_Name), 
      (enm, show_cmm_e CMM_EReference_name), 
      (enm, nm), 
      (enm, cNm rn))

-- builds node and edges for the definition connector of a process 
qurProcessConnection ::String ->String -> QuadURel String
qurProcessConnection nm st = 
   let cnNm = "Def" ++ nm in -- name of connector node
   let eSrcNm = "E" ++ cnNm ++ "Src" in
   let eTgtNm = "E" ++ cnNm ++ "Tgt" in
   qurOneTpl (singles (cnNm, show_cmm_n CMM_DefinesC)) 
      (set [(eSrcNm, show_cmm_e CMM_Esrc), (eTgtNm, show_cmm_e CMM_Etgt)], set [(eSrcNm, cnNm), (eTgtNm, cnNm)], 
         set [(eSrcNm, nm), (eTgtNm, st)])

--mkAEnnm :: String -> String
--mkAEnnm nm = nm ++ "_anyExp"

--mk_st_AnyExp :: String -> QuadURel String
--mk_st_AnyExp nm = singleQUR ((mkAEnnm nm, show_cmm_n CMM_AnyExp)
--   , (mkenm, show_cmm_e CMM_Eaexp)
--   , (mkenm, nm)
--   , (mkenm, mkAEnnm nm))
--    where mkenm = "EAE_"++nm

--expValNm::String->String->Int->Int->String
--expValNm nm b k j = "EV_" ++ nm ++ "_" ++ b ++  "_" ++ (show k) ++ "_" ++ (show j)

--qurValExpQ::String->String->Int->Int->PCs_CMM_Es->QuadURel String
--qurValExpQ nm b k j et = singleQUR ((expValNm nm b k j, show_cmm_n CMM_ValueExp),
--    (mkEExpVal nm b k j, show_cmm_e et),
--    (mkEExpVal nm b k j, mkTxtExpNm nm k),
--    (mkEExpVal nm b k j, expValNm nm b k j))

--qurTxtExp::String->String->Int->PCs_CMM_Ns->PCs_CMM_Es->QuadURel String
--qurTxtExp nm b k bty e_ty_ps = 
--   singleQUR ((mkTxtExpNm nm, show_cmm_n bty),
--      (mkETxtExpNm nm b k, show_cmm_e e_ty_ps),
--      (mkETxtExpNm nm b k, nm), (mkETxtExpNm nm b k, mkTxtExpNm nm k))
    --where tnm = if nty == CMM_AnyExp then mkAEnnm nm else nm

--qurExpSingle ::String ->String->Int->PCs_CMM_Es->QuadURel String
--qurExpSingle nm b k e_ty_ps = 
--    qurTxtExp nm b k CMM_ExpSingle e_ty_ps `join` qurValExpQ nm b k 1 CMM_EvExp
--
--    qur (set [(mkBindingNm nm k, show_cmm_n CMM_BindingSingle), (bvalNm b j, show_cmm_n CMM_BValue)], 
--      set [(mkEBindingNm nm b, show_cmm_e e_ty_ps), (mkEBindingVal nm b j, show_cmm_e CMM_Eval)], 
--      set [(mkEBindingNm nm b, tnm), (mkEBindingVal nm b j, mkBindingNm nm k)], 
--      set [(mkEBindingNm nm b, mkBindingNm nm k), (mkEBindingVal nm b j, bvalNm b j)])
--    where tnm = if nty == CMM_AnyExp then mkAEnnm nm else nm

--qurFrTxtExps ::String ->[String]->Int->Int->PCs_CMM_Es->QuadURel String
--qurFrTxtExps _ [] _ _ _ = nilQUR
--qurFrTxtExps nm (b:bs) k j e_ty_ps = 
--   qurTxtExp nm b k CMM_ExpSet e_ty_ps `join` qurValExpQ nm b k j CMM_EvExps
--   `join` qurFrTxtExps nm bs k (j+1) e_ty_ps
--   where tnm = if nty == CMM_AnyExp then mkAEnnm nm else nm

--qurTxtExps::String->[TxtExp]->PCs_CMM_Es->QuadURel String
--qurTxtExps nm es e_ty = foldr(\(e, k) qs->qurTextExp nm e k CMM_Eexps `join` qs) nilQUR (zip es [1..length es])

qurTxtExp::String->String->QuadURel String
qurTxtExp nm e = singleQUR ((mkTxtExpNm nm e, show_cmm_n CMM_TxtExp),
      (mkETxtExpNm nm 1, show_cmm_e CMM_Eexp),
      (mkETxtExpNm nm 1, nm), (mkETxtExpNm nm 1, mkTxtExpNm nm e))

qurTxtExp_k::String->String->Int->QuadURel String
qurTxtExp_k nm e k = singleQUR ((mkTxtExpNm_k nm e k, show_cmm_n CMM_TxtExp),
      (mkETxtExpNm nm k, show_cmm_e CMM_Eexps),
      (mkETxtExpNm nm k, nm), (mkETxtExpNm nm k, mkTxtExpNm_k nm e k))

qurTxtExps::String->[String]->QuadURel String
qurTxtExps nm es = foldr(\(e, k) qs-> qs `join` qurTxtExp_k nm e k) nilQUR (zip es [1..length es])

qurRenamingNames ::String->String->String-> QuadURel String
qurRenamingNames nm fr to = 
   let nm' = mk_ren_nm nm fr to
       nm1 = cNm (nm' ++ "_" ++ fr ++ "_new")
       nm2 = cNm (nm' ++ "_" ++ to ++ "_old")
       enm1 = "ERenNewNmOf"++nm1 
       enm2 = "ERenOldNmOf"++nm2 in
   qur (set [(nm1, show_cmm_n CMM_Name), (nm2, show_cmm_n CMM_Name)],
      set [(enm1, show_cmm_e CMM_ERenaming_new), (enm2, show_cmm_e CMM_ERenaming_old)],
      set [(enm1, nm),  (enm2, nm)],
      set [(enm1, nm1), (enm2, nm2)])

mk_ren_nm ::String->String->String->String
mk_ren_nm nm fr to = nm ++ "_renaming_"++fr++"_"++to

mk_e_Ren::String->String->String ->String
mk_e_Ren nm fr to  = "ERen"++nm++"_"++fr++"_"++to

qurRenaming::String->String->String->QuadURel String
qurRenaming nm fr to = 
   let nm' = mk_ren_nm nm fr to in
      qurRenamingNames nm' fr to `join`
      singleQUR ((nm', show_cmm_n CMM_Renaming)
         , (mk_e_Ren nm fr to, show_cmm_e CMM_ERenamings)
         , (mk_e_Ren nm fr to, nm)
         , (mk_e_Ren nm fr to, nm'))

mkHasParamQ::String->String->Int->QuadURel String
mkHasParamQ nm p k = 
   singleQUR ((mkParamNm nm p k, show_cmm_n CMM_Parameter)
      , (mkEPNm nm p, show_cmm_e CMM_Eparams)
      , (mkEPNm nm p, nm)
      , (mkEPNm nm p, mkParamNm nm p k))

--qurParamSetTy::String->PCType->QuadURel String -- The set of is missing. // Work here
--qurParamSetTy nm t = 
--   let eTyNm = "E_" ++ nm ++ "_setof" in
--   singleQUR ((show t, show_cmm_n . frPCTypeToMM $ t)
--      , (eTyNm, show_cmm_e CMM_EsetOf)
--      , (eTyNm, nm)
--      , (eTyNm, show t))

qurParamTy0::String->PCType->QuadURel String 
qurParamTy0 nm t = 
   let eTyNm = "E_" ++ nm ++ "_ty" in
   singleQUR ((show_t $ t, show_cmm_n . frPCTypeToMM $ t)
      , (eTyNm, show_cmm_e CMM_Etype)
      , (eTyNm, nm)
      , (eTyNm, show_t t))
qurParamTy::String->PCType->QuadURel String 
qurParamTy nm st@(SetT t) = 
   let tnm = show_t st
       eSoNm = "E_" ++ tnm ++ "_setof" in 
   singleQUR ((tnm, show_cmm_n . frPCTypeToMM $ st)
            , (eSoNm, show_cmm_e CMM_EsetOf)
            , (eSoNm, tnm)
            , (eSoNm, show_t $ t)) `join` qurParamTy0 nm st
qurParamTy nm t = qurParamTy0 nm t

qurParams :: String -> [(Name, Maybe PCType)] -> QuadURel String
qurParams nm ps = 
   let enmQ pnm k = qurName (mkParamNm nm pnm k) pnm 
       tyQ pnm k t = if isNil t then nilQUR else qurParamTy (mkParamNm nm pnm k) (the t) in
   foldr (\((pnm, pty), k) qs->enmQ pnm k `join` mkHasParamQ nm pnm k `join` tyQ pnm k pty `join` qs) nilQUR (zip ps [1..length ps])

--consExps :: String -> [TxtExp] -> QuadURel String
--consExps nm bs = 
--   foldr (\(b, k) qs->qurTextExp nm b k CMM_Eexps `join` qs) nilQUR (zip bs [1..length bs])

qurGuard :: String -> Maybe String -> QuadURel String
qurGuard nm Nothing = nilQUR
qurGuard nm (Just g) =
   let gnm =  nm ++ "_guard_" ++ g in
   singleQUR ((gnm, show_cmm_n CMM_TxtExp), 
      ("E"++nm++"_g", show_cmm_e CMM_Eguard), 
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
qurNode (Node nm (Process start ps)) _ = 
   qurName nm nm 
   `join` qurNodeNTy nm CMM_Process 
   `join` qurProcessConnection nm start 
   `join` qurParams nm ps
qurNode (Node nm (Operator op bs)) ns = 
   let q1 = qurOp nm op CMM_ECombination_op
       q2 = if nmOfOp op `elem` ns then nilQUR else singleQURFrFst (nmOfOp op, nodeOfOp op)
       qbs = qurTxtExps nm bs in
   gJoin [qurNodeNTy nm CMM_Combination, q1, q2, qbs]
qurNode (Node nm (Reference i rn g bs rs)) _ = 
   let qurRNm = gJoin [qurNodeNTy nm CMM_Reference, qurRefName nm rn]
       consQ = (qurTxtExps nm bs) `join` qurRNm  
       consRIQ = 
         let iv = if i then "YesV" else "NoV" in singleQURFrSndTrpl (("E"++nm++"_inner", show_cmm_e CMM_EReference_inner), ("E"++nm++"_inner", nm), ("E"++nm++"_inner", iv)) 
       consRs = foldr (\(fr, to) rqs->(qurRenaming nm fr to) `join` rqs) nilQUR rs in
   gJoin [if null rn then qurNodeNTy nm CMM_Reference else consQ, qurGuard nm g, consRs, consRIQ]
qurNode (Node nm (Atom rnm e g)) _ = 
   gJoin [qurName nm $ if isNil rnm then nm else the rnm, qurGuard nm g, qurNodeNTy nm CMM_Atom
         , if null e then nilQUR else qurTxtExp nm e]
qurNode (Node nm1 (Import fn nm2)) _ = 
   gJoin [qurName nm1 nm1, if isNil fn then nilQUR else qurIFName nm1 (the fn), 
         if isNil nm2 then nilQUR else qurPCName nm1 (the nm2), qurNodeNTy nm1 CMM_Import]
qurNode (Node nm (QuantifiedOp op v e g)) _ = 
   let eNm e = "EVar_"++e
       qv = singleQUR ((cNm v, show_cmm_n CMM_Name), (eNm v, show_cmm_e CMM_Evar), (eNm v, nm), (eNm v, cNm v)) in
   gJoin [qurNodeNTy nm CMM_Quantification, qurName nm nm, qv, 
      qurTxtExp nm e, qurOp nm op CMM_EopOfQuantifiedOp, qurGuard nm g]
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
--         consForC nm start = (mkEnmQUR nm nm) `join` (singleQURFrFst (nm, show_cmm_n CMM_Compound) `join` mkConnForCompound nm start)
--         mkQURForRNm nm rn = singleQUR ((cNm rn, show_cmm_n CMM_Name), ("ERNmOf"++nm, show_cmm_e CMM_EReference_name), ("ERNmOf"++nm, nm), ("ERNmOf"++nm, cNm rn))
--         consRIQ nm i = let iv = if i then "YesV" else "NoV" in qurOneTpl nil (singles ("E"++nm++"_inner", show_cmm_e CMM_EReference_inner), singles ("E"++nm++"_inner", nm), singles ("E"++nm++"_inner", iv))
--         consForRef nm rn bs rs = foldr(\(b, k) qs->mk_BindingQ nm b k CMM_Ebindings CMM_Binding `join` qs) ((mkQURForRNm nm rn) `join` (singleQURFrFst $ rP nm)) (zip bs [1..length bs]) 
--         consForOp_ nm op ns = let p = (nm, show_cmm_n CMM_Combination) in if (nmOfOp op) `elem` ns then mkQ nm op (singles p) else mkQ nm op (p `intoSet` singles (mkOpP op))
--         consForOp nm op bs ns = foldr(\(b, k) qs-> qs `join` mk_BindingQ nm b k CMM_Ebindings CMM_Binding) (consForOp_ nm op ns) (zip bs [1..length bs]) 
--         atNm nm rnm = if isNil rnm then nm else the rnm
--         atPs nm aexp = if isNil aexp then nilQUR else mkAnyExpQ nm (the aexp)
--         rP nm = (nm, show_cmm_n CMM_Reference) 

takeCInfo ::ConnectorInfo->String->String->(PCs_CMM_Ns, String, [TxtExp])
takeCInfo (After o) bnm _  = (CMM_AfterC, "AfterC_" ++ bnm, [if o then "o" else "c"])
takeCInfo Op bnm tgt       = (CMM_BranchC, "C" ++ bnm ++ "_" ++ tgt, [])
takeCInfo (OpIfB g) bnm _  = (CMM_BMainIfC, (show_cmm_n CMM_BMainIfC) ++ bnm, maybeToLs g)
takeCInfo OpElse bnm _     = (CMM_BElseC, (show_cmm_n CMM_BElseC) ++ bnm, [])
takeCInfo OpJump bnm _     = (CMM_BJumpC, (show_cmm_n CMM_BJumpC) ++ bnm, [])
takeCInfo (Ref bs h) bnm _ = (CMM_ReferenceC, "C"++ bnm, (if h then "h" else "v"):bs)

qurConnectors::Foldable t=>t Connector ->QuadURel String
qurConnectors cs  = 
   let eNmS nm = "E" ++ nm ++ "Src" 
       eNmT nm = "E" ++ nm ++ "Tgt" 
       oty ty = if ty `elem` [CMM_BElseC, CMM_BJumpC, CMM_BMainIfC] then CMM_BranchC else ty 
       consConn nm ty src tgt = 
         qur (singles (nm, show_cmm_n ty), 
            set [(eNmS nm, show_cmm_e CMM_Esrc), (eNmT nm, show_cmm_e CMM_Etgt)], 
            set [(eNmS nm, nm), (eNmT nm, nm)], set [(eNmS nm,src), (eNmT nm,tgt)]) 
       cons (Connector cty src tgt) = 
         let (ty, nm, bs) = takeCInfo cty src tgt in let q = consConn nm ty src tgt in q `join` (consOther nm ty bs) in
   foldr (\c qur->cons c `join` qur) nilQUR cs 
   where consOther nm CMM_BMainIfC g = qurGuard nm (toMaybeFrLs g)
         consOther nm CMM_ReferenceC bs = consRCHQ nm (head bs) `join` qurTxtExps nm (tail bs)
         consOther nm CMM_AfterC bs = let ov = if (head bs) == "o" then "YesV" else "NoV" in singleQURFrSndTrpl ((eac_co nm, show_cmm_e CMM_EAfterC_copen), (eac_co nm, nm), (eac_co nm, ov))
         consOther _ _ _ =  nilQUR
         consRCHQ nm h = let hv = if h == "h" then "YesV" else "NoV" in singleQURFrSndTrpl (("E"++nm++"_hidden", show_cmm_e CMM_EReferenceC_hidden), ("E"++nm++"_hidden", nm), ("E"++nm++"_hidden", hv))
         --consForRefC nm [] = ([], [], [], [])
         --consForRefC nm (p:ps) = ([(mkPNm nm p, show_cmm_n CMM_Parameter)], [(mkEPNm nm p, show_cmm_e CMM_EHasParams)], [(mkEPNm nm p, nm)], [(mkEPNm nm p, mkPNm nm p)]) `combineQAsConcat` (consForRefC nm ps)
         eac_co nm = "E"++nm++"_copen"
         --val (BVal v) = v

qurEnumTerms::String->[String]->QuadURel String
qurEnumTerms nm ts = 
   let eNM k = "E" ++ nm ++ "_" ++ (show k)
       tNm k = "EnumTerm_" ++ nm ++ "_" ++ (show k)
       cons_e k = singleQURFrSndTrpl ((eNM k, show_cmm_e CMM_Eterms), (eNM k, nm), (eNM k, tNm k))
       cons k t = singleQURFrFst (tNm k, show_cmm_n CMM_EnumTerm) `join` cons_e k `join` qurTxtExp (tNm k) t in
   foldr (\(t, k) qur->cons k t `join` qur) nilQUR (zip ts [1..(length ts)])

qurCustom::String->String->QuadURel String
qurCustom tnm dnm =
   let eNm = "E" ++ dnm ++ "_type" in
   singleQUR 
      ( (tnm, show_cmm_n CMM_Custom)
      , (eNm, show_cmm_e CMM_Etype)
      , (eNm, dnm)
      , (eNm, tnm))

qurDefinition::Definition ->QuadURel String
qurDefinition (DefEnum nm ls) = 
   let enum_nm = "Enum_" ++ nm 
       --cty_nm = "CTy_" ++ nm 
       cty_nm = "Dt_" ++ nm in
   (qurName enum_nm nm) -- name for enumeration
   `join` (qurName cty_nm nm) -- name for custom type
   `join` singleQURFrFst (enum_nm, show_cmm_n CMM_EnumType) -- Node for enumeration
   `join` qurCustom cty_nm enum_nm -- Node for custom type and relation to definition
   `join` qurEnumTerms enum_nm ls -- values of enumeration

qurDefs::Foldable t=>t Definition ->QuadURel String
qurDefs = foldr (\d qur->qurDefinition d `join` qur) nilQUR
   
--consOtherEdges :: String -> [NodeDef] -> [EdgeDef] -> [a]
consOtherEdges::Eq b=> SGr String b -> String ->String->Rel String String ->QuadURel String
consOtherEdges sg_mm nm start ns_t = 
   let ess = (set [("EPCSt", show_cmm_e CMM_EStarts), ("EStCSrc_", show_cmm_e CMM_Esrc), ("EStCTgt_", show_cmm_e CMM_Etgt)], 
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
       qur1 = ns_m_i_q `join` qurName nm nm `join` qurName "StartN_" "StartN_" `join` qurNodes (getENodes elems)
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

test4a :: [(TxtExp, String)]
test4a = readP_to_S parseTxtExp' "'diff(ges, {e})'"
test4b :: [(TxtExp, String)]
test4b = readP_to_S parseTxtExp' "'a>0'"

test5a :: [(Node, String)]
test5a = readP_to_S pcQuantifiedOp "quantifiedOp bop.Choice e:'ges'"
test5b :: [(Node, String)]
test5b = readP_to_S pcQuantifiedOp "quantifiedOp someoneMoves.Choice e :'eas' {active and (not triggered)}"
test5c :: [(Node, String)]
test5c = readP_to_S pcQuantifiedOp "quantifiedOp grab.Choice e :{grabLaptop,grabJewels}"

test5d :: [(Node, String)]
test5d = readP_to_S pcQuantifiedOp "quantifiedOp stealO.IntChoice x : 'Stealable'"
test5e :: [(Node, String)]
test5e = readP_to_S pcQuantifiedOp "quantifiedOp BreakIn.IntChoice x : 'MeansBreakIn'"

test5d' = qurNode (fst . head $ test5d) []
   --let n = head  . (readP_to_S pcAtomPack "atomPack stealO.IntChoice x : 'Stealable' @ 'steal.x'") in
  -- qurNode n

test6a :: [(Node, String)]
test6a = readP_to_S pcAtom "atom :'someoneEnters'"
test6b :: [(Node, String)]
test6b = readP_to_S pcAtom "atom :'timeout'{t==0}"
test6c :: [(Node, String)]
test6c = readP_to_S pcAtom "atom :'steal.x'"
test6d = qurNode (fst . head $ test5c) []
test6e = readP_to_S pcAtom "atom :'steal.x.y'"
test6f = readP_to_S pcAtom "atom stopIt2:'stopIt'"
test6g :: [(Node, String)]
test6g = readP_to_S pcAtom "atom :'coin50p'{x≤100}"

test7a :: [(Node, String)]
test7a = readP_to_S pcReference "reference RefTimer:Timer.'3'[timeout/mute]"
test7b :: [(Node, String)]
test7b = readP_to_S pcReference "reference RefTimer"
test7c :: [(Node, String)]
test7c = readP_to_S pcReference "reference RefHouseUnderAttack:HouseUnderAttack"
test7d :: [(Node, String)]
test7d = readP_to_S pcReference "reference RefHouseAlarm:HouseAlarm.{intoHall},{mainDoor,roomWindow},{intoRoom,intoKitchen,intoLivingRoom,grabTV,grabJewels,grabLaptop}"
test7e :: [(Node, String)]
test7e = readP_to_S pcReference "reference RefIntoRoom:IntoRoom"

test8a :: [(Connector, String)]
test8a = readP_to_S pc_referenceC "ref_connector RefHouseAttacker->HouseAttacker.'bes','mes','ses'"
test8b :: [(Connector, String)]
test8b = readP_to_S pc_referenceC "ref_connector RefJarOpenedTake->JarOpened.'n-1','m'"
test8c :: [(Connector, String)]
test8c = readP_to_S pc_referenceC "ref_connector RefJarOpenedDrop->JarOpened.'n+1','m'"
test8d :: [(Connector, String)]
test8d = readP_to_S pc_referenceC "ref_connector RefHouseAlarm0->HouseAlarm0.'false','false'"
test8e :: [(Connector, String)]
test8e = readP_to_S pc_referenceC "ref_connector RefGetandGive->GetandGive.'0'"
test8f :: [(Connector, String)]
test8f = readP_to_S pc_referenceC "ref_connector RefTimer->PC_Timer"
test8g :: [(Connector, String)]
test8g = readP_to_S pc_referenceC "ref_connector hidden RefIntoHall->IntoHall"
test8h :: [(Connector, String)]
test8h = readP_to_S pc_referenceC "ref_connector RefSeizeControl2->SeizeControl.'diff(ges, {e})'"

test9a :: [([TxtExp], String)]
test9a = readP_to_S (pcExps '.') ".'n-1','m'"

test9b :: [([TxtExp], String)]
test9b = readP_to_S (pcExps '.') ".'n+1','m'"

test10 :: [(Connector, String)]
test10 = readP_to_S pcAfterC "after open a->b"

test11 :: [(Connector, String)]
test11 = readP_to_S pc_opBG "op_connector_g OpAuthenticate->OpAuthenticateChoice{n>0}\n"

test12a :: [(Node, String)]
test12a = readP_to_S pcProcess "process GetandGive.x@OpGetandGive"
test12b :: [(Node, String)]
test12b = readP_to_S pcProcess "process Clock@tick"
test12c :: [(Node, String)]
test12c = readP_to_S pcProcess "process JarOpened.n,m@OpJarOpenedIf"

test13a :: [(Node, String)]
test13a = readP_to_S pcOperator "operator OpCashMachine2.Throw:'cancel','deny'"
test13b :: [(Node, String)]
test13b = readP_to_S pcOperator "operator OpProtectedHouse.Parallel:'intoHall','mainDoor','roomWindow','intoRoom','intoKitchen','intoLivingRoom','grabTV','grabJewels','grabLaptop'"
test13c :: [(Node, String)]
test13c = readP_to_S pcOperator "operator OpStoppableTimer1.Throw:'arrete'"

test14a :: [(Elem, String)]
test14a = readP_to_S pcElem "enum Stealable : 'Laptop','TV','Other'"
test14b :: [(Elem, String)]
test14b = readP_to_S pcElem "enum Stealable : 'Laptop', 'TV', 'Other'"
test14c :: [(Elem, String)]
test14c = readP_to_S pcElem "enum Scores : 'Deuce', 'AdvantageA', 'AdvantageB', 'Num.int.int'"
--test9 = loadPC get_sg_pcs_mm def_path "../pcs/PC_SimpleLife.pc"

test15a :: [(Node, String)]
test15a = readP_to_S pcImport "import PC_StopTimer"

test15b :: [(Node, String)]
test15b = readP_to_S pcImport "import StopTimer as STI for PC_StopTimer"