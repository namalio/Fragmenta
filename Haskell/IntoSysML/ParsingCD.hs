---------------------------------------
-- Project: Fragmenta
-- Module: 'ParsingCD'
-- Description: Parses SysML configuration diagrams (a subset of SysML internal block diagrams) 
-- textual descriptions to produce a graph with extra typing
-- Author: Nuno Amálio
---------------------------------------
module IntoSysML.ParsingCD(loadCD) where

import Text.ParserCombinators.ReadP
import Control.Applicative ( Alternative((<|>)) )
import Gr_Cls
import Grs
import SGrs
import Sets
import Relations
import TheNil
import MyMaybe
import IntoSysML.IntoSysML_CD_MM_Names
import ParsingCommon
import ParseUtils
import IntoSysML.ASDCommon
import SimpleFuns
import FrParsingToWET
import GrswET 
import Control.Monad(when)
import IntoSysML.ASCD

-- getStates desc = foldr (\e es-> if isState e then (getSt e):es else es) [] (gElems desc)
-- getTransitions desc = foldr (\e es-> if isTransition e then (getT e):es else es) [] (gElems desc)
-- getTheCs elems = foldl (\es e-> if not . isNode $ e then (getC e):es else es) [] elems

parsePortI :: ReadP PortI
parsePortI = do
   string "port"
   skipSpaces
   nm<-parse_id 
   skipSpaces
   parse_id >>= return . PortI nm

parseBlockI :: ReadP CDElem
parseBlockI = do
   string "block"
   skipSpaces
   nm<-parse_id 
   skipSpaces
   ty<-parse_id 
   skipSpaces
   ps<-between (char '{') (skipSpaces >>char '}') (many (skipSpaces >> parsePortI))
   return (ElemB $ BlockI nm ty ps)

parseCompositionI :: ReadP CDElem
parseCompositionI = do
   string "composition"
   skipSpaces
   nm<-parse_id
   skipSpaces
   ty<-parse_id
   skipSpaces
   char ':'
   skipSpaces
   bls<-parse_id
   skipSpaces
   string "->"
   skipSpaces
   blt<-parse_id
   return (ElemCn $ CompositionI nm ty bls blt)

parseConnector :: ReadP CDElem
parseConnector = do
   string "connector"
   skipSpaces
   nm<-option "" parse_id
   skipSpaces
   char ':'
   skipSpaces
   ty<-parse_id
   skipSpaces
   char '@'
   skipSpaces
   sBl<-parse_id -- name of source block
   char '.'
   sp<-parse_id -- name of source port
   skipSpaces
   string "->"
   skipSpaces
   tBl<-parse_id -- name of target block
   char '.'
   tp<-parse_id -- name of target port
   return (ElemCr $ Connector nm ty (sBl, sp) (tBl, tp))

parseCDElem :: ReadP CDElem
parseCDElem = do
  parseBlockI <|> parseCompositionI <|> parseConnector

parseCD :: ReadP CD
parseCD = do
   string "CD"
   skipSpaces
   nm<-parse_id 
   skipSpaces
   char ':'
   manyTill (skipSpaces >> parseCDElem) (skipSpaces >> eof) >>= return . CD nm
   --return (CD nm els)

loadCDFrFile::FilePath->IO (Maybe CD)
loadCDFrFile fn = do   
    --contents <- readFile fn
    --makes sure it is read
    readFile fn >>= return . parseMaybe parseCD

rootId::String->String
rootId nm = nm ++ "_ConfigurationDiagram"

connectorId::String->String
connectorId nm = nm ++ "_Connector"

typeId::String->String
typeId nm = nm ++ "_type"

-- Gets identifier of element in graph
gElemGId::CDElem->String
gElemGId (ElemB bi) = blockIId . gBlINm $ bi
gElemGId (ElemCn cn) = compositionIId . gCompositionNm $ cn
gElemGId (ElemCr cr) = connectorId . gCrNm $ cr

-- builds id of entity being named along with required edges 
nmPI :: String->String->PInfoWET String
nmPI snm nm = 
   let np = (nm, show_cd_mm_n CD_MM_Name)
       ep = ("ENmOf"++snm, show_cd_mm_e CD_MM_Ename)
       sp = ("ENmOf"++snm, snm)
       tp = ("ENmOf"++snm, nm) in 
   single4Fst np ep sp tp 

-- name of an edge from a node
enmFrN::String->String
enmFrN n = "E"++n

portIPI::String->String->PortI->PInfoWET String
portIPI nmBl blTy (PortI nm tnm) = 
   let nnm = portIId nmBl nm 
       nPI = (nnm, show_cd_mm_n CD_MM_PortI) in
   gJoin [singleNP nPI, singleNET (nnm, tnId blTy tnm), nmPI nnm nm]

portsIPI::String->String->[PortI]->PInfoWET String
portsIPI nmBl blTy ps = 
   let enm_l p = enmFrN $ (portIId nmBl $ gPtINm p) ++ "_port" 
       ep p = (enm_l p, show_cd_mm_e CD_MM_EBlockI_ports)
       sp p = (enm_l p, blockIId nmBl)
       tp p = (enm_l p, portIId nmBl $ gPtINm p) 
       es_et p = (enm_l p, tnId blTy (gPtINm p) ++ "_port")
       es_m = foldl (\pi p->gJoin[singleEPs (ep p) (sp p) (tp p), singleEET $ es_et p, pi]) emptyPIWET ps in
   foldl (\pi p->pi `join` (portIPI nmBl blTy p)) emptyPIWET ps `join` es_m
       
-- extracts the parsing info of a CD element
piFrCDElem::CDElem->PInfoWET String 
piFrCDElem (ElemB (BlockI nm tnm ps)) = 
   let nnm = blockIId nm in
   gJoin[nmPI nnm nm, singleNET (nnm, blockId tnm)
      , singleNP (nnm, show_cd_mm_n CD_MM_BlockI)
      , portsIPI nm tnm ps]
piFrCDElem (ElemCn (CompositionI nm tynm snm tnm)) = 
   let nnm = compositionIId nm
       nPI = (nnm, show_cd_mm_n CD_MM_CompositionI) 
       enm_s = enmFrN $ snm ++ "_" ++ tnm ++ "_src" 
       enm_t = enmFrN $ snm ++ "_" ++ tnm ++ "_tgt" 
       es_s = singleEPs (enm_s, show_cd_mm_e CD_MM_ECompositionI_src) (enm_s, nnm) (enm_s, blockIId snm)
       es_t = singleEPs (enm_t, show_cd_mm_e CD_MM_ECompositionI_tgt) (enm_t, nnm) (enm_t, blockIId tnm) in
   gJoin[singleNP nPI, nmPI nnm nm, singleNET (nnm, compositionId tynm), es_s, es_t]
piFrCDElem (ElemCr cr@(Connector nm tnm _ _)) = 
   let nnm = connectorId . gCrNm $ cr
       ntnm = typeId tnm
       nPI1 = singleNP (nnm, show_cd_mm_n CD_MM_Connector) 
       nPI2 = singleNP (ntnm, show_cd_mm_n CD_MM_ATypeRef) 
       (sBl, spnm) = gCrSPInfo cr
       (tBl, tpnm) = gCrTPInfo cr
       enm1 = enmFrN $ gCrNm cr ++ "_src" 
       enm2 = enmFrN $ gCrNm cr ++ "_tgt"
       enm3 = enmFrN $ gCrNm cr ++ "_ftype"
       es1 = singleEPs (enm1, show_cd_mm_e CD_MM_EConnector_src) (enm1, nnm) (enm1, portIId sBl spnm)
       es2 = singleEPs (enm2, show_cd_mm_e CD_MM_EConnector_tgt) (enm2, nnm) (enm2, portIId tBl tpnm) 
       es3 = singleEPs (enm3, show_cd_mm_e CD_MM_EConnector_ftype) (enm3, nnm) (enm3, ntnm) in
   gJoin [nmPI nnm $ gCrNm cr, nPI1, nPI2, es1, es2, es3]

piElems::String->[CDElem]->PInfoWET String 
piElems rnm es = 
   let elsPI = foldr(\e pi->piFrCDElem e `join` pi) emptyPIWET es
       enm tnm = enmFrN $ rnm ++ "_" ++ tnm 
       emp tnm = (enm tnm, show_cd_mm_e CD_MM_EHasElements) 
       esp tnm = (enm tnm, rootId rnm)
       etp tnm gnm = (enm tnm, gnm)
       npi tnm gnm = singleEPs (emp tnm) (esp tnm) (etp tnm gnm) in
   foldr(\e pi-> npi (gElemNm e) (gElemGId e) `join` pi) elsPI es

-- PI of root element
rootInfo::String->PInfoWET String
rootInfo nm  = 
   let nnm = rootId nm
       nsP = (nnm, show_cd_mm_n CD_MM_ConfigurationDiagram) in 
   nsP `joinNP` nmPI nnm nm

-- Constructs the graph with extra typing for the given CD model
gwetCD::CD->GrwET String String
gwetCD (CD nm els) = 
   let fpi = rootInfo nm `join` piElems nm els 
       cdG = consG (dom_of . nsm $ fpi) (dom_of . esm $ fpi) (sf fpi) (tf fpi) 
       tm = consGM (nsm fpi) (esm fpi) 
       etm = consGM (nsem fpi) (esem fpi) in
   consGWET cdG tm etm

loadCD::String->IO(GrwET String String)
loadCD fn = do
   ocd <- loadCDFrFile fn
   when (isNil ocd) $ do
         putStrLn "The CD definition could not be parsed."
   f(ocd >>= return . gwetCD)
   --return $ f <$> (ocd >>= return . gwetCD)
   where f Nothing = return Gr_Cls.empty
         f (Just g) = return g 


def_path :: String
def_path = "IntoSysML/Examples/"

test1 = readP_to_S parsePortI "port p P"
test2a = readP_to_S parseConnector "connector c : Int @ A.p1->B.p2"
test2b = readP_to_S parseConnector "connector : Int @ A.p1 -> B.p2"
test3 = readP_to_S parseBlockI "block b B {port p1 P1\n\t port p2 P2\n}"
test4 = readP_to_S parseBlockI "block b B {}"
test5 = readP_to_S parseCompositionI "composition c C : b1 -> b2"
test6 = readP_to_S parseBlockI "block S Source {port sw SW}"
--test6a = readP_to_S parse_ITN  "v1 OpenClosed \"closed\""
--test6b = readP_to_S parse_port "out v1 OpenClosed \"closed\" {}"
--test6c = readP_to_S parse_port "in v2 OpenClosed"

test7 :: [(CD, String)]
test7 = readP_to_S parseCD "CD ThreeWaterTanks:\n\tblock S Source {port sw SW}"

test8a :: IO ()
test8a = do
   readFile (def_path ++ "water_tanks.cd") >>= print
test8b :: IO ()
test8b = do
   --readFile (def_path ++ "three_water_tanks.cd") >>= readP_to_S parseCD >>= print
   loadCDFrFile (def_path ++ "water_tanks.cd") >>= print
   --putStrLn $ show cd
test8c :: IO ()
test8c = do
   loadCD (def_path ++ "water_tanks.cd") >>= print
   --putStrLn $ show asd_g
