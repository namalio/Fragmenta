------------------------------
-- Project: Fragmenta
-- Module: 'DrawASD'
-- Description: Module that deals with drawing of SysML ASDs via graphviz
-- Author: Nuno Amálio
-----------------------------
module IntoSysML.DrawCD(
   drawCD) where
 
import IntoSysML.IntoSysMLCD
import SGrs
import Gr_Cls
import Grs
import GrswT
import Sets
import Relations
import ShowUtils
import TheNil
import MyMaybe
import IntoSysML.ASD_MM_Names
import ParseUtils
import MMI
import IntoSysML.ASDCommon
import ParsingCommon
import SimpleFuns
import IntoSysML.ASCD
import IntoSysML.IntoSysMLCD

data MultiTree a = MultiTree a [MultiTree a]
   deriving (Eq, Show)

data CDDrawing = CDDrawing Name [MultiTree BlockI] [Connector]
   deriving (Eq, Show)

mkCDDrawing::MMI String String->CDG String String->CDDrawing
mkCDDrawing mmi cd =
   let cr = gCompRel cd
       rs = dom_of cr `sminus` ran_of cr
       cs = map (mkConnector cd) $ toList (gConnectors (gCRSG mmi) cd) in
   CDDrawing (gCDName cd) (mkMultiTrees mmi cd rs cr) cs

mkMultiTrees::MMI String String->CDG String String->Set String->Rel String String->[MultiTree BlockI]
mkMultiTrees _ _ EmptyS _ = []
mkMultiTrees mmi cd (Set r rs) cr = mkMultiTree mmi cd r cr:mkMultiTrees mmi cd rs cr

mkMultiTree::MMI String String->CDG String String->String->Rel String String->MultiTree BlockI
mkMultiTree mmi cd r cr = 
   let sns = img cr [r] in
   MultiTree (mkBlI cd r) (mkMultiTrees mmi cd sns cr)

--drawCD mmi cd = 
--  let els = foldl (\es e->mkElem mmi cd e:es) [] (gCDElems cd) in
--  CD (gCDName cd) els
  --where
  --    addTo Nothing es = es
  --    addTo (Just e) es = e:es

--mkElem::MMI String String->CDG String->String->Maybe CDElem
--mkElem mmi cd enm 
--   | isBlockI (gCRSG mmi) cd enm = Just $ mkBlI cd enm
--   | isCompositionI (gCRSG mmi) cd enm = Just $ mkCompositionI cd enm
--   | isConnector (gCRSG mmi) cd enm = Just $ consConnector cd enm

-- Constructs a port instance
mkPtI::CDG String String->String->PortI
mkPtI cd pnm = PortI (gName cd pnm) (gEty cd pnm)

-- Constructs a block instance 
mkBlI::CDG String String->String->BlockI
mkBlI cd bnm = 
   let ps = map (mkPtI cd) (toList $ gBlIPorts cd bnm) 
       (etynm, _) = splitAt' (=='_') (gEty cd bnm) in
   BlockI (gName cd bnm) etynm ps

-- Constructs a composition instance 
--mkCompositionI::CDG String->String->CDElem
--mkCompositionI cd cnm = 
--   ElemCn (CompositionI (gName cd cnm) (gEty cd cnm) (gCompSrc cd cmm) (gCompTgt cd cmm))

-- Constructs a connector
mkConnector::CDG String String->String->Connector
mkConnector cd cnm =
   Connector (gName cd cnm) (fst . splitAt' (=='_') $ gFlowTy cd cnm) (gSrcP cd cnm) (gTgtP cd cnm)

wrPortI::String->PortI->String
wrPortI blNm (PortI nm _) = 
   let id = portIId blNm nm 
       blId = blockIId blNm in 
   id ++ "[shape=circle,label=\"" ++ nm++ "\"];\n"
   ++ blId ++ "->" ++ id ++ "[dir=none];\n"

wrPortIs::String->[PortI]->String
wrPortIs blNm ps = foldr (\p s->wrPortI blNm p ++ s) "" ps

wrBlINode::BlockI->String
wrBlINode (BlockI nm tnm ps) = 
   let id = blockIId nm in
   id ++ "[shape=plain,fillcolor=\"#CCFFCC\",style = filled,label=\"" ++ nm ++ " : " ++ tnm ++ "\"];\n"
   ++ wrPortIs nm ps

wrEndCluster::String
wrEndCluster = "}\n"
wrBlICluster::String->String->String
wrBlICluster nm tnm = 
   let idc = blockIId nm ++ "_" -- id of cluster
       idn = blockIId nm in     -- id of self node
   "subgraph " ++ idc ++ " {\ncluster=true;label=\"" ++ nm ++ ":" ++ tnm ++ "\";\n"
   ++ idn ++ "[shape=plain,fillcolor=\"#CCFFCC\",style = filled,label=self];\n"
 
wrTrees::[MultiTree BlockI]->String
wrTrees = concatMap wrTree
--wrTrees [] = ""
--wrTrees (t:ts) = wrTree t ++ wrTrees ts
wrTree::MultiTree BlockI->String
wrTree (MultiTree b []) = wrBlINode b
wrTree (MultiTree (BlockI nm tnm ps) (t:ts)) = 
   wrBlICluster nm tnm ++ wrTree t ++ wrTrees ts ++ wrEndCluster ++ wrPortIs nm ps

wrConnector::Connector->String
wrConnector (Connector nm ty (sBl, sp) (tBl, tp)) =
   let spId = portIId sBl sp 
       tpId = portIId tBl tp in
   spId ++ "->" ++ tpId ++ "[label=\"" ++ ty ++ "\"];\n"

wrCDAsGraphviz :: CDDrawing->String
wrCDAsGraphviz (CDDrawing nm ts cs) = "digraph {\ncompound=true;\nrankdir=LR;\nlabel=" ++ nm ++ ";\n" 
   ++ "labelloc=t;\n" ++ wrTrees ts ++ foldl (\s c->wrConnector c ++ s) "}" cs

drawCD :: MMI String String -> CDG String String -> String
drawCD mmi cd = wrCDAsGraphviz $ mkCDDrawing mmi cd