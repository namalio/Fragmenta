------------------
-- Project: PCs/Fragmenta
-- Module: 'PCsDraw'
-- Description: Draws PCs as graphviz ddescriptions
-- Author: Nuno Amálio
-----------------
module PCs.PCsDraw(wrPCAsGraphviz) where
 
import PCs.PCs
import SGrs
import Gr_Cls
import Grs
import Sets
import Relations
import ShowUtils
import TheNil
import MyMaybe
import PCs.PCs_MM_Names

type Guard = Maybe String
data NodeInfo = Compound [String] | Atom String Guard (Maybe (String, String)) 
    | Reference Bool String [String] (Rel String String) Guard
    | Start | Stop | Skip | Import | Op String [String]
    deriving(Eq, Show) 
data Node = Node String NodeInfo deriving(Eq, Show) 
data ConnectorInfo = CDef | CAfter Bool | CRef [String] Bool | CStart | CBranch | CBranchIf String | CBranchElse | CBranchJump deriving(Eq, Show) 
data Connector = Connector String ConnectorInfo String String deriving(Eq, Show) 
data PCDrawing = PCDrawing String [Node] [Connector] (Set (Set String)) deriving(Eq, Show) 

nmOfNode :: Node -> String
nmOfNode (Node nm _) = nm 

isNodeStart :: Node -> Bool
isNodeStart (Node _ ni) = ni == Start

in_sames :: Eq a => a -> Set (Set a) -> Bool
in_sames x EmptyS = False
in_sames x (Set l ls) = x `elem` l || in_sames x ls

sames' :: Eq b =>Rel b b -> Set b -> Set (Set b) -> Set (Set b)
sames' _ EmptyS ls = ls
sames' r (Set x xs) ls 
   | in_sames x ls = sames' r xs ls
   | otherwise = sames' r xs $ ((x `intoSet` img (trancl r) [x]) `intoSet` ls)

sames :: Eq b=>Rel b b -> Set (Set b)
sames r = sames' r (dom_of r) nil

toNodeKind :: PC String String -> String -> PCs_CMM_Ns -> NodeInfo
toNodeKind pc n CMM_Compound  = Compound $ paramsOf pc n
toNodeKind pc n CMM_Atom      = Atom (nmOfNamed pc n) (guardOf pc n) (anyExpOfAt pc n) 
toNodeKind pc n CMM_Reference = Reference (inner_Ref pc n) (nmOfRef pc n) (paramsOf pc n) (renamingsOf pc n) (guardOf pc n)
toNodeKind _ _ CMM_Skip       = Skip
toNodeKind _ _ CMM_Stop       = Stop
toNodeKind _ _ CMM_StartN     = Start
toNodeKind _ _ CMM_Import     = Import

toOp :: PCs_CMM_Ns -> String
toOp CMM_VOpIf            = "If"
toOp CMM_VOpChoice        = "◻︎"
toOp CMM_VOpIntChoice     = "⊓"
toOp CMM_VOpParallel      = "||"
toOp CMM_VOpInterleave    = "|||"
toOp CMM_VOpThrow         = "Θ"

consDrawingNode :: SGr String String -> PC String String -> String -> Node
consDrawingNode sg_mm pc n = 
   let nt = read_cmm $ tyOfN n pc in
   let nts = [CMM_Compound, CMM_Atom, CMM_Reference, CMM_Stop, CMM_Skip, CMM_StartN, CMM_Import] in
   if nt `elem` nts then Node n $ toNodeKind pc n nt else Node n $ Op (toOp . read_cmm $ opValOfOp sg_mm pc n) (paramsOf pc n)

toConnectorKind :: PC String String -> String -> PCs_CMM_Ns -> ConnectorInfo
toConnectorKind _ _ CMM_DefinesC     = CDef
toConnectorKind _ _ CMM_StartC       = CStart
toConnectorKind pc c CMM_AfterC      = CAfter (openAC pc c)
toConnectorKind pc c CMM_ReferenceC  = CRef (paramsOf pc c) (hidden_RC pc c)
toConnectorKind _ _ CMM_BranchC      = CBranch 
toConnectorKind pc c CMM_BMainIfC    = CBranchIf (the $ guardOf pc c)
toConnectorKind _ _ CMM_BElseC       = CBranchElse
toConnectorKind _ _ CMM_BJumpC       = CBranchJump

consDrawingNodes :: Foldable t => SGr String String -> PC String String -> t String -> [Node]
consDrawingNodes sg_mm pc = foldr (\n ns'->(consDrawingNode sg_mm pc n):ns') []

consConnectors :: Foldable t => MMInfo String String -> PC String String -> t String -> [Connector]
consConnectors mmi pc cs = foldr (\c cs'->(Connector c (toConnectorKind pc c (read_cmm $ tyOfN c pc)) (srcOf mmi pc c) (tgtOf mmi pc c)):cs') [] cs

--getStartName nm = "start_" ++ nm 

--consCStart pc m = let c = (getPCDef m) in
--   Connector c CStart c (getPCStart pc m)

toPCDrawing :: MMInfo String String -> PC String String -> PCDrawing
toPCDrawing mmi pc = 
   let nodes = consDrawingNodes (pc_sg_cmm mmi) pc (pc_ns_of_nty (pc_sg_cmm mmi) pc CMM_Node)  in
   let cs = consConnectors mmi pc (pc_ns_of_nty (pc_sg_cmm mmi) pc CMM_Connector)  in
   let r_after = afterCRel mmi pc in
   let freeFromSameRefs = filterS (\n->(length (img (inv $ r_after) [n])>1)) (pc_ns_of_nty (pc_sg_cmm mmi) pc CMM_Reference)  in
   let ss_r = (rsub r_after freeFromSameRefs) `sminus` (inv $ trancl $ withinRel mmi pc) in
   let ss' = set [getPCStart (pc_sg_cmm mmi) pc, startCompound mmi pc] `intoSet` (sames ss_r) in
   PCDrawing (getPCDef pc) nodes cs ss'

wrParamsLabel :: Foldable t => String -> t String -> String
wrParamsLabel nm ps = 
   let lps = if null ps then "" else "(" ++ (showStrs ps ",") ++ ")" in
   "\"" ++ nm ++ " " ++ lps ++ "\""

wrGuard :: Maybe String -> Bool -> String
wrGuard Nothing _ = ""
wrGuard (Just g) html = " {" ++ g ++ "}" ++ (if html then "<br/>" else "\n")

wrRefLabelPsRens nm ps rs g b = 
   let lps = if null ps then "" else "(" ++ (showStrs ps ",") ++ ")" in
   let st_lrs = if null lps then "" else "\n" in
   let lrs = if null rs then "" else st_lrs ++ "⟦" ++ (showStrs (foldr (\(fr, to) rps->(fr ++ "/" ++ to):rps) [] rs) ",") ++ "⟧" in
   "\"↑" ++ (wrGuard g False) ++ nm ++ " " ++ lps ++ lrs ++ inner ++ "\""
   where inner = if b then "\n(Inner)" else ""

wrOperatorLabel :: [String] -> String
wrOperatorLabel [] = ""
wrOperatorLabel ps = (wrSepElems ps "," False False 0) 

wrParamatersOfOp :: String -> [String] -> String
wrParamatersOfOp nm [] = ""
wrParamatersOfOp nm ps = "\n"++ nm ++ "_ps" ++  "[shape=rect,fillcolor=yellow,style=\"filled,dotted\",label=\"" ++ (wrOperatorLabel ps) ++ "\"];\n" 
   ++ nm ++"->" ++ nm ++ "_ps [dir=none,color=\"black:invis:black\"];\n" ++ "{rank=same;" ++ nm ++ "," ++ nm ++ "_ps}"


wrAtomCommon :: [Char] -> [Char]
wrAtomCommon nm = nm ++ " [shape=ellipse,fillcolor=greenyellow,style = filled,label=" 
wrAtomAny0 :: Maybe String -> [Char]
wrAtomAny0 g = "<" ++ (wrGuard g True)
wrAtomAny :: String -> Maybe String -> [Char]
wrAtomAny "" g = (wrAtomAny0 g) ++ "<I>anyof</I> " 
wrAtomAny atv g = (wrAtomAny0 g) ++ "<I>any</I> " ++ atv ++ ":"

-- Writes graphviz code of a PC node
wrNode :: Node ->String
wrNode (Node nm (Compound ps)) =  nm ++ " [shape=box,fillcolor=deepskyblue,style = filled,label=" ++ (wrParamsLabel nm ps) ++ "];" 
wrNode (Node nm (Atom rnm g Nothing)) =  (wrAtomCommon nm) ++ "\"" ++ (wrGuard g False) ++ rnm ++ "\"];"
wrNode (Node nm (Atom rnm g (Just (atv, atS)))) = (wrAtomCommon nm) ++ (wrAtomAny atv g) ++ atS  
    ++ "<br/>[" ++ rnm ++ "]>];"
wrNode (Node nm (Reference b rnm ps rs g)) = nm 
    ++ " [shape=rectangle,fillcolor=" ++ fillColor 
    ++ ",style=\"rounded,filled,dashed\",label="++ (wrRefLabelPsRens rnm ps rs g b) ++"];"
    where fillColor = if b then "\"#CBD7EB\"" else "gray"
wrNode (Node nm (Op op ps)) = nm ++ " [shape=diamond,fillcolor=yellow,style = filled,label=\"" ++ op ++ "\"];" 
   ++ wrParamatersOfOp nm ps
wrNode (Node nm Stop) = nm ++ " [shape=box,fillcolor=mistyrose2,style = filled,label=\"STOP\"];"
wrNode (Node nm Skip) = nm ++ " [shape=box,fillcolor=\"#B9E0A5\",style = filled,label=\"SKIP\"];"
wrNode (Node nm Import) = nm ++ " [shape=hexagon,fillcolor=orangered,style=filled,label =" ++  nm ++ "];" 

wrConnectorSettings :: ConnectorInfo -> String
wrConnectorSettings CDef = "[arrowhead=\"onormal\",penwidth=2,label=\"=\"];"
wrConnectorSettings CBranch = "[arrowhead=\"open\"];"
wrConnectorSettings (CBranchIf g) = "[arrowhead=\"open\",label=\""++g ++"\"];"
wrConnectorSettings CBranchElse = "[arrowhead=\"open\",label=\"Else\"];"
wrConnectorSettings CBranchJump = "[arrowhead=\"open\",label=\"Jump\"];"
wrConnectorSettings (CAfter o) =  "[arrowtail=" ++ (if o then "odot" else "dot") ++ ",dir=both,label=\"after\"];"
wrConnectorSettings (CRef ps _) = "[arrowhead=\"normalnormal\",fillcolor=white,label=" ++ (wrParamsLabel "" ps) ++ "];"
wrConnectorSettings CStart = "[label=\"starts\"];"

wrConnector :: Connector -> String
wrConnector (Connector _ (CRef _ True) _ _) = ""
wrConnector (Connector nm ek s t) = s ++ "->" ++ t ++ (wrConnectorSettings ek)

wrNodes :: Foldable t => t Node -> String
wrNodes ns  = foldr (\n ns'-> (wrNode n)++ "\n" ++ns') "" ns

wrConnectors :: Foldable t => t Connector -> String
wrConnectors cs  = foldr (\c cs'-> (wrConnector c)++ "\n" ++cs') "" cs 

wrSamesLs :: Foldable t =>t String->String
wrSamesLs ls = (foldr (\n ns-> if null ns then n else n ++ "," ++ ns) "" ls) ++ "}"

wrSameRank :: Foldable t => t String->String
wrSameRank ls = "{rank=same;" ++ wrSamesLs ls

--wrMinRank :: Foldable t => t String -> String
--wrMinRank ls = "{rank=min;" ++ wrSamesLs ls

wrSames' :: Set (Set String) -> String
wrSames' EmptyS = ""
wrSames' (Set l ls) = (wrSameRank l) ++ "\n" ++ (wrSames' ls)

wrSames :: Set (Set String) -> String
wrSames ls = --wrMinRank (first ls) ++ "\n" ++ wrSames' (rest ls)
   wrSames' ls

startNode :: [Node] -> String
startNode ns = nmOfNode . the $ filter (isNodeStart) ns
wrStartNode :: String -> String -> String
wrStartNode snm nm = snm ++  " [shape = cds,color=burlywood2,style=filled,height=.2,width=.2, label =" ++  nm ++ "];" 

wrPCDrawing :: PCDrawing -> String
wrPCDrawing (PCDrawing nm ns cs ss) = "digraph {\n" ++ (wrStartNode (startNode ns) nm) ++ "\n" 
   ++ (wrNodes $ filter (not . isNodeStart) ns) ++ "\n" ++ (wrSames ss) ++ "\n" ++ (wrConnectors cs) ++ "}"

wrPCAsGraphviz :: MMInfo String String -> PC String String -> String
wrPCAsGraphviz mmi pc = wrPCDrawing $ toPCDrawing mmi pc