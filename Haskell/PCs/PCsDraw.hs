------------------
-- Project: PCs/Fragmenta
-- Module: 'PCsDraw'
-- Description: Draws PCs as graphviz ddescriptions
-- Author: Nuno Amálio
-----------------
module PCs.PCsDraw(wrPCAsGraphviz
   , toPCDrawing) 
   where
 
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
import SimpleFuns (butLast)
import MMI ( gCRSG, MMI )
import PCs.PCsCommon

type Guard = Maybe String
type BindingExp = String

-- A parameter is a string and a type
data NodeInfo = Compound [Param] | Atom Id Guard
    | Reference Bool String [String] (Rel String String) Guard
    | Start | Stop | Skip | Import | Op OpKind [String]
    | QuantifiedOp OpKind Id BindingExp Guard 
    deriving(Eq, Show) 
data Node = Node Id NodeInfo deriving(Eq, Show) 
data ConnectorInfo = CDef | CAfter Bool | CRef [String] Bool 
   | CStart | CBranch | CBranchIf String 
   | CBranchElse 
   | CBranchJump 
   deriving(Eq, Show) 
data Connector = Connector String ConnectorInfo String String 
   deriving(Eq, Show) 
data Definition = Definition Id (Set String)
   deriving(Eq, Show)
data PCDrawing = PCDrawing String [Node] [Connector] [Definition] (Set (Set String)) 
   deriving(Eq, Show)

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
   | otherwise = sames' r xs $ (x `intoSet` img (trancl r) [x]) `intoSet` ls

sames :: Eq b=>Rel b b -> Set (Set b)
sames r = sames' r (dom_of r) nil

--fillVarBOfAtomPack::(String, Either String [String])->(String, String)
--fillVarBOfAtomPack v b = (v, strOfBinding b)
--fillVarBOfAtomPack (Just (v, b)) = Just (v, strOfBinding b) 

toNodeKind :: SGr String String ->PC String String -> String -> PCs_CMM_Ns -> NodeInfo
toNodeKind _ pc n CMM_Compound  = Compound $ fmap (uncurry cParam) (paramsOf pc n)
toNodeKind _ pc n CMM_Atom      = 
   let e = expOfAtom pc n
       rest = if isNil e then "" else "." ++ (the e) in
   Atom (nmOfNamed pc n ++ rest) (guardOf pc n) --(fillAnyExp $ anyExpOfAt pc n) 
toNodeKind _ pc n CMM_Reference = Reference (inner_Ref pc n) (nmOfRef pc n) (strOfTxtExps $ expsOf pc n) (renamingsOf pc n) (guardOf pc n)
toNodeKind _ _ _ CMM_Skip       = Skip
toNodeKind _ _ _ CMM_Stop       = Stop
toNodeKind _ _ _ CMM_StartN     = Start
toNodeKind _ _ _ CMM_Import     = Import
toNodeKind sg_mm pc n CMM_QuantifiedOp  = 
   let (v, e) = varBQuantifiedOp pc n in
   QuantifiedOp (readOp . read_cmm $ opQuantifiedOp sg_mm pc n) v (strOfTxtExp e) (guardOf pc n) 

--toOp :: PCs_CMM_Ns -> String
--toOp CMM_VOpIf            = "If"
--toOp CMM_VOpChoice        = "◻︎"
--toOp CMM_VOpIntChoice     = "⊓"
--toOp CMM_VOpParallel      = "||"
--toOp CMM_VOpInterleave    = "|||"
--toOp CMM_VOpThrow         = "Θ"

consDrawingNode :: SGr String String -> PC String String -> String -> Node
consDrawingNode sg_mm pc n = 
   let nt = read_cmm $ tyOfN n pc in
   let nts = [CMM_Compound, CMM_Atom, CMM_Reference, CMM_Stop, CMM_Skip, CMM_StartN, CMM_Import, CMM_QuantifiedOp] in
   if nt `elem` nts then Node n $ toNodeKind sg_mm pc n nt else Node n $ Op (readOp . read_cmm $ opValOfOp sg_mm pc n) (strOfTxtExps $ expsOf pc n)

toConnectorKind :: PC String String -> String -> PCs_CMM_Ns -> ConnectorInfo
toConnectorKind _ _ CMM_DefinesC     = CDef
toConnectorKind _ _ CMM_StartC       = CStart
toConnectorKind pc c CMM_AfterC      = CAfter (openAC pc c)
toConnectorKind pc c CMM_ReferenceC  = CRef (strOfTxtExps $ expsOf pc c) (hidden_RC pc c)
toConnectorKind _ _ CMM_BranchC      = CBranch 
toConnectorKind pc c CMM_BMainIfC    = CBranchIf (the $ guardOf pc c)
toConnectorKind _ _ CMM_BElseC       = CBranchElse
toConnectorKind _ _ CMM_BJumpC       = CBranchJump

consDrawingNodes :: Foldable t => SGr String String -> PC String String -> t String -> [Node]
consDrawingNodes sg_mm pc = foldr (\n ns'->(consDrawingNode sg_mm pc n):ns') []

consConnectors :: Foldable t => MMI String String -> PC String String -> t String -> [Connector]
consConnectors mmi pc cs = foldr (\c cs'->(Connector c (toConnectorKind pc c (read_cmm $ tyOfN c pc)) (srcOf mmi pc c) (tgtOf mmi pc c)):cs') [] cs

consDefinitions :: Foldable t => MMI String String -> PC String String -> t String -> [Definition]
consDefinitions mmi pc ds = foldr (\d ds'->(Definition d $ enumValsOf pc d):ds') [] ds


--getStartName nm = "start_" ++ nm 

--consCStart pc m = let c = (getPCDef m) in
--   Connector c CStart c (getPCStart pc m)

toPCDrawing :: MMI String String -> PC String String -> PCDrawing
toPCDrawing mmi pc = 
   let nodes = consDrawingNodes (gCRSG mmi) pc (ntyNsPC (gCRSG mmi) pc CMM_Node)
       cs = consConnectors mmi pc (ntyNsPC (gCRSG mmi) pc CMM_Connector) 
       ds = consDefinitions mmi pc (ntyNsPC (gCRSG mmi) pc CMM_Definition) 
       r_after = afterCRel mmi pc
       freeFromSameRefs = filterS (\n->length (img (inv r_after) [n])>1) (ntyNsPC (gCRSG mmi) pc CMM_Reference)
       ss_r = (rsub r_after freeFromSameRefs) `sminus` (inv $ trancl $ withinRel mmi pc)
       ss' = set [getPCStart (gCRSG mmi) pc, startCompound mmi pc] `intoSet` (sames ss_r) in
   PCDrawing (getPCDef pc) nodes cs ds ss'

wrParams :: (Foldable t, Functor t) => String -> t Param -> String
wrParams nm ps = 
   let ps' = fmap show ps
       lps = if null ps then "" else "(" ++ (showStrs ps' ",") ++ ")" in
   "\"" ++ nm ++ " " ++ lps ++ "\""

wrBindingsLabel :: Foldable t => String -> t String -> String
wrBindingsLabel nm bs = 
   let lbs = if null bs then "" else "(" ++ (showStrs bs ",") ++ ")" in
   "\"" ++ nm ++ " " ++ lbs ++ "\""

wrGuard :: Maybe String -> Bool -> String
wrGuard Nothing _ = ""
wrGuard (Just g) html = " {" ++ g ++ "}" ++ (if html then "<br/>" else "\n")

wrRefLabelPsRens :: Foldable t=>String -> [String] -> t (String, String) -> Maybe String -> Bool -> String
wrRefLabelPsRens nm bss rs g b = 
   let bs = wrOperatorLabel bss
       lbs = if null bs then "" else "(" ++ bs ++ ")"
       st_lrs = if null bs then "" else "\n" 
       lrs = if null rs then "" else st_lrs ++ "⟦" ++ (showStrs (foldr (\(fr, to) rps->(fr ++ "/" ++ to):rps) [] rs) ",") ++ "⟧" in
   "\"↑" ++ (wrGuard g False) ++ nm ++ " " ++ lbs ++ lrs ++ inner ++ "\""
   where inner = if b then "\n(Inner)" else ""

wrOperatorLabel :: [String] -> String
wrOperatorLabel [] = ""
wrOperatorLabel bs = showStrs bs "," 

--wrParamatersOfOp :: String -> [Param] -> String
--wrParamatersOfOp nm [] = ""
--wrParamatersOfOp nm ps = "\n"++ nm ++ "_ps" ++  "[shape=rect,fillcolor=yellow,style=\"filled,dotted\",label=\"" 
--   ++ (wrOperatorLabel ps) ++ "\"];\n" 
--   ++ nm ++"->" ++ nm ++ "_ps [dir=none,color=\"black:invis:black\"];\n" ++ "{rank=same;" ++ nm ++ "," ++ nm ++ "_ps}"


--toBindingsStrs::[String] -> String
--toBindingsStrs bs = wrOperatorLabel bs 

wrBindingsOfOp :: String -> [String] -> String
wrBindingsOfOp nm [] = ""
wrBindingsOfOp nm bss = "\n"++ nm ++ "_bs" ++  "[shape=rect,fillcolor=yellow,style=\"filled,dotted\",label=\"" 
   ++ wrOperatorLabel bss ++ "\"];\n" 
   ++ nm ++"->" ++ nm ++ "_bs [dir=none,color=\"black:invis:black\"];\n" ++ "{rank=same;" ++ nm ++ "," ++ nm ++ "_bs}"

--wrAtomCommon :: [Char] -> [Char]
--wrAtomCommon nm = nm ++ " [shape=ellipse,fillcolor=greenyellow,style = filled,label=" 
--wrAtomAny0 :: Maybe String -> [Char]
--wrAtomAny0 g = "<" ++ wrGuard g True
--wrAtomAny :: String -> Maybe String -> [Char]
--wrAtomAny "" g = (wrAtomAny0 g) ++ "<I>anyof</I> " 
--wrAtomAny atv g = (wrAtomAny0 g) ++ "<I>any</I> " ++ butLast atv ++ ":"

-- Writes graphviz code of a PC node
drawNode :: Node ->String
drawNode (Node nm (Compound ps)) =  nm ++ " [shape=box,fillcolor=deepskyblue,style = filled,label=" ++ (wrParams nm ps) ++ "];" 
drawNode (Node nm (Atom rnm g)) =  nm ++ " [shape=ellipse,fillcolor=greenyellow,style=filled,label=" ++ "\"" ++ (wrGuard g False) ++ rnm ++ "\"];"
--drawNode (Node nm (Atom rnm g)) = (wrAtomCommon nm) ++ (wrAtomAny atv g) -- ++ atS  
--    ++ "<br/>[" ++ rnm ++ "]>];"
drawNode (Node nm (Reference b rnm bs rs g)) = nm 
    ++ " [shape=rectangle,fillcolor=" ++ fillColor 
    ++ ",style=\"rounded,filled,dashed\",label="++ (wrRefLabelPsRens rnm bs rs g b) ++"];"
    where fillColor = if b then "\"#CBD7EB\"" else "gray"
drawNode (Node nm (Op op bs)) = nm ++ " [shape=diamond,fillcolor=yellow,style=filled,label=\"" ++ show op ++ "\"];" 
   ++ wrBindingsOfOp nm bs
drawNode (Node nm Stop) = nm ++ " [shape=box,fillcolor=mistyrose2,style = filled,label=\"STOP\"];"
drawNode (Node nm Skip) = nm ++ " [shape=box,fillcolor=\"#B9E0A5\",style = filled,label=\"SKIP\"];"
drawNode (Node nm Import) = nm ++ " [shape=hexagon,fillcolor=orangered,style=\"filled,rounded\",label =" ++  nm ++ "];" 
drawNode (Node nm (QuantifiedOp op v b g)) = 
   nm ++ " [shape=hexagon,fillcolor=gold1,style=filled,label=<" 
   ++ show op ++ " " ++ (butLast v) ++ ":" ++ b ++ (wrGuard g False) ++ ">];"

wrConnectorSettings :: ConnectorInfo -> String
wrConnectorSettings CDef = "[arrowhead=\"onormal\",penwidth=2,label=\"=\"];"
wrConnectorSettings CBranch = "[arrowhead=\"open\"];"
wrConnectorSettings (CBranchIf g) = "[arrowhead=\"open\",label=\""++g ++"\"];"
wrConnectorSettings CBranchElse = "[arrowhead=\"open\",label=\"Else\"];"
wrConnectorSettings CBranchJump = "[arrowhead=\"open\",label=\"Jump\"];"
wrConnectorSettings (CAfter o) =  "[arrowtail=" ++ (if o then "odot" else "dot") ++ ",dir=both,label=\"after\"];"
wrConnectorSettings (CRef bs _) = "[arrowhead=\"normalnormal\",fillcolor=white,label=" ++ (wrBindingsLabel "" bs) ++ "];"
wrConnectorSettings CStart = "[label=\"starts\"];"

wrConnector :: Connector -> String
wrConnector (Connector _ (CRef _ True) _ _) = ""
wrConnector (Connector nm ek s t) = s ++ "->" ++ t ++ (wrConnectorSettings ek)


drawDefVal::String->String
drawDefVal dv = dv ++ "[shape=box,fillcolor=darkolivegreen1,style=\"filled\",label=" ++ dv ++"];\n" 
drawDef :: Definition -> String
drawDef (Definition nm vs) =  
   "subgraph cluster_" ++ nm ++ " {\n" ++ "style=\"filled,rounded\";\n"
   ++ "label =" ++ nm ++ ";\n"
   ++ "fillcolor = cadetblue1;\n"
   ++ foldr (\dv s->drawDefVal dv ++ s) "" vs
   ++ "}\n"

drawDefs :: Foldable t => t Definition -> String
drawDefs = foldr (\d ds'-> (drawDef d)++ "\n" ++ ds') ""

drawNodes :: Foldable t => t Node -> String
drawNodes = foldr (\n ns'-> (drawNode n)++ "\n" ++ns') ""

drawConnectors :: Foldable t => t Connector -> String
drawConnectors = foldr (\c cs'-> (wrConnector c)++ "\n" ++cs') ""

wrSamesLs :: Foldable t =>t String->String
wrSamesLs ls = foldr (\n ns-> if null ns then n else n ++ "," ++ ns) "" ls ++ "}"

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
wrPCDrawing (PCDrawing nm ns cs ds ss) = "digraph {\n" ++ drawDefs ds ++ "\n" ++ (wrStartNode (startNode ns) nm) ++ "\n" 
   ++ (drawNodes $ filter (not . isNodeStart) ns) ++ "\n" ++ (wrSames ss) ++ "\n" ++ (drawConnectors cs) ++ "}"

wrPCAsGraphviz :: MMI String String -> PC String String -> String
wrPCAsGraphviz mmi pc = wrPCDrawing $ toPCDrawing mmi pc