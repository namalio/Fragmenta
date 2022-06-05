module SGsDraw(SGDrawing(..),is_so,DrawPartKind(..),consSGDrawingDesc, wrSGGraphvizDesc, ls_of_node_names) where

import Gr_Cls
import Grs
import SGrs
import Relations
import MyMaybe
import SGElemTys
import Mult

data DrawPartKind = StandAlone | PartOf
   deriving(Eq, Show) 

is_so::DrawPartKind->Bool
is_so dpk = dpk == StandAlone

data SGEdge = SGEdge String SGETy (Maybe Mult) (Maybe Mult) String String  String
    deriving (Show)
data SGNode = SGNode String SGNTy [String] 
    deriving (Show) 
data SGDrawing = SGDrawing [SGNode] [SGEdge] 
    deriving (Show) 

node_name::SGNode->String
node_name (SGNode nm _ _) = nm

ls_of_node_names::SGDrawing->[String]
ls_of_node_names (SGDrawing ns es) = map node_name ns

consEdge sg e = 
   let et = appl (ety sg) e in
   SGEdge e et (toMaybeFrLs $ img (srcm sg) [e]) (toMaybeFrLs $ img (tgtm sg) [e]) (appl (src sg) e) (appl (tgt sg) e) (if et == Eder then appl (derb sg) e else "")
consEdges sg = foldr (\e es'->(consEdge sg e):es') [] (es sg)

consNode sg n = SGNode n (appl (nty sg) n) []
consNodes sg = foldr (\n ns'->(consNode sg n):ns') [] (ns sg)
consSGDrawingDesc sg = SGDrawing (consNodes sg) (consEdges sg)

wrNode (SGNode nm Nabst _) = "\"" ++ nm++ "\"" ++ "[shape=record,fillcolor=lightskyblue1,style = filled,label=<{<I>"++nm++"</I><br/>(A)}>];"
wrNode (SGNode nm Nvirt _) = "\"" ++ nm++ "\"" ++ "[shape=record,fillcolor=lightskyblue1,style =\"filled,dotted\",label=<{<I>"++nm++"</I><br/>(V)}>];"
wrNode (SGNode nm Nenum _) = "\"" ++ nm++ "\"" ++ "[shape=record,fillcolor=\"#FFCCFF\",style = filled,label=\""++nm++"\\l(enum)\"];"
wrNode (SGNode nm Nval _) = "\"" ++ nm++ "\"" ++ "[shape=cds,fillcolor=\"#FFF2CC\",style = filled,label=\""++nm++"\"];"
wrNode (SGNode nm Nprxy _) = "\"" ++ nm++ "\"" ++ "[shape=box,fillcolor=lightgray,style =\"rounded,filled,dotted\",label=<"++(tail nm)++"<br/>(P)>];"
wrNode (SGNode nm Nopt _) =  "\"" ++ nm ++ "\"" ++"[shape=record,fillcolor=\"#CCFFFF\",style =\"filled,dotted\",label=<"++nm++"<br/>(O)>];"
wrNode (SGNode nm _ _) =  "\"" ++ nm ++ "\"" ++"[shape=record,fillcolor=lightskyblue1,style = filled,label=\""++nm++"\"];"
wrNodes ns  = foldr (\n ns'-> (wrNode n)++ "\n" ++ns') "" ns

wrMUV Many _ = "*"
wrMUV (Val n) b = if n == 1 then if b then "1" else "" else show n
wrMult (Rm n sm)  = (show n) ++ ".." ++ (wrMUV sm True)
wrMult (Sm sm) = (wrMUV sm) False

wrEdgeSettings _ et@(Einh) m1 m2 d = "[" ++ (wrEdgeSettings' "" et m1 m2 d) ++ "];"
wrEdgeSettings nm et m1 m2 d = "[" ++ (wrEdgeSettings' (tail nm) et m1 m2 (tail d)) ++ "];"

wrEdgeSettings' _ (Einh) _ _ _ = "arrowhead=onormal,arrowsize=2.0"
wrEdgeSettings' enm (Eder) (Just m1) (Just m2) d = "label=\""++enm++":" ++ d ++ " ▼\",dir=none,taillabel=\""++ (wrMult m1) ++"\",headlabel=\""++ (wrMult m2) ++"\",style=dotted"
wrEdgeSettings' enm (Ecomp Dbi) (Just m1) (Just m2) _= "label=\""++enm++"▼\",arrowtail=diamond,arrowhead=none,dir=both,taillabel=\""++ (wrMult m1) ++"\",headlabel=\""++ (wrMult m2) ++"\""
wrEdgeSettings' enm (Ecomp Duni) _ (Just m) _ = "label=\""++enm++"\",arrowhead=vee,arrowtail=diamond,dir=both,headlabel=\""++ (wrMult m) ++"\""
--wrEdgeSettings' enm (Ecomp Kseq) (Just m1) (Just m2)= "label=\""++enm++"▼\",arrowtail=diamond,arrowhead=veeodiamond,dir=both,taillabel=\""++ (wrMult m1) ++"\",headlabel=\"sequence "++ (wrMult m2) ++"\""
wrEdgeSettings' enm (Erel Dbi) (Just m1) (Just m2) _ = "label=\""++enm++"▼\",dir=none,taillabel=\""++ (wrMult m1) ++"\",headlabel=\""++ (wrMult m2) ++"\""
wrEdgeSettings' enm (Erel Duni) _ (Just m) _ = "label=\""++enm++"\",arrowhead=vee,headlabel=\""++ (wrMult m) ++"\",arrowsize=.5"
--wrEdgeSettings' enm (Erel Kseq) (Just m1) (Just m2) = "label=\""++enm++"▼\",arrowhead=veeodiamond,taillabel=\""++ (wrMult m1) ++"\",headlabel=\"sequence "++ (wrMult m2) ++"\""
wrEdgeSettings' enm (Ewander) (Just m1) (Just m2) _ = "label=\""++enm++"▼▲\",dir=none,taillabel=\""++ (wrMult m1) ++"\",headlabel=\""++ (wrMult m2) ++"\""
--wrEdgeSettings' enm (Eseq) (Just m1) (Just m2) = "label=\""++enm++"\",arrowhead=normalodiamond,taillabel=\""++ (wrMult m1) ++"\",headlabel=\"sequence "++ (wrMult m2) ++"  \""
--wrEdgeSettings' enm (Eval) _ _ = "arrowhead=normal,arrowsize=2.0,label=\""++enm++"\",dir=none"

--wrDerFrEdge nm (Eder) d = "\n\"" ++ (tail nm) ++ "\"->\"" ++ d ++ "\"[arrowhead=curve,style=dotted];\""
--wrDerFrEdge _ _ _       = ""
wrEdge (SGEdge nm et m1 m2 s t d) = "\"" ++ s ++ "\"->\"" ++ t ++ "\"" ++ (wrEdgeSettings nm et m1 m2 d) -- ++ (wrDerFrEdge nm et d)
wrEdges es  = foldr (\e es'-> (wrEdge e)++ "\n" ++es') "" es 

wrSGGraphvizDesc::String->DrawPartKind->SGDrawing->String
wrSGGraphvizDesc nm dpk (SGDrawing ns es) = 
   let wrStandAlone = "digraph {graph[label=" ++ nm ++ ",labelloc=tl,labelfontsize=12];\n" in
   (if is_so dpk then wrStandAlone else "") ++ (wrNodes ns) ++ "\n" ++ (wrEdges es) ++ (if is_so dpk then "}" else "")