module SGsDraw(SGDrawing(..),is_so,DrawPartKind(..),consSGDrawingDesc, wrSGGraphvizDesc, ls_of_node_names) where

import Gr_Cls
import Grs
import SGrs ( nty, ety, srcm, tgtm, pe, ds )
import Relations
import MyMaybe
import SGElemTys
import Mult
import PathExpressions
import Sets

data DrawPartKind = StandAlone | PartOf
   deriving(Eq, Show) 

is_so::DrawPartKind->Bool
is_so dpk = dpk == StandAlone

data SGEdge = SGEdge String SGETy Mult Mult String String (PE String String)
   deriving (Show)
data SGNode = SGNode String SGNTy [String] 
   deriving (Show) 
data SGDrawing = SGDrawing [SGNode] [SGEdge] [(String, String)]
   deriving (Show) 

node_name::SGNode->String
node_name (SGNode nm _ _) = nm

ls_of_node_names::SGDrawing->[String]
ls_of_node_names (SGDrawing ns _ _) = map node_name ns

consEdge sg e = 
   let et = appl (ety sg) e in
   SGEdge e et (appl (srcm sg) e) (appl (tgtm sg) e) (appl (src sg) e) (appl (tgt sg) e) (appl (pe sg) e)
consEdges sg = foldr (\e es'->(consEdge sg e):es') [] (es sg)

consNode sg n = SGNode n (appl (nty sg) n) []
consNodes sg = foldr (\n ns'->(consNode sg n):ns') [] (ns sg)
consDeps sg = foldr (\(e1, e2) ds'->(e1, e2):ds') [] (ds sg)
consSGDrawingDesc sg = SGDrawing (consNodes sg) (consEdges sg) (consDeps sg)

wrNode (SGNode nm Nabst _) = "\"" ++ nm++ "\"" ++ "[shape=record,fillcolor=lightskyblue1,style = filled,label=<{<I>"++nm++"</I><br/>(A)}>];"
wrNode (SGNode nm Nvirt _) = "\"" ++ nm++ "\"" ++ "[shape=record,fillcolor=lightskyblue1,style =\"filled,dotted\",label=<{<I>"++nm++"</I><br/>(V)}>];"
wrNode (SGNode nm Nenum _) = "\"" ++ nm++ "\"" ++ "[shape=record,fillcolor=\"#FFCCFF\",style = filled,label=\""++nm++"\\l(enum)\"];"
wrNode (SGNode nm Nval _) = "\"" ++ nm++ "\"" ++ "[shape=cds,fillcolor=\"#FFF2CC\",style = filled,label=\""++nm++"\"];"
wrNode (SGNode nm Nprxy _) = "\"" ++ nm++ "\"" ++ "[shape=box,fillcolor=lightgray,style =\"rounded,filled,dotted\",label=<"++(tail nm)++"<br/>(P)>];"
wrNode (SGNode nm Nopt _) =  "\"" ++ nm ++ "\"" ++"[shape=record,fillcolor=\"#CCFFFF\",style =\"filled,dotted\",label=<"++nm++"<br/>(O)>];"
--wrNode (SGNode nm Npath _) =  "\"" ++ nm++ "\"" ++ "[shape=box,style =\"filled,dashed\",label=\""++nm++"\"];"
wrNode (SGNode nm _ _) =  "\"" ++ nm ++ "\"" ++"[shape=record,fillcolor=lightskyblue1,style = filled,label=\""++nm++"\"];"
wrNodes :: Foldable t => t SGNode -> String
wrNodes ns  = foldr (\n ns'-> (wrNode n)++ "\n" ++ns') "" ns

wrMUV :: MultVal -> Bool -> String
wrMUV Many _ = "*"
wrMUV (Val n) b = if n == 1 then if b then "1" else "" else show n

wrMultS :: MultC -> String
wrMultS (Rm n sm)  = (show n) ++ ".." ++ (wrMUV sm True)
wrMultS (Sm sm) = (wrMUV sm) False

wrMult ::Mult -> String
wrMult (m `Set` EmptyS) = wrMultS m
wrMult (m `Set` ms) = (wrMultS m) ++ if ms == EmptyS then "" else  "," ++ (wrMult ms)

wrPEA (Edg e) = e
wrPEA (Inv e) = "~" ++ e

wrPE (At pea) = wrPEA pea
wrPE (Dres v pea) = v ++ " ◁ " ++ (wrPEA pea)
wrPE (Rres pea v) = (wrPEA pea)  ++ " ▷ " ++ v
wrPE (SCmp pe1 pe2) = (wrPE pe1) ++ " ⨾ " ++ (wrPE pe2)

wrEdgeSettings _ et@(Einh) m1 m2 pe = "[" ++ (wrEdgeSettings' "" et m1 m2 pe) ++ "];"
wrEdgeSettings nm et m1 m2 pe = "[" ++ (wrEdgeSettings' (tail nm) et m1 m2 pe) ++ "];"

--wrEdgeSettings' _ (Epdep) _ _ _ = "arrowhead=normal,arrowtail=normal,style=dotted"
wrEdgeSettings' :: [Char] -> SGETy -> Mult -> Mult -> PE String String -> String
wrEdgeSettings' _ (Einh) _ _ _ = "arrowhead=onormal,arrowsize=2.0"
wrEdgeSettings' enm (Eder) m1 m2 pe = "label=\""++enm++": " ++ (wrPE pe) ++ " ▼\",dir=none,taillabel=\""++ (wrMult m1) ++"\",headlabel=\""++ (wrMult m2) ++"\",style=dotted"
--wrEdgeSettings' enm (Epath) _ _ pe = "label=\""++enm++":" ++ (wrPE pe) ++ " ▼\",dir=none,style=dotted"
wrEdgeSettings' enm (Ecomp Dbi) m1 m2 _ = "label=\""++enm++"▼\",arrowtail=diamond,arrowhead=none,dir=both,taillabel=\""++ (wrMult m1) ++"\",headlabel=\""++ (wrMult m2) ++"\""
wrEdgeSettings' enm (Ecomp Duni) _ m _ = "label=\""++enm++"\",arrowhead=vee,arrowtail=diamond,dir=both,headlabel=\""++ (wrMult m) ++"\""
--wrEdgeSettings' enm (Ecomp Kseq) (Just m1) (Just m2)= "label=\""++enm++"▼\",arrowtail=diamond,arrowhead=veeodiamond,dir=both,taillabel=\""++ (wrMult m1) ++"\",headlabel=\"sequence "++ (wrMult m2) ++"\""
wrEdgeSettings' enm (Erel Dbi) m1 m2 _ = "label=\""++enm++"▼\",dir=none,taillabel=\""++ (wrMult m1) ++"\",headlabel=\""++ (wrMult m2) ++"\""
wrEdgeSettings' enm (Erel Duni) _ m _ = "label=\""++enm++"\",arrowhead=vee,headlabel=\""++ (wrMult m) ++"\",arrowsize=.5"
--wrEdgeSettings' enm (Erel Kseq) (Just m1) (Just m2) = "label=\""++enm++"▼\",arrowhead=veeodiamond,taillabel=\""++ (wrMult m1) ++"\",headlabel=\"sequence "++ (wrMult m2) ++"\""
--wrEdgeSettings' enm (Ewander) m1 m2 _ = "label=\""++enm++"▼▲\",dir=none,taillabel=\""++ (wrMult m1) ++"\",headlabel=\""++ (wrMult m2) ++"\""
--wrEdgeSettings' enm (Eseq) (Just m1) (Just m2) = "label=\""++enm++"\",arrowhead=normalodiamond,taillabel=\""++ (wrMult m1) ++"\",headlabel=\"sequence "++ (wrMult m2) ++"  \""
--wrEdgeSettings' enm (Eval) _ _ = "arrowhead=normal,arrowsize=2.0,label=\""++enm++"\",dir=none"

--wrDerFrEdge nm (Eder) d = "\n\"" ++ (tail nm) ++ "\"->\"" ++ d ++ "\"[arrowhead=curve,style=dotted];\""
--wrDerFrEdge _ _ _       = ""
npath_nm nm = "N_" ++ (tail nm)
wrEdge (SGEdge nm Epath _ _ s t pe) = wrNode ++ wrEdgeS ++ wrEdgeT
   where wrNode = "\"" ++ (npath_nm nm) ++ "\"" ++ "[shape=none,label=\""++(npath_nm nm)++" ➝ " ++ (wrPE pe) ++ "\"];\n"
         wrEdgeS = "\"" ++ (npath_nm nm) ++ "\"->\"" ++ s ++ "\"" ++ "[" ++ "arrowhead=dot,style=dotted" ++ "];\n"
         wrEdgeT = "\"" ++ (npath_nm nm) ++ "\"->\"" ++ t ++ "\"" ++ "[" ++ "arrowhead=vee,style=dotted" ++ "];\n"
wrEdge (SGEdge nm et m1 m2 s t pe) = "\"" ++ s ++ "\"->\"" ++ t ++ "\"" ++ (wrEdgeSettings nm et m1 m2 pe) -- (wrDerFrEdge nm et d)
wrEdges es  = foldr (\e es'-> (wrEdge e)++ "\n" ++es') "" es 
wrDep e1 e2 =  "\"" ++ (npath_nm e1) ++ "\"->\"" ++ (npath_nm e2) ++ "\"" ++ "[" ++ "arrowhead=normal,style=dashed, label = \"=\"" ++ "];\n"
wrDeps ds = foldr (\(e1, e2) ds'-> (wrDep e1 e2)++ ds') "" ds 

wrSGGraphvizDesc::String->DrawPartKind->SGDrawing->String
wrSGGraphvizDesc nm dpk (SGDrawing ns es ds) = 
   let wrStandAlone = "digraph {graph[label=" ++ nm ++ ",labelloc=tl,labelfontsize=12];\n" in
   (if is_so dpk then wrStandAlone else "") ++ (wrNodes ns) ++ "\n" ++ (wrEdges es) ++ (wrDeps ds) ++ (if is_so dpk then "}" else "")