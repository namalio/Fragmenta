module GrsDraw(wrGAsGraphviz) where

import Gr_Cls
import Relations ( appl )

data GEdge = GEdge String String String 
   deriving(Show)
data GNode = GNode String 
   deriving(Show) 
data GDrawing = GDrawing [GNode] [GEdge] 
   deriving(Show) 

--node_name::GNode->String
--node_name (GNode nm _) = nm

--ls_of_node_names::GDrawing->[String]
--ls_of_node_names (GDrawing ns es) = map node_name ns

consEdge g e = GEdge e (appl (src g) e) (appl (tgt g) e)
consEdges g = foldr (\e es'->(consEdge g e):es') [] (es g)

consNode n = GNode n 
consNodes g = foldr (\n ns'->(consNode n):ns') [] (ns g)
consGDrawingDesc :: GR g => g String String -> GDrawing
consGDrawingDesc g = GDrawing (consNodes g) (consEdges g)

wrEdgeSettings::String->String
wrEdgeSettings nm = "[" ++ (wrEdgeSettings' $ tail nm) ++ "];"
wrEdgeSettings'::String->String
wrEdgeSettings' enm = "label=\""++enm++"▼\",arrowhead=vee"
wrEdge :: GEdge->String
wrEdge (GEdge nm s t) = "\"" ++ s ++ "\"->\"" ++ t ++ "\"" ++ (wrEdgeSettings nm)
wrEdges :: Foldable t =>t GEdge->String
wrEdges es = foldr (\e es'-> (wrEdge e)++ "\n" ++es') "" es 

wrNode ::GNode ->String
wrNode (GNode nm) =  "\"" ++ nm ++ "\"" ++"[shape=box,fillcolor=\"#CCFFFF\",style = filled,label=\""++nm++"\"];"
wrNodes :: Foldable t=>t GNode->String
wrNodes ns  = foldr (\n ns'-> (wrNode n)++ "\n" ++ns') "" ns

wrGGraphvizDesc::String->GDrawing->String
wrGGraphvizDesc nm (GDrawing ns es) = 
   let intro = "digraph {graph[label=" ++ nm ++ ",labelloc=tl,labelfontsize=12];\n" in
   let end = "}" in
   intro ++ (wrNodes ns) ++ "\n" ++ (wrEdges es) ++ end


wrGAsGraphviz ::GR g=>String->g String String->String
wrGAsGraphviz nm g = wrGGraphvizDesc nm $ consGDrawingDesc g