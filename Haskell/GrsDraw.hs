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
wrEdgeSettings nm = "[" ++ (wrEdgeSettings' nm) ++ "];"
wrEdgeSettings'::String->String
wrEdgeSettings' "" = "arrowhead=vee"
wrEdgeSettings' enm = "label=\""++tail enm++"\",arrowhead=vee"
wrEdge :: Bool->GEdge->String
wrEdge b (GEdge nm s t) = 
   let nm' = if b then nm else "" in
   "\"" ++ s ++ "\"->\"" ++ t ++ "\"" ++ (wrEdgeSettings nm')
wrEdges :: Foldable t =>Bool->t GEdge->String
wrEdges b = foldr (\e es'-> (wrEdge b e)++ "\n" ++es') ""

wrNode ::GNode ->String
wrNode (GNode nm) =  "\"" ++ nm ++ "\"" ++"[shape=box,fillcolor=\"#CCFFFF\",style = filled,label=\""++nm++"\"];"
wrNodes :: Foldable t=>t GNode->String
wrNodes = foldr (\n ns'-> wrNode n ++ "\n" ++ns') ""

-- Boolean indicates whether edge labels are visible
wrGGraphvizDesc::String->Bool->GDrawing->String
wrGGraphvizDesc nm b (GDrawing ns es) = 
   let intro = "digraph {graph[label=" ++ nm ++ ",labelloc=tl,labelfontsize=12];\n" in
   let end = "}" in
   intro ++ (wrNodes ns) ++ "\n" ++ (wrEdges b es) ++ end


wrGAsGraphviz ::GR g=>String->Bool->g String String->String
wrGAsGraphviz nm b g = wrGGraphvizDesc nm b $ consGDrawingDesc g