module GwTDraw(wrGwTAsGraphviz) where

import Gr_Cls
import Grs
import GrswT
import Relations

data GwTEdge = GwTEdge String String String String
   deriving(Show)
data GwTNode = GwTNode String String
   deriving(Show) 
data GwTDrawing = GwTDrawing [GwTNode] [GwTEdge] 
   deriving(Show) 

--node_name::GNode->String
--node_name (GNode nm _) = nm

--ls_of_node_names::GDrawing->[String]
--ls_of_node_names (GDrawing ns es) = map node_name ns

consEdge :: (GR g, GRM g) => g String String -> String -> GwTEdge
consEdge gwt e = GwTEdge e (appl (src gwt) e) (appl (tgt gwt) e) (appl (fE gwt) e)
--consEdges gwt = foldr (\e es'->(consEdge gwt e):es') [] (es gwt)

consNode :: String -> String -> GwTNode
consNode = GwTNode

--consNodes gwt = foldr (\n ns'->(consNode n (appl (fV gwt) n)):ns') [] (ns gwt)
consGwTDrawingDesc :: (GRM g, GR g) => g String String -> GwTDrawing
consGwTDrawingDesc gwt = 
   let nodes  = foldr (\n ns'->(consNode n (appl (fV gwt) n)):ns') [] (ns gwt)
       edges = foldr (\e es'->(consEdge gwt e):es') [] (es gwt) in
   GwTDrawing nodes edges

wrEdgeSettings :: String -> String -> String
wrEdgeSettings nm ety = "[" ++ (wrEdgeSettings' (tail nm) (tail ety)) ++ "];"
wrEdgeSettings' :: String -> String -> String
wrEdgeSettings' enm ety = "label=\":"++enm++ " ::" ++ ety ++ "▼\",arrowhead=vee"
wrEdge :: GwTEdge -> String
wrEdge (GwTEdge nm s t ety) = "\"" ++ s ++ "\"->\"" ++ t ++ "\"" ++ (wrEdgeSettings nm ety)
--wrEdges es  = 

wrNode :: GwTNode -> String
wrNode (GwTNode nm nty) =  "\"" ++ nm ++ "\"" ++"[shape=box,fillcolor=\"#CCFFFF\",style = filled,label=\":"++nm++" :: " ++ nty ++ "\"];"
--wrNodes ns  = foldr (\n ns'-> (wrNode n)++ "\n" ++ns') "" ns

wrGwTGraphvizDesc::String->GwTDrawing->String
wrGwTGraphvizDesc nm (GwTDrawing ns es) = 
   let intro = "digraph {graph[label=" ++ nm ++ ",labelloc=tl,labelfontsize=12];\n" 
       end = "}" 
       strNodes = foldr (\n ns'-> (wrNode n)++ "\n" ++ns') "" ns
       strEdges = foldr (\e es'-> (wrEdge e)++ "\n" ++es') "" es  in
   intro ++strNodes ++ "\n" ++ strEdges ++ end

wrGwTAsGraphviz :: (GRM g, GR g) => String -> g String String -> String
wrGwTAsGraphviz nm gwt = wrGwTGraphvizDesc nm $ consGwTDrawingDesc gwt