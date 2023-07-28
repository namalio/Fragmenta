module GwETDraw(wrGwETAsGraphviz) where

import Gr_Cls
import Grs
import GrswET
import Sets ( toList )
import Relations ( appl)
import TheNil ( Nil(isNil), The(the) )
import MyMaybe ( applM )

data GwETEdge = GwETEdge String String String String (Maybe String)
   deriving(Show)
data GwETNode = GwETNode String String (Maybe String)
   deriving(Show) 
data GwETDrawing = GwETDrawing [GwETNode] [GwETEdge] 
   deriving(Show) 

--node_name::GNode->String
--node_name (GNode nm _) = nm

--ls_of_node_names::GDrawing->[String]
--ls_of_node_names (GDrawing ns es) = map node_name ns

consEdge :: GrwET String String -> String -> GwETEdge
consEdge gwt e = 
   let sn = appl (src gwt) e
       tn = appl (tgt gwt) e
       t = appl (fE gwt) e
       et = applM (fE (get gwt)) e in
   GwETEdge e sn tn t et
--consEdges gwt = foldr (\e es'->(consEdge gwt e):es') [] (es gwt)

consNode :: String -> String ->Maybe String->GwETNode
consNode = GwETNode

--consNodes gwt = foldr (\n ns'->(consNode n (appl (fV gwt) n)):ns') [] (ns gwt)
--map (\n ->consNode n (appl (fV gwt) n)) (ns gwt) --map (\n (consNode n (appl (fV gwt) n))) (ns gwt)
consGwETDrawingDesc :: GrwET String String -> GwETDrawing
consGwETDrawingDesc gwt = 
   let nodes = (\n->consNode n (appl (fV gwt) n) (applM (fV (get gwt)) n)) <$> (toList . ns $ gwt) 
       edges = consEdge gwt <$> (toList . es $ gwt) in
   GwETDrawing nodes edges

wrEdgeSettings ::String->String->Maybe String->String
wrEdgeSettings nm ety et = "[" ++ (wrEdgeSettings' (tail nm) (tail ety) et) ++ "];"
wrEdgeSettings' ::String->String->Maybe String->String
wrEdgeSettings' enm ety et = 
   let set = if isNil et then "" else "→" ++ the et in 
   "label=\":"++enm++ " ::" ++ ety ++ set ++"▼\",arrowhead=vee"

wrEdge :: GwETEdge -> String
wrEdge (GwETEdge nm s t ety et) = 
   "\"" ++ s ++ "\"->\"" ++ t ++ "\"" ++ (wrEdgeSettings nm ety et)
--wrEdges es  = 

wrNode :: GwETNode -> String
wrNode (GwETNode nm nty et) = 
   let snt = if isNil et then "" else "→" ++ the et in 
   "\"" ++ nm ++ "\"" ++"[shape=box,fillcolor=\"#CCFFFF\",style = filled,label=\":"++nm++" :: " ++ nty ++ snt ++ "\"];"
--wrNodes ns  = foldr (\n ns'-> (wrNode n)++ "\n" ++ns') "" ns

wrGwETGraphvizDesc::String->GwETDrawing->String
wrGwETGraphvizDesc nm (GwETDrawing ns es) = 
   let intro = "digraph {graph[label=" ++ nm ++ ",labelloc=tl,labelfontsize=12];\n" 
       end = "}" 
       strNodes = foldr (\n ns'-> (wrNode n)++ "\n" ++ns') "" ns
       strEdges = foldr (\e es'-> (wrEdge e)++ "\n" ++es') "" es  in
   intro ++strNodes ++ "\n" ++ strEdges ++ end

wrGwETAsGraphviz :: String -> GrwET String String -> String
wrGwETAsGraphviz nm gwt = wrGwETGraphvizDesc nm . consGwETDrawingDesc $ gwt