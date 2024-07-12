module SGsDraw(
   SGDrawing(..)
   , is_so
   ,DrawPartKind(..)
   ,consSGDrawingDesc
   , wrSGGraphvizDesc
   , ls_of_node_names)
where

import Gr_Cls ( consGM, GR(ns, src, tgt, es), GRM(fE, fV), GrM )
import Grs
import SGrs 
import Relations
import MyMaybe
import SGElemTys
import Mult
import PathExpressions
import Sets
import ShowUtils
import SimpleFuns (butLast)
import TheNil

data DrawPartKind = StandAlone | PartOf
   deriving(Eq, Show) 

is_so::DrawPartKind->Bool
is_so dpk = dpk == StandAlone


data SGEdgeFI = SGEdgeFIM SGETy Mult Mult (PE String String) (Maybe String)
   | SGEdgeFICnt SGVCEOP (Maybe String)
   deriving (Show)
data SGEdge = SGEdge String String String SGEdgeFI
   deriving (Show)
data SGNode = SGNode String SGNTy (Maybe String)
   deriving (Show) 
data SGDrawing = SGDrawing [SGNode] [SGEdge] [(String, String)]
   deriving (Show) 

nname::SGNode->String
nname (SGNode nm _ _) = nm

--isEPath::SGEdge->Bool
--isEPath (SGEdge _ _ _ _ (SGEdgeFIM Epath _ _ _)) = True 

ls_of_node_names::SGDrawing->[String]
ls_of_node_names (SGDrawing ns _ _) = nname <$> ns

consSGEdgeM::(Eq a, Eq b, Show a,  Show b)=>SGr a b->GrM String String->b->SGEdgeFI
consSGEdgeM sg etm e = 
   let pes = fmap2PE show show $ appl (pe sg) e 
       enm = slimShow e in
   SGEdgeFIM (appl (ety sg) e) (appl (srcm sg) e) (appl (tgtm sg) e) pes (applM (fE etm) enm)

consSGEdgeCnt::(Eq a, Eq b, Show a,  Show b)=>SGr a b->GrM String String->b->SGEdgeFI
consSGEdgeCnt sg _ e = 
   let (op, ovce) = appl (vcei sg) e in
   SGEdgeFICnt op (show <$> ovce)

consEdge::(Eq a, Eq b, Show a,  Show b)=>SGr a b->GrM String String->b->SGEdge
consEdge sg etm e = 
   let enm = slimShow e
       et = appl (ety sg) e 
       sn = slimShow $ appl (src sg) e 
       tn = slimShow $ appl (tgt sg) e
       pes = fmap2PE show show $ appl (pe sg) e in
   SGEdge enm sn tn (consf et sg etm e )
   where consf Evcnt = consSGEdgeCnt
         consf _ = consSGEdgeM

consEdges::(Eq a, Eq b, Show a, Show b)=>SGr a b->GrM String String->[SGEdge]
consEdges sg etm = map (consEdge sg etm) (toList . es $ sg)

consNode::(Eq a, Show a)=>SGr a b->a->GrM String String->SGNode
consNode sg n etm = 
   let nnm = slimShow n in
   SGNode nnm (appl (nty sg) n) (applM (fV etm) nnm) 

consNodes::(Eq a, Eq b, Show a)=>SGr a b->GrM String String->[SGNode]
consNodes sg etm = map (\n->consNode sg n etm) (toList . ns $ sg)

consDeps::(Eq a, Eq b, Show a, Show b)=>SGr a b ->[(String, String)]
consDeps sg = foldr (\(e1, e2) ds'->(slimShow e1, slimShow e2):ds') [] (ds sg)
consSGDrawingDesc::(Eq a, Eq b, Show a, Show b)=>SGr a b ->GrM a b->SGDrawing
consSGDrawingDesc sg etm = 
   let m2 = consGM (strP <$> fV etm) (strP <$> fE etm) 
       strP (x, y) = (slimShow x, slimShow y) in
   SGDrawing (consNodes sg m2) (consEdges sg m2) (consDeps sg)

--addETN::SGNode->GrM String String->SGNode
--addETN (SGNode nm nty _) etm = SGNode nm nty (applM (fV etm) nm) 

--addETE::SGEdge->GrM String String->SGEdge
--addETE (SGEdge nm ety sm tm sn tn pei _) etm = 
--   SGEdge nm ety sm tm sn tn pei (applM (fE etm) nm) 

--addET::(Eq a, Eq b, Show a, Show b)=>SGDrawing->GrM a b->SGDrawing
--addET (SGDrawing ns es ds) m = 
--   let m2 = consGM (strP <$> fV m) (strP <$> fE m)
--       ns' = map (`addETN` m2) ns
--       es' = map (`addETE` m2) es 
--       strP (x, y) = (show x, show y) in
--   SGDrawing ns' es' ds

wret::Maybe String->String
wret Nothing = ""
wret (Just nm) = ":" ++ nm
wrNode :: SGNode -> String
wrNode (SGNode nm Nabst _) = "\"" ++ nm++ "\"" ++ "[shape=record,fillcolor=lightskyblue1,style = filled,label=<{<I>"++nm++"</I><br/>(A)}>];"
wrNode (SGNode nm Nvirt _) = "\"" ++ nm++ "\"" ++ "[shape=record,fillcolor=lightskyblue1,style =\"filled,dotted\",label=<{<I>"++nm++"</I><br/>(V)}>];"
wrNode (SGNode nm Nenum _) = "\"" ++ nm++ "\"" ++ "[shape=record,fillcolor=\"#FFCCFF\",style = filled,label=\""++nm++"\\l(enum)\"];"
wrNode (SGNode nm Nval _) = "\"" ++ nm++ "\"" ++ "[shape=cds,fillcolor=\"#FFF2CC\",style = filled,label=\""++tail nm++"\"];"
wrNode (SGNode nm Nprxy _) = "\"" ++ nm++ "\"" ++ "[shape=box,fillcolor=lightgray,style =\"rounded,filled,dotted\",label=<"++(tail nm)++"<br/>(P)>];"
--wrNode (SGNode nm Nopt _) =  "\"" ++ nm ++ "\"" ++"[shape=record,fillcolor=\"#CCFFFF\",style =\"filled,dotted\",label=<"++nm++"<br/>(O)>];"
--wrNode (SGNode nm Npath _) =  "\"" ++ nm++ "\"" ++ "[shape=box,style =\"filled,dashed\",label=\""++nm++"\"];"
wrNode (SGNode nm Nnrml et) =  "\"" ++ nm ++ "\"" ++"[shape=record,fillcolor=lightskyblue1,style = filled,label=\""++nm++wret et++"\"];"
wrNodes :: Foldable t => t SGNode -> String
wrNodes = foldr (\n ns'-> (wrNode n)++ "\n" ++ns') ""

wrMUV :: MultVal -> Bool -> String
wrMUV Many _ = "*"
wrMUV (Val n) b = if n == 1 then if b then "1" else "" else show n

wrMultS :: MultC -> String
wrMultS (Rm n sm) = show n ++ ".." ++ (wrMUV sm True)
wrMultS (Sm sm)   = (wrMUV sm) False

wrMult ::Mult -> String
wrMult (Mult (m `Set` EmptyS)) = wrMultS m
wrMult (Mult (m `Set` ms)) = wrMultS m ++ if ms == EmptyS then "" else  "," ++ wrMult (Mult ms)

edgName :: [a] -> [a]
edgName = drop 2 . butLast

nodeName:: [a]->[a]
nodeName = drop 1 . butLast

wrPEA :: PEA String->String
wrPEA (Edg e) = edgName e
wrPEA (Inv e) = "~" ++ edgName e

wrPEC :: PEC String String -> String
wrPEC (At pea) = wrPEA pea
wrPEC (Dres v pea) = nodeName v ++ " ◁ " ++ wrPEA pea
wrPEC (Rres pea v) = wrPEA pea  ++ " ▷ " ++ nodeName v
wrPE :: PE String String->String
wrPE (Ec pec) = wrPEC pec 
wrPE (SCmp pec pe) = wrPEC pec ++ " ⨾ " ++ wrPE pe

wrEdgeSettings ::String->SGETy->Mult->Mult->PE String String->Maybe String->String
wrEdgeSettings _ et@(Einh) m1 m2 pe ets = "[" ++ (wrEdgeSettings' "" et m1 m2 pe ets) ++ "];"
wrEdgeSettings nm et m1 m2 pe ets = "[" ++ (wrEdgeSettings' (tail nm) et m1 m2 pe ets) ++ "];"

--wrEdgeSettings' _ (Epdep) _ _ _ = "arrowhead=normal,arrowtail=normal,style=dotted"
edgeLabel::String->Maybe String->String
edgeLabel enm Nothing = enm
edgeLabel enm (Just ets) = enm++":"++ets

wrEdgeSettings' :: String->SGETy->Mult->Mult->PE String String->Maybe String->String
wrEdgeSettings' _ Einh _ _ _ _ = "arrowhead=onormal,arrowsize=2.0"
wrEdgeSettings' enm Eder m1 m2 pe _ = "label=\""++enm++": " ++ (wrPE pe) ++ " ▼\",dir=none,taillabel=\""++ (wrMult m1) ++"\",headlabel=\""++ (wrMult m2) ++"\",style=dotted"
--wrEdgeSettings' enm (Epath) _ _ pe = "label=\""++enm++":" ++ (wrPE pe) ++ " ▼\",dir=none,style=dotted"
wrEdgeSettings' enm (Ecomp Dbi) m1 m2 _ ets = "label=\""++edgeLabel enm ets++"▼\",arrowtail=diamond,arrowhead=none,dir=both,taillabel=\""++ (wrMult m1) ++"\",headlabel=\""++ (wrMult m2) ++"\""
wrEdgeSettings' enm (Ecomp Duni) _ m _ ets= "label=\""++edgeLabel enm ets++"\",arrowhead=vee,arrowtail=diamond,dir=both,headlabel=\""++ (wrMult m) ++"\""
--wrEdgeSettings' enm (Ecomp Kseq) (Just m1) (Just m2)= "label=\""++enm++"▼\",arrowtail=diamond,arrowhead=veeodiamond,dir=both,taillabel=\""++ (wrMult m1) ++"\",headlabel=\"sequence "++ (wrMult m2) ++"\""
wrEdgeSettings' enm (Erel Dbi) m1 m2 _ ets = "label=\""++edgeLabel enm ets++"▼\",dir=none,taillabel=\""++ (wrMult m1) ++"\",headlabel=\""++ (wrMult m2) ++"\""
wrEdgeSettings' enm (Erel Duni) _ m _ ets = "label=\""++edgeLabel enm ets++"\",arrowhead=vee,headlabel=\""++ (wrMult m) ++"\",arrowsize=.5"
--wrEdgeSettings' enm (Erel Kseq) (Just m1) (Just m2) = "label=\""++enm++"▼\",arrowhead=veeodiamond,taillabel=\""++ (wrMult m1) ++"\",headlabel=\"sequence "++ (wrMult m2) ++"\""
--wrEdgeSettings' enm (Ewander) m1 m2 _ = "label=\""++enm++"▼▲\",dir=none,taillabel=\""++ (wrMult m1) ++"\",headlabel=\""++ (wrMult m2) ++"\""
--wrEdgeSettings' enm (Eseq) (Just m1) (Just m2) = "label=\""++enm++"\",arrowhead=normalodiamond,taillabel=\""++ (wrMult m1) ++"\",headlabel=\"sequence "++ (wrMult m2) ++"  \""
--wrEdgeSettings' enm (Eval) _ _ = "arrowhead=normal,arrowsize=2.0,label=\""++enm++"\",dir=none"

--wrDerFrEdge nm (Eder) d = "\n\"" ++ (tail nm) ++ "\"->\"" ++ d ++ "\"[arrowhead=curve,style=dotted];\""
--wrDerFrEdge _ _ _       = ""
npathNm :: String -> String
npathNm nm = "N_" ++ (tail nm)

wrEdgeEPath::String->String->String->PE String String->String
wrEdgeEPath nm s t pe = 
   wrNode ++ wrEdgeS ++ wrEdgeT
   where wrNode = "\"" ++ npathNm nm ++ "\"" ++ "[shape=none,label=\""++npathNm nm++ " :: " ++ wrPE pe ++ "\"];\n"
         wrEdgeS = "\"" ++ npathNm nm ++ "\"->\"" ++ s ++ "\"" ++ "[" ++ "arrowhead=dot,style=dotted" ++ "];\n"
         wrEdgeT = "\"" ++ npathNm nm ++ "\"->\"" ++ t ++ "\"" ++ "[" ++ "arrowhead=vee,style=dotted" ++ "];\n"

wrEdgeDep::String->String->String
wrEdgeDep s t = "\"" ++ s ++ "\"->\"" ++ t ++ "\""
wrEdge :: SGEdge -> String
wrEdge (SGEdge nm s t (SGEdgeFIM et sm tm pe ets))
   | et == Epath = wrEdgeEPath nm s t pe 
   | otherwise = wrEdgeDep s t ++ wrEdgeSettings nm et sm tm pe ets -- (wrDerFrEdge nm et d)
wrEdge (SGEdge nm s t (SGEdgeFICnt op e)) = 
   let estr = if isNil e then "" else tail . slimStr . str_of_ostr $ e in
   wrEdgeDep s t ++ "[arrowhead=vee,style=dashed,label=\"" 
      ++ estr ++ wrOp op ++ "\"];\n"
   where wrOp Eq = " ="
         wrOp Neq = " ≠"
         wrOp Leq = " ≤"
         wrOp Geq = " ≥"
         wrOp Lt = " <"
         wrOp Gt = " >"
   

--wrEdge :: SGEdge -> String
--wrEdge (SGEdge nm _ _ s t pe ets) = wrNode ++ wrEdgeS ++ wrEdgeT
--   where wrNode = "\"" ++ npath_nm nm ++ "\"" ++ "[shape=none,label=\""++npath_nm nm++" ➝ " ++ (wrPE pe) ++ "\"];\n"
--         wrEdgeS = "\"" ++ npath_nm nm ++ "\"->\"" ++ s ++ "\"" ++ "[" ++ "arrowhead=dot,style=dotted" ++ "];\n"
--         wrEdgeT = "\"" ++ npath_nm nm ++ "\"->\"" ++ t ++ "\"" ++ "[" ++ "arrowhead=vee,style=dotted" ++ "];\n"
--wrEdge (SGEdge nm et m1 m2 s t pe ets) = "\"" ++ s ++ "\"->\"" ++ t ++ "\"" ++ (wrEdgeSettings nm et m1 m2 pe ets) -- (wrDerFrEdge nm et d)
wrEdges :: Foldable t => t SGEdge -> String
wrEdges = foldr (\e es'-> wrEdge e++ "\n" ++es') ""
wrDep :: String -> String -> String
wrDep e1 e2 =  "\"" ++ (npathNm e1) ++ "\"->\"" ++ (npathNm e2) ++ "\"" ++ "[" ++ "arrowhead=normal,style=dashed, label = \"=\"" ++ "];\n"
wrDeps :: Foldable t => t (String, String) -> String
wrDeps ds = foldr (\(e1, e2) ds'-> (wrDep e1 e2)++ ds') "" ds 

wrSGGraphvizDesc::String->DrawPartKind->SGDrawing->String
wrSGGraphvizDesc nm dpk (SGDrawing ns es ds) = 
   let wrStandAlone = "digraph {graph[label=" ++ nm ++ ",labelloc=tl,labelfontsize=12];\n" in
   (if is_so dpk then wrStandAlone else "") ++ (wrNodes ns) ++ "\n" ++ (wrEdges es) ++ (wrDeps ds) ++ (if is_so dpk then "}" else "")