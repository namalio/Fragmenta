------------------------------
-- Project: Fragmenta
-- Module: 'IntoSysMLDraw'
-- Description: Module that deals with the drawing of ASDs as graphviz descriptions
-- Author: Nuno Amálio
-----------------------------
module IntoSysML.ASDsDraw(wrASDAsGraphviz, drawASD) where
 
import IntoSysML.IntoSysML
import SGrs
import Gr_Cls
import Grs
import Sets
import Relations
import ShowUtils
import The_Nil
import MyMaybe
import IntoSysML.IntoSysML_ASD_MM_Ns
import ParseUtils
import MMI
import IntoSysML.ASDParseDrawCommon

data Comp = Comp Name Name
   deriving(Eq, Show)
data VType = VType Name 
   deriving(Eq, Show)
data BlockDef = BlockDef  Name [FlowPort]
   deriving(Eq, Show)
data Component = Component BlockDef [Variable] ComponentKind
   deriving(Eq, Show)
-- The different block types
data Block = BSystem BlockDef | BElement Component | BCompound Component PhenomenaKind 
   deriving(Eq, Show) 
data ASDDrawing = ASDDrawing [Block] [VType] [Comp] 
   deriving(Eq, Show) 

gBlockName (Block nm) = nm 

consProperty asd p = Property (gName asd p) (gName asd $ gPropVTy asd p) (gPropExp asd p)
consVariable asd v = Variable (consProperty asd v) (read $ gVKind asd v)
consInFP asd fp = InFlowPort (consProperty asd fp)
consOutFP asd fp = OutFlowPort (consProperty asd fp) (foldl (\ifps ifp->(gName asd ifp):ifps) [] $ gOFPDeps fp)
consFP asd fp = 
  consFPa (read_asd_mm $ appl (ty asd) fp)
  where consFPa (ASD_MM_InFlowPort) = consInFP asd fp
        consFPa (ASD_MM_OutFlowPort) = consOutFP asd fp

consBlockDef mmi asd b = BlockDef (gName asd b) (foldl (\fps fp->(consFP mmi asd fp):fps) [] $ gBlockFPs b) 
consBSystem mmi asd b = BSystem $ consBlockDef mmi asd b
consComponent mmi asd c = Component (consBlockDef mmi asd c) (gCVars asd c) (read $ gCKind asd c)
consBElement mmi asd be = BElement (consComponent mmi asd be)
consCompound mmi asd c = BCompound (consComponent mmi asd be) (read $ gCPKind asd c)
-- The compound (Here)
consBloc mmi asd b = 
  consBlocka (read_asd_mm $ appl (ty asd) b) = 
  where consBlocka (ASD_MM_System) = consBSystem mmi asd b
        consBlocka (ASD_MM_BElement) = consBElement mmi asd b
        consBlocka (ASD_MM_Compound) = consCompound mmi asd b


consEnum mmi asd e = VTypeEnum (gName asd e) (gEnumLs asd e)
consVType mmi asd tnm = VType tnm
consComp mmi asd nms nmt = Comp nms nmt

drawASD mmi asd = 
  let bls = foldl (\bs bnm->(consBlock mmi asd bnm):bs) [] (gASDBlocks asd) in
  let vts = foldl (\ts tnm->(consVType mmi asd tnm):ts) [] (gASDVTypes asd) in
  let cs = foldl (\cos c->(consComp mmi asd c):cos) [] (gASDComps asd) in
  ASDDrawing bls vts cs

cons_Src_Tgt sg_mm stc s t = 
  let ch_nm s' = let snm = (s' ++ "_St") in if isMutableStatewInner sg_mm stc snm then nmOfNamed' stc $ gInnerStart sg_mm stc snm else s' in
  let prop_s = let snm = (s ++ "_St") in if isMutableStatewInner sg_mm stc snm then "ltail=cluster_" ++ s else "" in
  let prop_t = let snm = (t ++ "_St") in if isMutableStatewInner sg_mm stc snm then "lhead=cluster_" ++ t else "" in
  (ch_nm s, ch_nm t, prop_s, prop_t)

wrTransition sg_mm stc (Transition nm s t ev g a) = 
   let sg = if null g then "" else "[" ++ g ++ "]" in
   let sa = if null a then "" else "/" ++ a in
   let (s', t', prop_s, prop_t) = cons_Src_Tgt sg_mm stc s t in
   let prop_s' = " " ++ prop_s in
   let prop_t' = " " ++ prop_t in
   s' ++ "->" ++ t' ++ "[label=\"" ++ ev ++ sg ++ sa ++ "\"" ++ "," ++ prop_s' ++ prop_t' ++ "];"

gNm nm = (fst $ splitAtStr "_" nm)
wrState _ _ (State nm MutableSt []) = nm ++ " [shape=box,fillcolor=darkseagreen,style=\"filled,rounded\",label="++ (gNm nm) ++ "];" 
wrState sg_mm stc (State _ MutableSt (d:[])) = wrDescwOuter sg_mm stc d
wrState sg_mm stc (State nm MutableSt ds@(_:_)) = (wrDescOuter nm) ++ (foldr (\d s->(wrDescwOuter sg_mm stc d)++s) "" ds) ++ "}\n"
wrState _ _ (State nm EndSt []) = 
   nm ++ " [shape=doublecircle,height=.3,width=.3,fixedsize=true,fillcolor=black,style=filled,label=\"\"];" 
wrState _ _ (State nm StartSt []) = 
   nm ++ " [shape = point,fillcolor=black,height=.2,width=.2,label=\"\"];\n"
wrState _ _ (State nm HistorySt []) = 
   nm ++ " [shape = circle,fillcolor=black,label=\"H\"];\n"
--wrState _ _ (State nm stt _) = nm ++  (show stt) ++ ";\n"

wrStates sg_mm stc ss = foldr (\s ss'-> (wrState sg_mm stc s)++ "\n" ++ ss') "" ss
wrTransitions sg_mm stc ts = foldr (\t ts'-> (wrTransition sg_mm stc t)++ "\n" ++ ts') "" ts 


--wrStartMarker sg_mm stc dnm start = 
--  let (s, t, prop_s, prop_t) = cons_Src_Tgt sg_mm stc ("StartMarker_" ++ dnm) start in
--  let props = if null (prop_s ++ prop_t) then "" else "[" ++ prop_s ++ " " ++ prop_t ++ "];" in
--  "StartMarker_" ++ dnm ++ " [shape = point,fillcolor=black,height=.2,width=.2,label=\"\"];\n"
--   ++  s ++ "->" ++ t ++ props ++ "\n"

wrDescOuter nm = "subgraph cluster_" ++ nm ++ " {\n" ++ "style=\"filled,rounded\";\n"
   ++ "label =\""++(gNm nm)++"\";\n" ++ "fillcolor = lightgray;\n"
wrDescwOuter sg_mm stc d = (wrDescOuter $ gDescName d) ++ (wrDescInner sg_mm stc d)
wrDescInner sg_mm stc (Desc nm sts ts) = (wrStates sg_mm stc sts) ++ "\n" ++ (wrTransitions sg_mm stc ts) ++ "}\n"
wrASDDrawing sg_mm asd (ASDDrawing nm descs) = "digraph {\ncompound=true;\nrankdir=LR;\nlabel=\"" ++ nm ++ "\";\n" 
   ++ "labelloc=t;\n" ++ (foldr (\d od_str->(wrDescwOuter sg_mm stc d)++ od_str) "" descs) ++ "}"
   

wrStCAsGraphviz mmi stc = wrStCDrawing (mmi_sg_cmm mmi) stc $ drawStC mmi stc