------------------------------
-- Project: Fragmenta
-- Module: 'StCsDraw'
-- Description: Module that deals with the drawing of StCs as graphviz ddescriptions
-- Author: Nuno Amálio
-----------------------------
module Statecharts.StCsDraw(wrStCAsGraphviz, drawStC) where
 
import Statecharts.StCs
import SGrs
import Gr_Cls
import Grs
import Sets
import Relations
import ShowUtils
import TheNil
import MyMaybe
import Statecharts.StCs_MM_Names
import ParseUtils
import Statecharts.StCsCommon
import MMI


data Transition = Transition Name Name Name Event Guard Action
   deriving(Eq, Show)
data State = State Name StateTy [Desc] 
   deriving(Eq, Show)
data Desc = Desc Name [State] [Transition]
   deriving(Eq, Show) 
data StCDrawing = StCDrawing Name [Desc] 
   deriving(Eq, Show) 

gDescName (Desc nm _ _) = nm 

consDescOf mmi stc dnm = 
  let (sts, ts) = gDescInfo (mmi_sg_cmm mmi) stc dnm in
  let descsOf s = foldr(\dnm' ds->(consDescOf mmi stc dnm'):ds) [] (gDescs stc s) in
  let sts' = foldr (\s sts->(State (nmOfNamed' stc s) (frCMMTyToStTy  (gCMMStTy (mmi_sg_cmm mmi) stc s)) $ descsOf s):sts) [] sts in
  let takeExp s = if null s then s else snd $ splitAt' (\ch->ch==':') s in
  let consT t = let (s, t', e, g, a) = gTransitionInfo stc t in let (e':(g':(a':[]))) = map (takeExp . str_of_ostr) [e, g, a] in
                Transition t (nmOfNamed' stc s) (nmOfNamed' stc t') e' g' a' in
  let ts' = foldr (\t tds-> (consT t):tds) [] ts in 
  Desc (nmOfNamed' stc dnm) sts' ts'

drawStC mmi stc = StCDrawing (gStCName stc) $ foldr (\dnm ds->(consDescOf mmi stc dnm):ds) [] (gMainDescs stc)

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
wrStCDrawing sg_mm stc (StCDrawing nm descs) = "digraph {\ncompound=true;\nrankdir=LR;\nlabel=\"" ++ nm ++ "\";\n" 
   ++ "labelloc=t;\n" ++ (foldr (\d od_str->(wrDescwOuter sg_mm stc d)++ od_str) "" descs) ++ "}"
   

wrStCAsGraphviz mmi stc = wrStCDrawing (mmi_sg_cmm mmi) stc $ drawStC mmi stc