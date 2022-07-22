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
import GrswT
import Sets
import Relations
import ShowUtils
import The_Nil
import MyMaybe
import IntoSysML.ASD_MM_Names
import ParseUtils
import MMI
import IntoSysML.ASDCommon
import CommonParsing
import SimpleFuns

   
data BlockDef = BlockDef Name [Port]
   deriving(Eq, Show)
data Component = Component BlockDef [Variable] ComponentKind
   deriving(Eq, Show)
-- The different block types
data Block = BSystem BlockDef | BElement Component | BCompound Component PhenomenaKind 
   deriving(Eq, Show) 
data ASDDrawing = ASDDrawing Name [Block] [VTypeDef] [Composition] 
   deriving(Eq, Show) 

gComponentNm (Component bd _ _) = gBlockDefNm bd
gBlockDefPs (BlockDef _ ps) = ps
gBlockDefNm (BlockDef nm _) = nm 


-- Gets the type of a primitive type node string
gPty p_str = fst . (splitAtStr "_PTy") $ p_str

consATy asd id = 
   let p_str = gPty id in
   if p_str == id then ATypeId $ gName asd id else ATypeP (read $ replace '_' ' ' p_str)
consTN asd tn = TypedName (gName asd tn) (consATy asd $ gTypedNameTy asd tn) 
consITN asd itn = Initialisable (gName asd itn) (consATy asd $ gTypedNameTy asd itn) (str_of_ostr $ gInitialisableExp asd itn) 
consFieldI asd itn = FieldI $ consITN asd itn
consVariable asd v = Variable (consITN asd v) (read $ gVKind asd v)
consInFP asd itn = InFlowPort (consITN asd itn)
consOutFP asd itn = OutFlowPort (consITN asd itn) $ foldl (\ifps ifp->(gName asd ifp):ifps) [] (gOFPDeps asd itn)
consAPIP asd itn = APIPort (consITN asd itn)
consFP asd fp = consFPa (read_asd_mm $ appl (fV . ty $ asd) fp)
  where consFPa (ASD_MM_InFlowPort) = consInFP asd fp
        consFPa (ASD_MM_OutFlowPort) = consOutFP asd fp

consOp asd op = Operation (gName asd op) (foldl (\ops o->(consTN asd o):ops) [] (gOpParams asd op)) (consATy asd $ gOpReturn asd op) -- Here
consBlockDef asd b = BlockDef (gName asd b) $ foldl (\fps fp->(consFP asd fp):fps) []  (gBlocPs asd b) 
consBSystem asd b = BSystem $ consBlockDef asd b
consBComponent asd c = Component (consBlockDef asd c) (foldl (\vs v->(consVariable asd v):vs) [] (gCVars asd c)) (read $ gCKind asd c)
consBElement asd be = BElement (consBComponent asd be)
consCompound asd c = BCompound (consBComponent asd c) (read $ gCPKind asd c)
-- The compound constructor
consBlock mmi asd b = 
  consBlocka (read_asd_mm $ appl (fV . ty $ asd) b) 
  where consBlocka (ASD_MM_System) = consBSystem asd b
        consBlocka (ASD_MM_BElement) = consBElement asd b
        consBlocka (ASD_MM_Compound) = consCompound asd b

-- enumerations
consEnum asd e = VTypeEnum (gName asd e) (foldl (\ls l->(gName asd l):ls) [] (gEnumLs asd e))
-- derived types (DTypes)
consDType asd dt = DType (gName asd dt) (read $ gPty $ gDTypePTy asd dt)
-- unit types (UType)
consUType asd ut = UType (gName asd ut) (read $ gPty $ gDTypePTy asd ut) (gUTypeUnit asd ut)
-- structural types
consStrtType asd st = VTypeStrt (gName asd st) $ foldl (\itns itn->(consFieldI asd itn):itns) [] $ gStrtTypeFields asd st
-- interface
consInterface asd i = Interface (gName asd i) $ foldl (\ops op-> (consOp asd op):ops) [] $ gInterfaceOps asd i

-- The VType constructor
consVType mmi asd tnm = consVTypea (read_asd_mm $ appl (fV . ty $ asd) tnm) 
  where consVTypea (ASD_MM_Enumeration) = consEnum asd tnm
        consVTypea (ASD_MM_DType) = consDType asd tnm
        consVTypea (ASD_MM_UnitType) = consUType asd tnm
        consVTypea (ASD_MM_StrtType) = consStrtType asd tnm
        consVTypea (ASD_MM_Interface) = consInterface asd tnm

gVal vstr = fst . (splitAtStr "_Val") $ vstr

consMVal asd mv = consMVala (read_asd_mm $ appl (fV .ty $ asd) mv)
                where consMVala (ASD_MM_MultValMany) = MMany
                      consMVala (ASD_MM_MultValNum) = MultN (read . gVal $ gMultValNumN asd mv)
consMult asd m = consMulta (read_asd_mm $ appl (fV .ty $ asd) m)
               where consMulta (ASD_MM_MultSingle) = MultS $ consMVal asd (gMultSMVal asd m)
                     consMulta (ASD_MM_MultRange) = MultR (read . gVal $ gMultRLb asd m) (consMVal asd (gMultRUb asd m)) 

-- Composition
consComp asd c = Composition (gCompSrc asd c) (gCompTgt asd c) (read $ gCompSrcM asd c) (consMult asd $ gCompTgtM asd c)

drawASD mmi asd = 
  let bls = foldl (\bs bnm->(consBlock mmi asd bnm):bs) [] (gASDBlocks asd) in
  let vts = foldl (\ts tnm->(consVType mmi asd tnm):ts) [] (gASDVTypes asd) in
  let cs = foldl (\cos c->(consComp asd c):cos) [] (gASDComps asd) in
  ASDDrawing (gASDName asd) bls vts cs


wrMUV MMany _ = "*"
wrMUV (MultN n) b = if n == 1 then if b then "1" else "" else show n
wrMult (MultR n mv)  = (show n) ++ ".." ++ (wrMUV mv True)
wrMult (MultS mv) = (wrMUV mv) False

wrMultCS (Optional) = "0..1"
wrMultCS (Compulsory) = ""

gExp estr = fst . (splitAtStr ":Exp") $ estr

wrPty (PInterval lb ub) = (show lb) ++ ".." ++ (show ub) 
wrPty pty = tail . show $ pty

wrATy (ATypeP pty) = wrPty pty
wrATy (ATypeId ity) = ity

wrTypedName (TypedName nm ty) = nm ++ " : " ++ (wrATy ty) 
wrInitialisable (Initialisable nm ty ie) = nm ++ " : " ++ (wrATy ty) ++ (if null ie then "" else " = " ++ (gExp ie))

wrPorts ps = if null ps then "" else "<I>ports</I><br/>\n" ++ (foldl (\str p-> (wrPMTy . gPoMTy $ p) 
               ++ (wrInitialisable . gPoITN $ p) ++ (wrDeps (gPoMTy p) (gPoDeps p)) ++ "<br align=\"left\"/>" ++ str)) "" ps
   where wrPMTy ASD_MM_InFlowPort = "in "
         wrPMTy ASD_MM_OutFlowPort = "out "
         wrDeps ASD_MM_InFlowPort _ = ""
         wrDeps ASD_MM_OutFlowPort deps = if null deps then "" else "→" 
                                        ++ (foldl (\d_str d->d ++ (if null d_str then "" else ", ") ++ d_str) "" deps)

wrVariable (Variable itn vk) = (if vk == Parameter then "parameter " else  "") ++ (wrInitialisable itn)
wrVariables vs = if null vs then "" else "<I>variables</I><br/>\n" ++ foldl (\str v-> (wrVariable v) ++ "<br align=\"left\"/>\n" ++ str) "" vs

wrBCompound (Component bd vs ck) pk = 
   let nm = gBlockDefNm bd in
   (blockId nm) ++ " [shape=plain,fillcolor=\"#99FFFF\",style = filled,label=<\n"
   ++ "<table border=\"0\" cellborder=\"1\" cellspacing=\"0\" cellpadding=\"4\">\n"
   ++ "<tr><td>«Component»<br/>" ++ nm ++ "</td> </tr> <tr> <td align=\"left\">\n" ++ "kind = " ++ (lower_fst . show $ ck) ++ "<br align=\"left\"/>"
   ++ "phenomena = " ++ (lower_fst . show $ pk) ++ "<br align=\"left\"/>\n"
   ++ (wrVariables vs) ++ (wrPorts . gBlockDefPs $ bd) 
   ++ "</td> </tr></table>>];\n" 

wrBSystem (BlockDef nm ps) = (blockId nm) ++ " [shape=plain,fillcolor=\"#99FFFF\",style = filled,label=<\n"
   ++ "<table border=\"0\" cellborder=\"1\" cellspacing=\"0\" cellpadding=\"4\">\n"
   ++ "<tr> <td>«System»<br/>" ++ nm ++ "</td> </tr>"
   ++ (if null ps then "" else ("<tr> <td>\n" ++ (wrPorts ps) ++ "</td> </tr>"))
   ++ "</table>>];" 

wrComponent (Component bd vs ck) = "<tr><td>kind="++ (lower_fst . show $ ck) ++ "<br align=\"left\"/>\n" 
   ++ (wrVariables vs) ++ (wrPorts . gBlockDefPs $ bd) 

wrBElement c =
   let nnm = blockId . gComponentNm $ c in
   nnm ++ " [shape=plain,fillcolor=\"#99FFFF\",style = filled,label=<\n"
   ++ "<table border=\"0\" cellborder=\"1\" cellspacing=\"0\" cellpadding=\"4\">\n"
   ++ "<tr><td>«Element»<br/>"++(gComponentNm c)++"</td> </tr>"++(wrComponent c) ++"</td> </tr>"
   ++ "</table>>];\n"


wrEnumeration nm ls = nm ++ " [shape=plain,fillcolor=\"#FCDC0D\",style = filled,label=<\n" 
   ++ "<table border=\"0\" cellborder=\"1\" cellspacing=\"0\" cellpadding=\"4\">\n"
   ++ "<tr> <td>«Enumeration»<br/>" ++ nm ++ "</td></tr><tr><td align=\"left\">" 
   ++ (foldl (\str l-> "– " ++ l ++ "<br align=\"left\"/>\n" ++ str) "" ls) 
   ++ "</td> </tr></table>>];"


wrTN nm ty = nm ++ " : " ++ (wrATy ty)

wrStrtProps [] = ""
wrStrtProps ps = 
   let init ie = if null ie then "" else " = " ++ ie in
   "<tr> <td align=\"left\">\n" 
   ++ (foldl (\str (FieldI itn)-> (wrTN (gITNNm itn) (gITNTy itn)) ++ (init $ gITNInit itn) ++ (if null str then "" else "<br/>\n") ++ str) "" ps) 
   ++ "</td> </tr>"

wrOps [] = ""
wrOps os = 
  let wrSep str = if null str then "" else ", " in
  let wrParam tn str = (wrTN (gTNNm tn) (gTNTy tn)) ++ (wrSep str) ++ str in
  let wrEndStr str = "<br align=\"left\"/>\n" ++ str in
  let rowStart = "<tr> <td align=\"left\">\n" in
  (foldl (\str o-> rowStart ++ (gOpNm o) ++ "(" ++ (foldl (\str' tn-> wrParam tn str') "" $ gOpPs o) ++  ") : " ++ (wrATy . gOpRet $ o) ++ (wrEndStr str)) "" os)


wrVTStrt nm ps = 
   nm ++ " [shape=plain,fillcolor=\"#FFD5A3\",style = filled,label=<\n"
   ++ "<table border=\"0\" cellborder=\"1\" cellspacing=\"0\" cellpadding=\"4\">\n"
   ++ "<tr> <td>«ValueType»<br/>" ++ nm ++ "</td> </tr>" ++ wrStrtProps ps
   ++ "</table>>];"
wrDType nm pt = nm ++ " [shape=plain,fillcolor=\"#FFD5A3\",style = filled,label=<"
   ++ "<table border=\"0\" cellborder=\"1\" cellspacing=\"0\" cellpadding=\"4\">\n"
   ++ "<tr><td>«ValueType»<br/>"++nm++ "⟹" ++ (tail . show $ pt) 
   ++ "</td> </tr></table>>];"
wrUType nm pt u = nm ++ " [shape=plain,fillcolor=\"#FFD5A3\",style = filled,label=<"
   ++ "<table border=\"0\" cellborder=\"1\" cellspacing=\"0\" cellpadding=\"4\">\n"
   ++ "<tr><td>«ValueType»<br/>"++nm++"⟹" ++ (tail . show $ pt) ++ "</td> </tr> <tr> <td align=\"left\">\n" 
   ++ "unit = " ++ (show u) ++ "</td> </tr></table>>];"
wInterface nm os = 
   nm ++ " [shape=plain,fillcolor=\"#FCF1A6\",style = filled,label=<\n"
   ++ "<table border=\"0\" cellborder=\"1\" cellspacing=\"0\" cellpadding=\"4\">\n"
   ++ "<tr> <td>«Interface»<br/>" ++ nm ++ "</td> </tr>" ++ (wrOps os)
   ++ "</td></tr></table>>];"

wrVT (VTypeEnum nm ls) = (wrEnumeration nm ls) ++ "\n"
wrVT (VTypeStrt nm ps) = (wrVTStrt nm ps) ++ "\n" 
wrVT (DType nm pt) = (wrDType nm pt) ++ "\n" 
wrVT (UType nm pt u) = (wrUType nm pt u) ++ "\n" 
wrVT (Interface nm os) = (wInterface nm os) ++ "\n" 


wrBlock (BSystem bd) = wrBSystem bd 
wrBlock (BElement c) = wrBElement c
wrBlock (BCompound c pk) = wrBCompound c pk

wrComposition (Composition nms nmt ms mt) = 
   let nm = "C_" ++ nms ++ "->" ++ nmt in
   nms ++ "->" ++ nmt ++ "[arrowhead=vee,arrowtail=diamond,dir=both,headlabel=\""++ (wrMult mt) ++"\",taillabel=\""++ (wrMultCS ms) ++"\"];\n"


wrASDDrawing sg_mm asd (ASDDrawing nm bls vts cs) = "digraph {\ncompound=true;\nrankdir=LR;\nlabel=" ++ nm ++ ";\n" 
   ++ "labelloc=t;\n" ++ (foldl (\str vt->(wrVT vt) ++ str) "" vts)
   ++ (foldl (\str b->(wrBlock b) ++ str) "" bls) 
   ++ (foldl (\str c->(wrComposition c) ++ str) "" cs) 
   ++ "}"
   

wrASDAsGraphviz mmi asd = wrASDDrawing (mmi_sg_cmm mmi) asd $ drawASD mmi asd