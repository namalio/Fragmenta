--------------------------
-- Project: Fragmenta
-- Module: 'IntoSysML'
-- Description: Handler module of Into SysML CDs
-- Author: Nuno Amálio
--------------------------

module IntoSysML.IntoSysMLCD(
    CDG
    , loadCDMMI
    , gName
    , gEty
    , gRoot
    , gCDName
    , gConnectors
    , isBlockI
    , isCompositionI
    , isConnector
    , gBlIPorts
    , gCompISrc 
    , gCompITgt
    , gCompRel
    , gFlowTy
    , gSrcP
    , gTgtP
)
where

import GrswET
import Mdls 
import LoadCheckDraw
import Gr_Cls
import MMI
import Frs
import Relations
import Sets
import IntoSysML.IntoSysML_CD_MM_Names
import TheNil
import SGrs
import ParseUtils

type CDG a b = GrwET a b

loadAMM :: String -> IO (String, Mdl String String)
loadAMM = flip loadMdl "IntoSysML_AAD_MM"

loadCMM :: String -> IO (String, Mdl String String)
loadCMM = flip loadMdl "IntoSysML_CD_MM"

loadRM :: String -> IO (GrM String String)
loadRM def_path = load_rm_cmdl_def def_path "IntoSysML_CD_MM"

loadCDMMI :: String -> IO (MMI String String)
loadCDMMI def_path = do
  (_, amm)<-loadAMM def_path
  (_, cmm)<-loadCMM def_path
  rm<-loadRM def_path
  return $ consMMI cmm amm rm (fsg . reso_m $ cmm)

-- Gives the relation of an edge in a ASD
consRelOfEdge::(GR g, GRM g)=>g String String->IntoSysML_CD_MM_Es->Rel String String
consRelOfEdge cd e = 
   let es = es_of_ety cd . show_cd_mm_e $ e in
   foldr (\e r->(appl (src cd) e, appl (tgt cd) e) `intoSet` r) nil es

-- Gets name of some named node
gName :: (GR g, GRM g) => g String String -> String -> String
gName cd = appl (consRelOfEdge cd CD_MM_Ename)

-- Gets a type's name of some node with an expected extra type
gEty :: (GR g, GRM g, GWET g, GWT g) => g String String -> String -> String
gEty cd = appl (fV . etm $ cd)

-- Gets name of given ASD
gRoot::(GWT g, GR g)=>g String String->String
gRoot cd = appl (inv . fV . ty $ cd) "ConfigurationDiagram"

gCDName :: (GR g, GRM g, GWT g) => g String String -> String
gCDName cd = gName cd . gRoot $ cd

nsNTy::(GRM gm) =>SGr String String->gm String String->IntoSysML_CD_MM_Ns->Set String
nsNTy sg_mm cd nt = ns_of_ntys cd sg_mm [show_cd_mm_n nt]

-- Gets CD elements
gCDElems ::(GR g, GRM g, GWT g) =>g String String -> Set String 
gCDElems cd = img (consRelOfEdge cd CD_MM_EHasElements) [gRoot cd]

-- Gets Connector elements
gConnectors::GRM g=>SGr String String->g String String -> Set String
gConnectors sg_mm cd = nsNTy sg_mm cd CD_MM_Connector

isBlockI :: GRM gm => SGr String String -> gm String String -> String -> Bool
isBlockI sg_mm cd n = n `elem` nsNTy sg_mm cd CD_MM_BlockI

isCompositionI :: GRM gm => SGr String String -> gm String String -> String -> Bool
isCompositionI sg_mm cd n = n `elem` nsNTy sg_mm cd CD_MM_CompositionI

isConnector :: GRM gm => SGr String String -> gm String String -> String -> Bool
isConnector sg_mm cd n = n `elem` nsNTy sg_mm cd CD_MM_Connector

-- Gets the ports of a block instance
gBlIPorts :: (GR g, GRM g) => g String String -> String -> Set String
gBlIPorts cd bln = img (consRelOfEdge cd CD_MM_EBlockI_ports) [bln]

-- Gets source block of a composition
gCompISrc :: (GR g, GRM g, GWT g) =>g String String ->String-> String
gCompISrc cd = appl (consRelOfEdge cd CD_MM_ECompositionI_src)

-- Gets source block of a composition
gCompITgt :: (GR g, GRM g, GWT g) =>g String String ->String-> String
gCompITgt cd = appl (consRelOfEdge cd CD_MM_ECompositionI_tgt)

-- Gets the composition relation
gCompRel:: (GR g, GRM g, GWT g) =>g String String -> Rel String String
gCompRel cd = inv (consRelOfEdge cd CD_MM_ECompositionI_src) `rcomp` (consRelOfEdge cd CD_MM_ECompositionI_tgt)

-- Gets flowing type of a connector 
gFlowTy::(GR g, GRM g, GWT g) => g String String->String->String
gFlowTy cd = appl (consRelOfEdge cd CD_MM_EConnector_ftype)

-- Gets source port of a connector 
gSrcP::(GR g, GRM g, GWT g) => g String String->String->(String, String)
gSrcP cd cr = 
    let s = appl (consRelOfEdge cd CD_MM_EConnector_src) cr 
        (sBl, r) = splitAt' (=='_') s 
        (sp, _) = splitAt' (=='_') r in
    (sBl, sp)

-- Gets target port of a connector 
gTgtP::(GR g, GRM g, GWT g) => g String String->String->(String, String)
gTgtP cd cr = 
    let s = appl (consRelOfEdge cd CD_MM_EConnector_tgt) cr
        (tBl, r) = splitAt' (== '_') s
        (tp, _) = splitAt' (== '_') r in
    (tBl, tp)