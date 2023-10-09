---------------------------------------
-- Project: Fragmenta
-- Module: 'ASCD'
-- Description: Representation of the abstract syntax of SysML configuration diagrams 
-- (a subset of SysML internal block diagrams) 
-- Author: Nuno Amálio
---------------------------------------

module IntoSysML.ASCD (
    PortI(..)
    , BlockI(..)
    , CompositionI(..)
    , Connector(..)
    , CDElem(..)
    , CD(..)
    , gPtINm
    , gPtITy
    , gBlINm
    , gBlITy
    , gBlIPs
    , gCompositionNm
    , gCrSPInfo
    , gCrSBlNm
    , gCrSPNm
    , gCrTPInfo
    , gCrTBlNm
    , gCrTPNm
    , gCrNm
    , gElemNm
    , blockIId
    , compositionIId
    , portIId) 
where

import SimpleFuns

-- Names are represented as strings
type Name = String

-- Port instance: name and port type
data PortI = PortI Name Name 
   deriving (Eq, Show)

--Block instance: instance's name, name of block type and ports
data BlockI = BlockI Name Name [PortI]
   deriving (Eq, Show)

-- Composition instance: name of composition, composition type, and names of source and target block instances
data CompositionI = CompositionI Name Name Name Name
   deriving (Eq, Show)

-- Connector: name of connector, name of flowing type
-- and the two ports being connected (a pair each, corresponding to block and port)
data Connector = Connector Name Name (Name, Name) (Name, Name)
   deriving (Eq, Show)

 -- A CD element is either a block instance, composition instance, or a connector
data CDElem = ElemB BlockI | ElemCn CompositionI | ElemCr Connector
   deriving(Eq, Show)

-- A CD comprises a name followed by a number of elements
data CD = CD Name [CDElem]
   deriving(Eq, Show)

-- Gets information contained in a port instance
gPtIInfo::PortI->(Name, Name)
gPtIInfo (PortI nm ty) = (nm, ty)
-- Gets name of port
gPtINm::PortI->Name
gPtINm = fst . gPtIInfo
-- Gets type of port
gPtITy::PortI->Name
gPtITy = snd . gPtIInfo

-- Gets information contained in a block instance
gBlIInfo::BlockI->(Name, Name, [PortI])
gBlIInfo (BlockI nm ty ps) = (nm, ty, ps)

gBlINm::BlockI->Name
gBlINm = fstT . gBlIInfo

gBlITy::BlockI->Name
gBlITy = sndT . gBlIInfo

gBlIPs::BlockI->[PortI]
gBlIPs = thdT . gBlIInfo

gCompositionNm::CompositionI->Name
gCompositionNm (CompositionI nm _ _ _) = nm

gCrSPInfo::Connector->(String, String)
gCrSPInfo (Connector _ _ sp _) = sp 
gCrSBlNm::Connector->String
gCrSBlNm = fst . gCrSPInfo 
gCrSPNm::Connector->String
gCrSPNm = snd . gCrSPInfo 
gCrTPInfo::Connector->(String, String)
gCrTPInfo (Connector _ _ _ tp) = tp
gCrTBlNm::Connector->String
gCrTBlNm = fst . gCrTPInfo 
gCrTPNm::Connector->String
gCrTPNm = snd . gCrTPInfo

-- Gets name of a connector
gCrNm::Connector->String
gCrNm cr@(Connector nm _ _ _) = nm ++ (gCrSBlNm cr) ++ "_" ++ (gCrSPNm cr) ++ "_" ++ (gCrTBlNm cr) ++ "_" ++ (gCrTPNm cr)

-- Gets root name of element
gElemNm::CDElem->String
gElemNm (ElemB bi) = gBlINm bi
gElemNm (ElemCn c) = gCompositionNm c
gElemNm (ElemCr c) = gCrNm c

-- Unique identifier of a block in a graph
blockIId::String->String
blockIId nm = nm ++ "_BlI"

-- Unique identifier of a composition in a graph
compositionIId::String->String
compositionIId nm = nm ++ "_CompositionI"

portIId::String->String->String
portIId nmBl nm = nmBl ++ "_" ++ nm ++ "_PI"