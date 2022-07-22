module IntoSysML.CD_MM_Names (IntoSysML_CD_MM_Ns(..), IntoSysML_CD_MM_Es(..), show_cd_mm_n, show_cd_mm_e, read_cd_mm)
where

data IntoSysML_CD_MM_Ns = CD_MM_Named | CD_MM_ConfigurationDiagram | CD_MM_Name | CD_MM_CompositionI | CD_MM_BlockI | CD_MM_Connector | CD_MM_PortI
   | CD_VTypeRef 
   deriving (Read, Show, Eq)

data IntoSysML_CD_MM_Es = CD_MM_ENamed_name | CD_MM_EHasCompositions | CD_MM_EHasConnectors | CD_MM_EHasBlocks | CD_MM_EComposition_src 
   | CD_MM_EComposition_tgt | CD_MM_EConnector_src | CD_MM_EConnector_tgt |  CD_MM_EBlockI_ports | CD_MM_EConnector_ftype
   deriving (Read, Show, Eq)

show_cd_mm_n nt = drop 7 (show nt)
show_cd_mm_e et = drop 7 (show et)

read_cd_mm :: String -> IntoSysML_CD_MM_Ns
read_cd_mm x = read ("CD_MM_" ++ x)
