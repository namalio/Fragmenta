module IntoSysML.IntoSysML_CD_MM_Names (IntoSysML_CD_MM_Ns(..), IntoSysML_CD_MM_Es(..), show_cd_mm_n, show_cd_mm_e, read_cd_mm)
where

data IntoSysML_CD_MM_Ns = CD_MM_Name | CD_MM_Named | CD_MM_PortI | CD_MM_ATypeRef | CD_MM_Connector | CD_MM_BlockI | CD_MM_CompositionI | CD_MM_CDElement | CD_MM_ConfigurationDiagram
    deriving (Read, Show, Eq)

data IntoSysML_CD_MM_Es = CD_MM_Ename | CD_MM_EBlockI_ports | CD_MM_EConnector_src | CD_MM_EConnector_tgt | CD_MM_ECompositionI_tgt | CD_MM_ECompositionI_src | CD_MM_EConnector_ftype | CD_MM_EHasElements
    deriving (Read, Show, Eq)

show_cd_mm_n :: IntoSysML_CD_MM_Ns -> String
show_cd_mm_n nt = drop 6 (show nt)
show_cd_mm_e :: IntoSysML_CD_MM_Es -> String
show_cd_mm_e et = drop 6 (show et)
read_cd_mm :: Read a => [Char] -> a
read_cd_mm x = read ("CD_MM_" ++ x)
