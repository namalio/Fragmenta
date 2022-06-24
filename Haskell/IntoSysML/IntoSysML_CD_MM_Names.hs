module IntoSysML.CD_MM_Names (IntoSysML_CD_MM_Ns(..), IntoSysML_CD_MM_Es(..), show_cd_mm_n, show_cd_mm_e, read_cd_mm)
where

data IntoSysML_CD_MM_Ns = CD_MM_Named | CD_MM_Name | CD_MM_PNat | CD_MM_PReal | CD_MM_PBool | CD_MM_PString | CD_MM_PType | CD_MM_PInterval | CD_MM_PInt 
	| CD_MM_ConfigurationDiagram | CD_MM_Connector | CD_MM_Port | CD_MM_CompositionI | CD_MM_BlockI | CD_MM_VTypeRef
    deriving (Read, Show, Eq)

data IntoSysML_CD_MM_Es = CD_MM_ENamed_name | CD_MM_EPInterval_lb | CD_MM_EPInterval_ub | CD_MM_Ecompositions | CD_MM_Eblocks | CD_MM_Econnectors 
	| CD_MM_EConnector_src | CD_MM_EConnector_tgt | CD_MM_EConnector_ftype | CD_MM_EBlockI_ports | CD_MM_ECompositionI_src | CD_MM_ECompositionI_tgt 
	| CD_MM_EVTypeRef_unit | CD_MM_EVTypeRef_base
    deriving (Read, Show, Eq)

show_cd_mm_n nt = drop 6 (show nt)
show_cd_mm_e et = drop 6 (show et)
read_cd_mm x = read ("CD_MM_" ++ x)
