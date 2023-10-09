module IntoSysML.AMM_Names (IntoSysML_AMM_Ns(..), IntoSysML_AMM_Es(..), show_amm_n, show_amm_e)
where

data IntoSysML_AMM_Ns = AMM_Feature | AMM_Connector | AMM_Part | AMM_VType | AMM_PElement | AMM_Trait | AMM_ArchitectureDiagram
    deriving (Read, Show, Eq)

data IntoSysML_AMM_Es = AMM_EConsistsOf | AMM_EHas | AMM_EConnector_src | AMM_EConnector_tgt
    deriving (Read, Show, Eq)

show_amm_n nt = drop 4 (show nt)
show_amm_e et = drop 4 (show et)

