module Statecharts.StCs_MM_Names (StCs_AMM_Ns(..), StCs_AMM_Es(..), StCs_CMM_Ns(..), StCs_CMM_Es(..), 
    show_amm_n, show_amm_e, show_cmm_n, show_cmm_e, read_cmm)
where

data StCs_AMM_Ns = AMM_Attribute | AMM_Element | AMM_DepthElement | AMM_Manner | AMM_Definition 
   | AMM_Description | AMM_Model
    deriving (Read, Show, Eq)

data StCs_AMM_Es = AMM_EHas | AMM_EContains | AMM_ERelatedTo | AMM_EAssociatedWith | AMM_EHasDesc
    deriving (Read, Show, Eq)

data StCs_CMM_Ns = CMM_StCModel | CMM_StCDesc | CMM_StartState | CMM_EndState | CMM_MutableState 
   | CMM_HistoryState | CMM_State | CMM_Element | CMM_Name | CMM_Named | CMM_Transition |  CMM_Event 
   | CMM_Guard | CMM_Action | CMM_WExp | CMM_Exp
    deriving (Read, Show, Eq)

data StCs_CMM_Es = CMM_ENamed_name | CMM_EContains | CMM_EHasDesc | CMM_ETransition_event 
   | CMM_ETransition_guard | CMM_ETransition_action | CMM_ETransition_src | CMM_ETransition_tgt 
   | CMM_EWExp_exp
    deriving (Read, Show, Eq)

show_amm_n :: Show a => a -> String
show_amm_n nt = drop 4 (show nt)
show_amm_e :: Show a => a -> String
show_amm_e et = drop 4 (show et)
show_cmm_n :: Show a => a -> String
show_cmm_n nt = drop 4 (show nt)
show_cmm_e :: Show a => a -> String
show_cmm_e et = drop 4 (show et)
read_cmm :: Read a => String -> a
read_cmm x = read ("CMM_" ++ x)

