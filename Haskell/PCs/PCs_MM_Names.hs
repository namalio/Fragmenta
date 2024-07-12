module PCs.PCs_MM_Names (PCs_AMM_Ns(..), PCs_AMM_Es(..), PCs_CMM_Ns(..), PCs_CMM_Es(..)
    , show_amm_n
    , show_amm_e
    , show_cmm_n
    , show_cmm_e
    , read_cmm)
where

data PCs_AMM_Ns = AMM_Connector | AMM_Node | AMM_Trait | AMM_PCDef | AMM_Element | AMM_Attribute
    deriving (Read, Show, Eq)

data PCs_AMM_Es = AMM_EContains | AMM_EHas | AMM_EStarts | AMM_EConnector_src | AMM_EConnector_tgt
    deriving (Read, Show, Eq)

data PCs_CMM_Ns = CMM_PNamedNode | CMM_PNamed | CMM_Import | CMM_Compound | CMM_Atom | CMM_Guard | CMM_Action 
    | CMM_Parameterised | CMM_TargetOfRef | CMM_Guarded | CMM_Parameter | CMM_PAtom | CMM_PParameter 
    | CMM_AnyExp | CMM_Operator | CMM_VOpChoice | CMM_VOpIntChoice | CMM_VOpParallel | CMM_VOpIf 
    | CMM_VOpInterleave 
    | CMM_VOpThrow | CMM_PConnector | CMM_StartC | CMM_PStartN | CMM_PCompound | CMM_ReferenceC | CMM_PConnector3 
    | CMM_PParameterised3 | CMM_PReference | CMM_PTargetOfRef | CMM_PYesNo3 | CMM_BranchC | CMM_BJumpC | CMM_BElseC 
    | CMM_BMainIfC | CMM_PGuarded2 | CMM_PAction4 | CMM_PCombination | CMM_PConnector4 | CMM_PYesNo2 
    | CMM_PCompound2 | CMM_PAction3 | CMM_DefinesC | CMM_AfterC | CMM_PConnector2 | CMM_Renaming | CMM_Reference 
    | CMM_PGuarded | CMM_PYesNo | CMM_PName | CMM_PAction2 | CMM_PParameterised2 | CMM_PNode2 | CMM_Combination 
    | CMM_Skip | CMM_Stop 
    | CMM_POperator | CMM_PAction | CMM_PParameterised | CMM_PNode | CMM_VNo | CMM_VYes | CMM_YesNo | CMM_StartN 
    | CMM_Name | CMM_Connector | CMM_Named | CMM_PCDef | CMM_NamedNode | CMM_Node
    deriving (Read, Show, Eq)

data PCs_CMM_Es = CMM_Ename | CMM_EContainsNs | CMM_EContainsCs | CMM_EStarts | CMM_ECombination_op | CMM_EReference_name 
    | CMM_EReference_inner | CMM_ERenamings | CMM_EAfterCSrc | CMM_EAfterCTgt | CMM_EDefinesCTgt | CMM_EDefinesCSrc 
    | CMM_EAfterC_copen | CMM_EBranchCSrc | CMM_EBranchCTgt | CMM_EReferenceC_hidden | CMM_EReferenceCTgt 
    | CMM_EReferenceCSrc | CMM_EStartTgt | CMM_EStartSrc | CMM_EatSet | CMM_EatVal | CMM_EAtomExp | CMM_EHasGuard 
    | CMM_EHasParams
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

