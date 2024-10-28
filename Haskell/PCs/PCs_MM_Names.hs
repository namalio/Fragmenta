module PCs.PCs_MM_Names (PCs_AMM_Ns(..), PCs_AMM_Es(..), PCs_CMM_Ns(..), PCs_CMM_Es(..), show_amm_n, show_amm_e, show_cmm_n, show_cmm_e
    , read_cmm)
where

data PCs_AMM_Ns = AMM_Attribute | AMM_Definition
    | AMM_Connector
    | AMM_Node
    | AMM_Trait
    | AMM_PCDef
    | AMM_Element
    deriving (Read, Show, Eq)

data PCs_AMM_Es = AMM_EConnector_tgt | AMM_EContains
    | AMM_EHas
    | AMM_EStarts
    | AMM_EConnector_src
    deriving (Read, Show, Eq)

data PCs_CMM_Ns = CMM_Node | CMM_PDefinition
    | CMM_PNamed
    | CMM_EnumType
    | CMM_EnumVal
    | CMM_PParameter
    | CMM_PCType
    | CMM_YesNo
    | CMM_VYes
    | CMM_VNo
    | CMM_Boolean
    | CMM_Integer
    | CMM_Event
    | CMM_Set
    | CMM_Operator
    | CMM_VOpChoice
    | CMM_VOpIntChoice
    | CMM_VOpParallel
    | CMM_VOpIf
    | CMM_VOpInterleave
    | CMM_VOpThrow
    | CMM_OpQuantifiedOp
    | CMM_PNode2
    | CMM_PBindable3
    | CMM_PAction3
    | CMM_PName2
    | CMM_PYesNo
    | CMM_PGuarded2
    | CMM_Reference
    | CMM_Renaming
    | CMM_PConnector2
    | CMM_AfterC
    | CMM_DefinesC
    | CMM_PAction4
    | CMM_PCompound2
    | CMM_PYesNo2
    | CMM_PConnector4
    | CMM_PCombination
    | CMM_PAction5
    | CMM_PGuarded3
    | CMM_BMainIfC
    | CMM_BElseC
    | CMM_BJumpC
    | CMM_BranchC
    | CMM_PYesNo3
    | CMM_PTargetOfRef
    | CMM_PReference
    | CMM_PBindable4
    | CMM_PConnector3
    | CMM_ReferenceC
    | CMM_PCompound
    | CMM_PStartN
    | CMM_StartC
    | CMM_PConnector
    | CMM_Combination
    | CMM_Skip
    | CMM_Stop
    | CMM_PBindable2
    | CMM_POperator
    | CMM_PAction2
    | CMM_PNode
    | CMM_ValueExp
    | CMM_ExpSingle
    | CMM_ExpSet
    | CMM_TxtExp
    | CMM_PGuarded
    | CMM_PAtom
    | CMM_PBindable
    | CMM_POpQuantifiedOp
    | CMM_PName
    | CMM_PAction
    | CMM_PNamedNode2
    | CMM_QuantifiedOp
    | CMM_Parameter
    | CMM_Bindable
    | CMM_Guarded
    | CMM_TargetOfRef
    | CMM_Action
    | CMM_Guard
    | CMM_Atom
    | CMM_Compound
    | CMM_Import
    | CMM_PNamed2
    | CMM_PNamedNode
    | CMM_Definition
    | CMM_StartN
    | CMM_Name
    | CMM_Connector
    | CMM_Named
    | CMM_PCDef
    | CMM_NamedNode
    deriving (Read, Show, Eq)

data PCs_CMM_Es = CMM_EenumVals | CMM_Ename
    | CMM_EContainsNs
    | CMM_EContainsCs
    | CMM_EContainsDs
    | CMM_EStarts
    | CMM_Eparams
    | CMM_Eguard
    | CMM_Evar
    | CMM_EvExps
    | CMM_EvExp
    | CMM_EopOfQuantifiedOp
    | CMM_Eexps
    | CMM_ED1
    | CMM_ED2
    | CMM_ECombination_op
    | CMM_EStartSrc
    | CMM_EStartTgt
    | CMM_EReferenceCSrc
    | CMM_EReferenceCTgt
    | CMM_EReferenceC_hidden
    | CMM_EBranchCTgt
    | CMM_EBranchCSrc
    | CMM_EAfterC_copen
    | CMM_EDefinesCSrc
    | CMM_EDefinesCTgt
    | CMM_EAfterCTgt
    | CMM_EAfterCSrc
    | CMM_ERenamings
    | CMM_EReference_inner
    | CMM_EReference_name
    | CMM_Etype
    | CMM_EsetOf
    deriving (Read, Show, Eq)

show_mm_n :: Show a => a -> String
show_mm_n nt = drop 4 (show nt)
show_amm_n :: PCs_AMM_Ns -> String
show_amm_n nt = show_mm_n nt
show_mm_e :: Show a => a -> String
show_mm_e et = drop 4 (show et)
show_amm_e :: PCs_AMM_Es -> String
show_amm_e et = show_mm_e et
show_cmm_n :: PCs_CMM_Ns -> String
show_cmm_n nt = show_mm_n nt
show_cmm_e :: PCs_CMM_Es -> String
show_cmm_e et = show_mm_e et
read_cmm :: Read a => String -> a
read_cmm x = read ("CMM_" ++ x)

