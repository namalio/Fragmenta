module PCs.MM_Names
    ( PCs_AMM_Ns(..)
    , PCs_AMM_Es(..)
    , PCs_CMM_Ns(..)
    ,  PCs_CMM_Es(..)
    , show_amm_n
    , show_amm_e
    , show_cmm_n
    , show_cmm_e
    , read_cmm
    )
where

data PCs_AMM_Ns
    = AMM_Attribute 
    | AMM_Definition
    | AMM_Connector
    | AMM_Node
    | AMM_Trait
    | AMM_PCDef
    | AMM_Element
    deriving (Read, Show, Eq)

data PCs_AMM_Es
    = AMM_Ectgt 
    | AMM_Econtains
    | AMM_Ehas
    | AMM_Estarts
    | AMM_Ecsrc
    deriving (Read, Show, Eq)

data PCs_CMM_Ns
    = CMM_Named 
    | CMM_Node
    | CMM_NamedNode
    | CMM_PCDef
    | CMM_Connector
    | CMM_StartN
    | CMM_Definition
    | CMM_PNamed
    | CMM_PNamed2
    | CMM_PTyped
    | CMM_PNamed3
    | CMM_PPCType
    | CMM_YesNo
    | CMM_VYes
    | CMM_VNo
    | CMM_Boolean
    | CMM_Integer
    | CMM_Event
    | CMM_Set
    | CMM_Custom
    | CMM_PDefinition
    | CMM_PWExp
    | CMM_EnumType
    | CMM_EnumTerm
    | CMM_Quantification
    | CMM_PNamedNode3
    | CMM_PAction
    | CMM_PName2
    | CMM_POpQuantifiedOp
    | CMM_PWExp3
    | CMM_PGuarded
    | CMM_TxtExp
    | CMM_Combinable
    | CMM_PNode2
    | CMM_PBindable
    | CMM_PAction4
    | CMM_PName3
    | CMM_PYesNo
    | CMM_PGuarded2
    | CMM_PStartOfPC
    | CMM_Reference
    | CMM_Renaming
    | CMM_PConnector2
    | CMM_AfterC
    | CMM_DefinesC
    | CMM_PAction5
    | CMM_PProcess2
    | CMM_PYesNo2
    | CMM_PConnector4
    | CMM_PCombinable2
    | CMM_PAction6
    | CMM_PGuarded4
    | CMM_PTxtExp2
    | CMM_PQuantification
    | CMM_BMainIfC
    | CMM_BElseC
    | CMM_BJumpC
    | CMM_BranchC
    | CMM_PDefinition2
    | CMM_PCustom
    | CMM_PName4
    | CMM_PReference2
    | CMM_PConnector5
    | CMM_PAtom2
    | CMM_PYesNo3
    | CMM_PRefTarget
    | CMM_PReference
    | CMM_PBindable2
    | CMM_PConnector3
    | CMM_ReferenceC
    | CMM_PStartOfPC2
    | CMM_PStartN
    | CMM_StartC
    | CMM_PConnector
    | CMM_Combination
    | CMM_Skip
    | CMM_Stop
    | CMM_PTxtExp
    | CMM_Bindable
    | CMM_PCombinable
    | CMM_POperator
    | CMM_PAction3
    | CMM_PNode
    | CMM_AnyOf
    | CMM_PAction2
    | CMM_PNamedNode4
    | CMM_PWExp2
    | CMM_OpQuantifiedOp
    | CMM_VOpThrow
    | CMM_VOpInterleave
    | CMM_VOpIf
    | CMM_VOpParallel
    | CMM_VOpIntChoice
    | CMM_VOpExtChoice
    | CMM_Operator
    | CMM_WExp
    | CMM_Guarded
    | CMM_StartOfPC
    | CMM_RefTarget
    | CMM_Action
    | CMM_PParameter
    | CMM_Atom
    | CMM_Process
    | CMM_Import
    | CMM_PName
    | CMM_PNamedNode2
    | CMM_Parameter
    | CMM_Typed
    | CMM_PCType
    | CMM_Name
    deriving (Read, Show, Eq)

data PCs_CMM_Es
    = CMM_EContainsNs 
    | CMM_Ename
    | CMM_Etype
    | CMM_Eparams
    | CMM_Epc_name
    | CMM_Efname
    | CMM_Ername
    | CMM_ECombination_op
    | CMM_Eexps
    | CMM_EDSCSrc
    | CMM_EDSCTgt
    | CMM_EReferenceC_hidden
    | CMM_EDRCSrc
    | CMM_EDRCTgt
    | CMM_EDAt
    | CMM_EDRt
    | CMM_EDDTy
    | CMM_EDBCSrc2
    | CMM_EDBCTgt
    | CMM_EDBCSrc
    | CMM_EDIf
    | CMM_EDACTgt
    | CMM_EDACSrc
    | CMM_EDDCTgt
    | CMM_EDDCSrc
    | CMM_EAfterC_copen
    | CMM_ERenaming_old
    | CMM_ERenaming_new
    | CMM_ERenamings
    | CMM_EReference_inner
    | CMM_EReference_name
    | CMM_Eguard
    | CMM_Eexp
    | CMM_EopOfQuantifiedOp
    | CMM_Evar
    | CMM_Eterms
    | CMM_EsetOf
    | CMM_EStarts
    | CMM_Etgt
    | CMM_Esrc
    | CMM_EContainsDs
    | CMM_EContainsCs
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

