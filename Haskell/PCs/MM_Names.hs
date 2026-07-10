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
    | AMM_DiagDef
    | AMM_Element
    deriving (Read, Show, Eq)

data PCs_AMM_Es
    = AMM_Ectgt 
    | AMM_Econtains
    | AMM_Ehas
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
    | CMM_PWParameters
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
    | CMM_TxtExp
    | CMM_PNode
    | CMM_PAction2
    | CMM_PCombinable
    | CMM_PTxtExp2
    | CMM_Stop
    | CMM_Skip
    | CMM_Combination
    | CMM_Bindable
    | CMM_PConnector
    | CMM_StartC
    | CMM_PStartN
    | CMM_PStartOfPC2
    | CMM_ReferenceC
    | CMM_PConnector3
    | CMM_PBindable2
    | CMM_PReference
    | CMM_PRefTarget
    | CMM_PYesNo3
    | CMM_PAtom2
    | CMM_PConnector5
    | CMM_PReference2
    | CMM_PName4
    | CMM_PCustom
    | CMM_PDefinition2
    | CMM_BranchC
    | CMM_BJumpC
    | CMM_BElseC
    | CMM_BMainIfC
    | CMM_PQuantification
    | CMM_PTxtExp3
    | CMM_PGuarded3
    | CMM_PAction5
    | CMM_PCombinable2
    | CMM_PConnector4
    | CMM_PProcess2
    | CMM_PAction4
    | CMM_DefinesC
    | CMM_AfterC
    | CMM_PConnector2
    | CMM_Renaming
    | CMM_Reference
    | CMM_PStartOfPC
    | CMM_PGuarded2
    | CMM_PYesNo
    | CMM_PName3
    | CMM_PAction3
    | CMM_PBindable
    | CMM_PNode2
    | CMM_Combinable
    | CMM_TyTxtExp
    | CMM_PTxtExp
    | CMM_PGuarded
    | CMM_POperator
    | CMM_POpQuantifiedOp
    | CMM_PName2
    | CMM_PAction
    | CMM_PNamedNode3
    | CMM_Quantification
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
    | CMM_PWParameters2
    | CMM_Import
    | CMM_Atom
    | CMM_Process
    | CMM_PName
    | CMM_PNamedNode2
    | CMM_Parameter
    | CMM_WParameters
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
    | CMM_Evar
    | CMM_Eop
    | CMM_EDQOp
    | CMM_Eguard
    | CMM_Eqtexp
    | CMM_EReference_name
    | CMM_EReference_inner
    | CMM_ERenamings
    | CMM_ERenaming_new
    | CMM_ERenaming_old
    | CMM_EDDCSrc
    | CMM_EDDCTgt
    | CMM_EDACSrc
    | CMM_EDACTgt
    | CMM_EDIf
    | CMM_EDBCSrc
    | CMM_EDBCTgt
    | CMM_EDBCSrc2
    | CMM_EDDTy
    | CMM_EDRt
    | CMM_EDAt
    | CMM_EDRCTgt
    | CMM_EDRCSrc
    | CMM_EReferenceC_hidden
    | CMM_EDSCTgt
    | CMM_EDSCSrc
    | CMM_Earguments
    | CMM_Eexp
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

