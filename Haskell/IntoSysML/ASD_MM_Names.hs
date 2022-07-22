module IntoSysML.ASD_MM_Names (IntoSysML_ASD_MM_Ns(..), IntoSysML_ASD_MM_Es(..), show_asd_mm_n, show_asd_mm_e, read_asd_mm)
where

data IntoSysML_ASD_MM_Ns = ASD_MM_Named | ASD_MM_Name | ASD_MM_PNat | ASD_MM_PReal | ASD_MM_PBool | ASD_MM_PString | ASD_MM_PType | ASD_MM_PInterval 
   | ASD_MM_PInt | ASD_MM_AType | ASD_MM_Composition | ASD_MM_StructureDiagram | ASD_MM_Block | ASD_MM_ValueType | ASD_MM_var | ASD_MM_parameter 
   | ASD_MM_VariableKind | ASD_MM_Exp | ASD_MM_Field | ASD_MM_FieldI |ASD_MM_Variable | ASD_MM_TypedName | ASD_MM_Initialisable | ASD_MM_Port | ASD_MM_OutFlowPort 
   | ASD_MM_InFlowPort | ASD_MM_APIPort | ASD_MM_DType | ASD_MM_UnitType | ASD_MM_Enumeration | ASD_MM_Literal | ASD_MM_StrtType | ASD_MM_Interface 
   | ASD_MM_Operation | ASD_MM_System | ASD_MM_BElement | ASD_MM_cyber 
   | ASD_MM_subsystem | ASD_MM_physical | ASD_MM_Component | ASD_MM_ComponentKind | ASD_MM_discrete | ASD_MM_continuous | ASD_MM_Compound | ASD_MM_PhenomenaKind 
   | ASD_MM_MultCompSrc | ASD_MM_optional | ASD_MM_compulsory
   | ASD_MM_Mult | ASD_MM_MultValMany | ASD_MM_MultValNum | ASD_MM_Nat | ASD_MM_MultSingle | ASD_MM_MultRange | ASD_MM_MultVal
   deriving (Read, Show, Eq)

data IntoSysML_ASD_MM_Es = ASD_MM_ENamed_name | ASD_MM_EPInterval_lb | ASD_MM_EPInterval_ub | ASD_MM_EHasBlocks | ASD_MM_EHasVTypes | ASD_MM_EHasCompositions 
   | ASD_MM_EVariable_kind | ASD_MM_ETypedName_type | ASD_MM_EInitialisable_init | ASD_MM_EOutFlowPort_depends | ASD_MM_EAPIPort_kind 
   | ASD_MM_EInterface_ops | ASD_MM_EOperation_return | ASD_MM_EOperation_params
   | ASD_MM_EDType_base | ASD_MM_EUnitType_unit | ASD_MM_EHasLiterals | ASD_MM_EStrtType_fields | ASD_MM_EBlock_ports | ASD_MM_EComponent_vars 
   | ASD_MM_EComponent_kind | ASD_MM_ECompound_phenomena | ASD_MM_EComposition_src | ASD_MM_EComposition_tgt | ASD_MM_EComposition_srcM | ASD_MM_EComposition_tgtM 
   | ASD_MM_EMultRange_lb | ASD_MM_EMultValNum_n | ASD_MM_EMultSingle_val | ASD_MM_EMultRange_ub | ASD_MM_EHasSystem | ASD_MM_EComposition_tgt_sys 
   | ASD_MM_EComposition_src_elem
   deriving (Read, Show, Eq)

show_asd_mm_n nt = drop 7 (show nt)
show_asd_mm_e et = drop 7 (show et)

read_asd_mm :: String -> IntoSysML_ASD_MM_Ns
read_asd_mm x = read ("ASD_MM_" ++ x)
