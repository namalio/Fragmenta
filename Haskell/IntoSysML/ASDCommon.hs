---------------------
-- Project: Fragmenta
-- Module: 'ASDParseDrawCommon'
-- Description: Common types and functions used in parsing and drawing
-- Author: Nuno Amálio
--------------------
module IntoSysML.ASDCommon(
   Name
   , Exp
   , AType(..)
   , TypedName(..)
   , Port(..)
   , Variable(..)
   , Initialisable(..)
   , FieldI(..)
   , PType(..)
   , Operation (..)
   , VTypeDef(..)
   , MultVal(..)
   , Mult(..)
   , MultCompSrc(..)
   , VariableKind(..)
   , ComponentKind
   , PhenomenaKind
   , Composition(..)
   , APIPortKind(..)
   , gTNNm 
   , gITNNm
   , gTNTy
   , gITNTy
   , gITNInit
   , gPoITN
   , gPoNm
   , gPoMTy
   , gPoDeps
   , gOpNm
   , gOpPs
   , gOpRet
   , gCNm
   , gCSrc
   , gCTgt
   , gCSrcM
   , gCTgtM
   , blockId
   , compositionId
   , base_ptypes
   , is_ATy_a_Pty
   , gATyPTy
   , gVarITN
   , varId
   , tnId
   , vtnId)
where

import IntoSysML.ASD_MM_Names

-- Names are represented as strings
type Name = String

-- Expressions are represented as strings
type Exp = String

-- A mulplicity value is either a natural number or many ('*') 
data MultVal = MultN Int | MMany
   deriving(Eq, Show) 

data Mult =  MultS MultVal | MultR Int MultVal
   deriving(Eq, Show) 

data MultCompSrc = Optional | Compulsory
   deriving(Eq, Show, Read) 

-- Primitive types
data PType = PReal | PString | PBool | PNat | PInt | PInterval Int Int
  deriving(Eq, Show, Read) 

base_ptypes :: [String]
base_ptypes = ["Real", "String", "Bool", "Nat", "Int"]

data AType = ATypeP PType | ATypeId Name
   deriving(Eq, Show, Read) 

-- Typed name: a name and a type, and an optional initialisation expression
data TypedName = TypedName Name AType
   deriving(Eq, Show, Read) 

-- An Initialisable: a name and a type, and an optional initialisation expression
data Initialisable = Initialisable Name AType Exp
   deriving(Eq, Show, Read) 

-- API Port kind: either requires or provides
data APIPortKind = Requires | Provides
   deriving(Eq, Show, Read) 

-- A port is either an input or output flowport, or an API port. They have an embedded property; output flow ports have a lists of dependencies (names of input ports)
data Port = InFlowPort Initialisable | OutFlowPort Initialisable [Name] | APIPort Initialisable APIPortKind
   deriving(Eq, Show) 

-- Variable kinds: either plain variables or parameters
data VariableKind = Var | Parameter
   deriving(Eq, Show, Read) 

-- A variable has  a name a type, an initialisation expression and a kind 
data Variable = Variable Initialisable VariableKind 
   deriving(Eq, Show) 

-- An initialisable field has  an initialisable, itself made uo of a triple 
data FieldI = FieldI Initialisable
   deriving(Eq, Show) 

-- Components are either cyber, subsystem or physical
data ComponentKind = Cyber | Subsystem | Physical 
   deriving(Eq, Show, Read) 

-- The phenomena of a compound component, either discrete or continuous
data PhenomenaKind = Discrete | Continuous
   deriving(Eq, Show, Read) 

data Operation = Operation Name [TypedName] AType
   deriving(Eq, Show, Read) 

-- A value type definition is either an enumeration, a structural type, a derived type or a unit type
data VTypeDef = VTypeEnum Name [Name] | VTypeStrt Name [FieldI] | DType Name PType | UType Name PType Name | Interface Name [Operation]
   deriving(Eq, Show) 

-- A Composition
data Composition = Composition Name Name Name MultCompSrc Mult
   deriving(Eq, Show) 

is_ATy_a_Pty :: AType -> Bool
is_ATy_a_Pty (ATypeP _) = True
is_ATy_a_Pty _ = False

gATyPTy (ATypeP pt) = pt 

-- Gets name of a property
gTNNm (TypedName nm _) = nm
-- Gets type of a property
gTNTy (TypedName _ ty) = ty

-- Gets initialisation of an initialisable
gITNNm (Initialisable nm _ _) = nm 
gITNTy (Initialisable _ ty _) = ty 
gITNInit (Initialisable _ _ ie) = ie

-- Functions to retrieve name of a port
gPoNm :: Port -> Name
gPoNm (InFlowPort itn)    = gITNNm itn
gPoNm (OutFlowPort itn _) = gITNNm itn
gPoNm (APIPort itn _)     = gITNNm itn

-- Functions to retrieve embedded inisiable typed name of a port
gPoITN :: Port -> Initialisable
gPoITN (InFlowPort itn)    = itn
gPoITN (OutFlowPort itn _) = itn
gPoITN (APIPort itn _)     = itn

gPoDeps :: Port -> [Name]
gPoDeps (OutFlowPort _ ds) = ds

-- Gets meta-type of a flow port
gPoMTy :: Port -> IntoSysML_ASD_MM_Ns
gPoMTy (InFlowPort _)    = ASD_MM_InFlowPort
gPoMTy (OutFlowPort _ _) = ASD_MM_OutFlowPort
gPoMTy (APIPort _ _) = ASD_MM_APIPort

-- Accessor functions of an Pperation
gOpNm :: Operation -> Name
gOpNm (Operation nm _ _) = nm
gOpPs :: Operation -> [TypedName]
gOpPs (Operation _ ps _)  = ps
gOpRet :: Operation -> AType
gOpRet (Operation _ _ aty)  = aty

-- Functions to retrieve components of a composition
gCNm :: Composition -> Name
gCNm (Composition nm _ _ _ _)   = nm
gCSrc :: Composition -> Name
gCSrc (Composition _ s _ _ _)   = s
gCTgt :: Composition -> Name
gCTgt (Composition _ _ t _ _)   = t
gCSrcM :: Composition -> MultCompSrc
gCSrcM (Composition _ _ _ sm _) = sm
gCTgtM :: Composition -> Mult
gCTgtM (Composition _ _ _ _ tm) = tm

-- Gets a variable's Initialisable
gVarITN :: Variable -> Initialisable
gVarITN (Variable itn _) = itn

-- Identifier of a block node in a graph
blockId::String ->String
blockId nm = nm ++ "_Block"

compositionId::String->String
compositionId nm = nm ++ "_Composition"

-- Identifiers in the instance graph
varId::String->String->String
varId cnm nm = cnm ++ "_" ++ nm ++ "_Var"
tnId::String->String->String
tnId cnm nm = cnm ++ "_" ++ nm ++ "_TN"
vtnId::String->String->IntoSysML_ASD_MM_Ns->String
vtnId cnm nm ASD_MM_Variable = varId cnm nm
vtnId cnm nm _ = tnId cnm nm

