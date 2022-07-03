---------------------
-- Project: Fragmenta
-- Module: 'ASDParseDrawCommon'
-- Description: Common types and functions used in parsing and drawing
-- Author: Nuno Amálio
--------------------
module IntoSysML.ASDCommon(Name, Exp, Property(..), FlowPort(..), Variable(..), PType(..), VTypeDef(..), VariableKind, 
   ComponentKind, PhenomenaKind, gPNm, gFPNm, gFPPr, gFPMTy)
where

import IntoSysML.ASD_MM_Names

-- Names are represented as strings
type Name = String

-- Expressions are represented as strings
type Exp = String

-- Primitive types
data PType = PReal | PString | PBool | PNat | PInt | PInterval Int Int
  deriving(Eq, Show, Read) 

-- Property: a name, a type id, and an optional initialisation expression
data Property = Property Name Name Exp
   deriving(Eq, Show) 

-- A flowport is either input or output. They have an embedded property; output flow ports have a lists of dependencies (names of input ports)
data FlowPort = InFlowPort Property | OutFlowPort Property [Name]
   deriving(Eq, Show) 

-- Variable kinds: either plain variables or parameters
data VariableKind = Var | Parameter
   deriving(Eq, Show, Read) 

-- A variable has an embedded property and a kind 
data Variable = Variable Property VariableKind 
   deriving(Eq, Show) 

-- Components are either cyber, subsystem or physical
data ComponentKind = Cyber | Subsystem | Physical 
   deriving(Eq, Show, Read) 

-- The phenomena of a compound component, either discrete or continuous
data PhenomenaKind = Discrete | Continuous
   deriving(Eq, Show, Read) 

-- A value type definition is either an enumeration, a structural type, a derived type or a unit type
data VTypeDef = VTypeEnum Name [Name] | VTypeStrt Name [Property] | DType Name PType | UType Name PType Name
   deriving(Eq, Show) 


-- Gets name of a property
gPNm (Property nm _ _) = nm

-- Functions to retrieve name of a flow port
gFPNm (InFlowPort p)    = gPNm p
gFPNm (OutFlowPort p _) = gPNm p

-- Functions to retrieve embedded property of a flow port
gFPPr (InFlowPort p) = p
gFPPr (OutFlowPort p _) = p

-- Gets meta-type of a flow port
gFPMTy (InFlowPort _)    = ASD_MM_InFlowPort
gFPMTy (OutFlowPort _ _) = ASD_MM_OutFlowPort
