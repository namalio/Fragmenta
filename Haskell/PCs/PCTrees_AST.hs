module PCs.PCTrees_AST (
    Id
    , PCExp
    , Guard
    , Param
    , TOp(..)
    , PCT(..)
    , CT(..)
    , PCTD(..)
    , theCt)
where

import Relations ( Rel )
import ShowUtils(showStrs)

type Id = String 
type PCExp = String 
type Guard = String
type Type = String
type Param = (Id, Type) 

data TOp = OpExtChoice 
  | OpIntChoice 
  | OpSeq Bool 
  | OpParallel [PCExp] 
  | OpInterleave 
  | OpThrow [Id]
  | OpIf Guard 
  deriving(Eq, Show)  

data PCT = Atom Id (Maybe Guard) (Maybe (Id, PCExp)) 
  | OpB TOp PCT PCT 
  | Kappa CT 
  | Ref Id (Maybe Guard) [PCExp] (Rel Id Id)
  | NilT | StopT | SkipT deriving(Eq, Show)

data CT = CT Id [Param] [CT] PCT 
  deriving(Eq, Show)

data PCTD = PCTD Id [CT] 
  deriving(Eq, Show)

theCt :: PCT -> CT
theCt (Kappa ct) = ct 

