module PCs.PCTrees_AST (
    Id, 
    PCExp, 
    Guard, 
    Param, 
    TOp(..), 
    PCT(..), 
    CT(..), 
    PCTD(..), 
    theCt
)
where

import Relations

type Id = String 
type PCExp = String 
type Guard = String
type Param = String 

data TOp = OpExtChoice | OpIntChoice | OpSeq Bool | OpParallel [Param] | OpInterleave | OpThrow [Param]
  | OpIf Guard deriving(Eq, Show)  
data PCT = Atom Id (Maybe Guard) (Maybe (Id, PCExp)) | OpB TOp PCT PCT 
  | Kappa CT 
  | Ref Id (Maybe Guard) [Param] (Rel Id Id)
  | NilT | StopT | SkipT deriving(Eq, Show)
data CT = CT Id [Param] [CT] PCT 
  deriving(Eq, Show)

data PCTD = PCTD Id [CT] 
  deriving(Eq, Show)

theCt :: PCT -> CT
theCt (Kappa ct) = ct 