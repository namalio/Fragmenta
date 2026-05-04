module PCs.PCTreesAST (
    PCTTypeD(..)
    , read_pctty
    , read_opctty
    , Param(..)
    , cParam
    , gParamId
    , gParamTyD
    , TOp(..)
    , PT(..)
    , DTDef(..)
    , PCTD(..)
    , ROp(..)
    , VTerm(..)
    , gPTs)
where

import Sets
import Relations ( Rel )
import ShowUtils
  (showStrs
  )
import PCs.TxtExpAST 
import PCs.Common(Id)
import TheNil


-- A PCT type designator — int, bool, some custom datatype, or some set of some type
data PCTTypeD 
  = Int 
  | Bool 
  | DT Id
  | SetT PCTTypeD 
  deriving (Eq)

read_pctty :: String -> PCTTypeD
read_pctty "Int" = Int
read_pctty "Bool" = Bool
read_pctty ('D':'t':'_':rest) = DT rest
read_pctty ('S':'e':'t':'_':rest) = SetT . read_pctty $ rest
--read_pctty ('D':'t':'_':rest) = DT rest
--read_pctty ('S':'e':'t':'_':rest) = DT rest

read_opctty :: Maybe String -> Maybe PCTTypeD
read_opctty Nothing = Nothing
read_opctty (Just s) = Just $ read_pctty s

instance Show PCTTypeD where
  show Int = "Int"
  show Bool = "Bool"
  show (DT id) = strip id 
    where strip('D':'t':'_':rest) = rest
          strip s = s
  show (SetT t) = "Set " ++ show t

-- A parameter: an id and an optional type designator
data Param = Param Id (Maybe PCTTypeD)
  deriving (Eq)

cParam::Id->Maybe PCTTypeD->Param
cParam = Param

gParamId::Param->Id
gParamId(Param id _) = id

gParamTyD::Param->Maybe PCTTypeD
gParamTyD(Param _ otd) = otd

instance Show Param where
  show (Param nm ty) = nm ++ (if isSomething ty then  " : " ++ show (the ty) else "")

-- A Guard is an expression
type G = Exp

-- A Tree operator
data TOp 
  = OpExtChoice -- external choice
  | OpIntChoice -- internal choice
  | OpSeq Bool -- Sequential composition (boolean indicates whether it is open or closed)
  | OpParallel [Exp] -- parallel operator
  | OpInterleave -- interleaving
  | OpThrow [Exp] -- throw
  | OpIf G -- Expression represents the if's guard 
  deriving(Eq, Show)  

-- A replicated operator
data ROp = OpRExtChoice Id PCTTypeD
  | OpRIntChoice Id PCTTypeD
  deriving(Eq, Show)  

-- Process Trees (PTs)
data PT 
  = Atom Exp (Maybe G)  -- An atom is an expression and a guard
  | OpB TOp PT PT       -- An operator which combines PTs
  | Kappa Id [Param] [PT] PT  -- A process definition
  | OpKappa Id ROp PT 
  | Rho Id (Maybe G) [Exp] (Rel Id Id) -- identifier, optional guard, list of PCEs, renaming
  | NilT | StopT | SkipT 
  deriving(Eq, Show)

-- A value term of a data type definition: an identifier followed by type designators
data VTerm = VTerm Id [PCTTypeD]
  deriving(Eq, Show)
-- A data type definition: an identifier and a set of value terms 
data DTDef = DTDef Id [VTerm]
  deriving(Eq, Show)

-- A PC tree definition
data PCTD = PCTD Id [DTDef] [PT] 
  deriving(Eq, Show)

gPTs::PCTD->[PT]
gPTs (PCTD _ _ pts) = pts 