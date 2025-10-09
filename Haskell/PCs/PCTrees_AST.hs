module PCs.PCTrees_AST (
    PCE(..)
    , PCTTypeD(..)
    , read_pctty
    , read_opctty
    , Param(..)
    , cParam
    , gParamId
    , gParamTyD
    , TOp(..)
    , PT(..)
    , PD(..)
    , DTDef(..)
    , PCTD(..)
    , ROp(..)
    , thePD
    , idPD
    , gPDs)
where

import Sets
import Relations ( Rel )
import ShowUtils(showStrs)
import PCs.PCTrees_Exp 
import PCs.PCsCommon(Id)
import TheNil


-- A PCT type designator — int, bool, or some datatype
data PCTTypeD 
  = Int 
  | Bool 
  | DT Id
  deriving (Eq)


read_pctty :: String -> PCTTypeD
read_pctty "Integer" = Int
read_pctty "Bool" = Bool
read_pctty id = DT id

read_opctty :: Maybe String -> Maybe PCTTypeD
read_opctty Nothing = Nothing
read_opctty (Just s) = Just $ read_pctty s

instance Show PCTTypeD where
  show Int = "Int"
  show Bool = "Bool"
  show (DT id) = "DT " ++ id 

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

-- The Guard type (an expression)
type G = PCE

-- A Tree operator
data TOp 
  = OpExtChoice -- external choice
  | OpIntChoice -- internal choice
  | OpSeq Bool -- Sequential composition (boolean indicates whether it is open or closed)
  | OpParallel [PCE] -- parallel operator
  | OpInterleave -- interleaving
  | OpThrow [PCE] -- throw
  | OpIf G -- Expression represents the if's guard 
  deriving(Eq, Show)  

-- A replicated operator
data ROp = OpRExtChoice Id PCTTypeD
  | OpRIntChoice Id PCTTypeD
  deriving(Eq, Show)  

-- Process Trees
data PT 
  = Atom PCEAtom (Maybe G)  -- An atom is an atomic expression and a guard
  | OpB TOp PT PT -- An operator that combines process trees
  | Kappa PD -- An inner process definition
  | OpKappa Id ROp PT 
  | Rho Id (Maybe G) [PCE] (Rel Id Id) -- identifier, optional guard, list of PCEs, renaming
  | NilT | StopT | SkipT 
  deriving(Eq, Show)

-- Process definition 
data PD = PD Id [Param] [PT] PT 
  deriving(Eq, Show)

-- A data type definition: an identifier and a set of literals
data DTDef = DTDef Id (Set Id) 
  deriving(Eq, Show)

-- A PC tree definition
data PCTD = PCTD Id [DTDef] [PD] 
  deriving(Eq, Show)

thePD :: PT -> PD
thePD (Kappa pd) = pd
thePD pt = error $ "Unexpected error while processing a PT:" ++ (show pt)

idPD::PD->Id
idPD (PD id _ _ _) = id

gPDs::PCTD->[PD]
gPDs (PCTD _ _ pds) = pds 