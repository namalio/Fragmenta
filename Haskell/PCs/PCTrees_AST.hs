module PCs.PCTrees_AST (
    PCE(..)
    , PCTTypeD(..)
    , read_opctty
    , Param
    , cParam
    , gParamId
    , gParamTyD
    , TOp(..)
    , PT(..)
    , PDT(..)
    , DTDef(..)
    , PCTD(..)
    , ROp(..)
    , thePDT
    , idPDT)
where

import Sets
import Relations ( Rel )
import ShowUtils(showStrs)
import PCs.PCTrees_Exp 
import PCs.PCsCommon(Id)


-- A PCT type designator (int, bool, or some datatype)
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

-- A parameter: an id and a type designator
data Param = Param Id (Maybe PCTTypeD)
  deriving (Eq)

cParam::Id->Maybe PCTTypeD->Param
cParam = Param

gParamId::Param->Id
gParamId(Param id _) = id

gParamTyD::Param->Maybe PCTTypeD
gParamTyD(Param _ otd) = otd

instance Show Param where
  show (Param nm ty) = nm ++ " : " ++ show ty

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
data ROp = OpRExtChoice Id Id
  | OpRIntChoice Id Id
  deriving(Eq, Show)  

-- Process Trees
data PT 
  = Atom PCEAtom (Maybe G)  -- An atom is an atomic expression and a guard
  | OpB TOp PT PT 
  | Kappa PD
  | OpKappa Id ROp PT 
  | Rho Id (Maybe G) [PCE] (Rel Id Id) -- Optional expression represents guard
  | NilT | StopT | SkipT 
  deriving(Eq, Show)

-- A data type definition: takes an identifier and a set of literals
data DTDef = DTDef Id (Set Id) 
  deriving(Eq, Show)

-- Process definition 
data PD = PD Id [Param] [PDT] PT 
  deriving(Eq, Show)

data PCTD = PCTD Id [DTDef] [PDT] 
  deriving(Eq, Show)

thePDT :: PT -> PDT
thePDT  (Kappa pdt) = pdt

idPDT::PDT->Id
idPDT (PDT id _ _ _) = id