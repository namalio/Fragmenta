module PCs.PCTreesAST 
    (TOp(..)
    , PT(..)
    , DTDef(..)
    , PCTD(..)
    , ROpT(..)
    , ROp(..)
    , VTerm(..)
    , gDTDs
    , gPTs
    , gIdVT
    , gIdOfRop)
where

import Sets
import Relations ( Rel )
import ShowUtils
  (showStrs
  )
import PCs.TxtExpAST 
import PCs.Common
  (Id
  , Param
  , PCTypeD
  , PCTypeE)
import TheNil



--data PCTTypeD 
--  = Int 
--  | Bool 
--  | DT Id
--  | SetT PCTTypeD 
--  deriving (Eq)


--read_pctty s = fail $ "Unexpected type designator string: " ++ s
--read_pctty ('D':'t':'_':rest) = DT rest
--read_pctty ('S':'e':'t':'_':rest) = DT rest

-- A parameter: an id and an optional type designator
--data Param = Param Id (Maybe PCType)
--  deriving (Eq)

-- A Guard is an expression
type G = Exp

-- A Tree operator
data TOp 
  = OpExtChoice -- external choice
  | OpIntChoice -- internal choice
  | OpSeq -- Sequential composition 
  | OpParallel [Exp] -- parallel operator
  | OpInterleave -- interleaving
  | OpThrow [Exp] -- throw
  | OpIf G -- Expression represents the if's guard 
  deriving(Eq, Show)  

-- A replicated operator term
data ROpT 
  = OpRExtChoice -- replicated external choice
  | OpRIntChoice -- internal internal choice
  deriving(Eq, Show)

-- A replicated operator data structure
data ROp = ROp ROpT Id PCTypeE
  deriving(Eq, Show)  

gIdOfRop::ROp->Id
gIdOfRop (ROp _ id _) = id

-- Process Trees (PTs)
data PT 
  = Atom Exp (Maybe G)  -- An atom is an expression and a guard
  | OpB TOp PT PT       -- An operator which combines PTs
  | Kappa Id [Param] [PT] PT  -- A process definition
  | OpKappa ROp PT 
  | Rho Id (Maybe G) [Exp] (Rel Id Id) -- identifier, optional guard, list of PCEs, renaming
  | NilT 
  | StopT 
  | SkipT 
  deriving(Eq, Show)

-- A value term of a data type definition: an identifier followed by type designators
data VTerm = VTerm Id [PCTypeD]
  deriving(Eq, Show)
-- A data type definition: an identifier and a set of value terms 
data DTDef = DTDef Id [VTerm]
  deriving(Eq, Show)

-- A PC tree definition
data PCTD = PCTD Id [DTDef] [Param] [PT] 
  deriving(Eq, Show)

gDTDs::PCTD->[DTDef]
gDTDs (PCTD _ dtds _ _) = dtds 

gPTs::PCTD->[PT]
gPTs (PCTD _ _ _ pts) = pts 

gIdVT::VTerm->Id
gIdVT (VTerm id tds) = id 