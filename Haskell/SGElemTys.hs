
------------------
-- Project: PCs/Fragmenta
-- Module: 'SGElemTy'
-- Description: Definitions related to the different types of SG elements (nodes or edges)
-- Author: Nuno Amálio
-----------------
module SGElemTys (SGNTy(..), SGETy(..), SGED(..), sgnty_set, sgety_set) where

import Sets ( set, Set )

data SGNTy = Nnrml | Nabst | Nprxy | Nenum | Nval | Nvirt
   deriving (Eq, Show)

sgnty_set :: Set SGNTy
sgnty_set = set [Nnrml, Nabst, Nprxy, Nenum, Nval, Nvirt]

-- The association edge direction
data SGED = Dbi | Duni  deriving (Eq, Show)

data SGETy = Einh | Ecomp SGED | Erel SGED  | Eder | Epath deriving (Show, Eq)

sgety_set :: Set SGETy
sgety_set = set $ [Einh, Eder, Epath] ++ [e d | e<-[Ecomp, Erel], d<-[Duni, Dbi]]

-- Order which dictates allowed inheritance relations 
nty_lti:: SGNTy->SGNTy->Bool
nty_lti nt1 nt2 = nt1 /= Nprxy && (nt2 /= Nval) -- proxies may not inherit and values may not be inherited
    && (nt2 == Nprxy  || nt1 == Nnrml -- removed previous 1st disjuct: (nt2 `elem` [Nenum, Nvirt] && nt1 == Nval) || 
       || (nt1 == Nenum && nt2 == Nvirt) || (set [nt1, nt2] <= set [Nvirt, Nabst]))
    

-- Ordering underpinning the compliance of refinement relations; says which node types can be refinement related
nty_leqr:: SGNTy->SGNTy->Bool
nty_leqr nt1 nt2 = nt1 == nt2 || nt1 == Nprxy || (nt2 `elem` [Nnrml, Nvirt] && nt1 `elem` [Nnrml, Nvirt, Nabst]) 
   || nt2 == Nnrml || (nt1 == Nnrml && nt2 == Nprxy)
--nty_leqr _ Nnrml    = True
--nty_leqr _ Nopt     = True
--nty_leqr Nprxy _    = True
--nty_leqr nt Nabst   = nt `elem` [Nnrml, Nvirt]
--nty_leqr nt Nvirt   = nt `elem` [Nnrml, Nabst]
--nty_leqr Nnrml nt   = nt `elem` [Nprxy]
--nty_leqr nt1 nt2    = nt1 == nt2 

instance Ord SGNTy where
    (<) :: SGNTy -> SGNTy -> Bool
    (<) = nty_lti
    (<=) :: SGNTy -> SGNTy -> Bool
    (<=) = nty_leqr

--instance Eq SGETy where
--    (==) :: SGETy -> SGETy -> Bool
--    (==) (Erel _) (Erel _)   = True
--    (==) (Ecomp _) (Ecomp _) = True
--    (==) Einh Einh           = True
--    (==) Eder Eder           = True
--    (==) Epath Epath         = True
--    (==) _ _                 = False
--    (==) ety1 ety2             = ety1 == ety2
    
ety_eq :: SGETy -> SGETy -> Bool
ety_eq (Erel _) (Erel _)   = True
ety_eq (Ecomp _) (Ecomp _) = True
ety_eq ety1 ety2           = ety1 == ety2

-- Relation used for refinement: wander edges are refined by any non-inheritance edges
--ety_leq et1 Ewander  = True
--ety_leq Eder et2     = et2 `elem` [e d | e<-[Ecomp, Erel], d<-[Duni, Dbi]]
--ety_leq :: SGETy -> SGETy -> Bool
--ety_leq (Ecomp _) (Erel Dbi)  = True
--ety_leq (Ecomp Duni) (Erel Duni)  = True
--ety_leq et1 et2      = (not $ set [et1, et2] <= set [Einh, Eder, Epath]) && (et1 `ety_eq` et2) 

instance Ord SGETy where
    (<=) :: SGETy -> SGETy -> Bool
    (<=) (Ecomp _) (Erel Dbi)      = True
    (<=) (Ecomp Duni) (Erel Duni)  = True
    (<=) ety1 ety2                 = (not $ set [ety1, ety2] <= set [Einh, Eder, Epath]) && (ety1 `ety_eq` ety2) 
    --(<=) = ety_leq