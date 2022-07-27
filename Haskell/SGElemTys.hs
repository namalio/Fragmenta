
------------------
-- Project: PCs/Fragmenta
-- Module: 'SGElemTy'
-- Description: Definitions related to the different types of SG elements (nodes or edges)
-- Author: Nuno Amálio
-----------------
module SGElemTys (SGNTy(..), SGETy(..), SGED(..), sgnty_set, sgety_set) where

import Logic
import Sets

data SGNTy = Nnrml | Nabst | Nprxy | Nenum | Nval | Nvirt | Nopt deriving (Eq, Show)

sgnty_set = [Nnrml, Nabst, Nprxy, Nenum, Nval, Nvirt, Nopt]

-- The association edge direction
data SGED = Dbi | Duni  deriving (Eq, Show)

data SGETy = Einh | Ecomp SGED | Erel SGED | Ewander | Erefm | Epath | Edep deriving (Eq, Show)
sgety_set = [Einh, Ewander, Erefm, Epath, Edep] ++ [e d | e<-[Ecomp, Erel], d<-[Duni, Dbi]]

-- Order which dictates allowed inheritance relations 
nty_lti:: SGNTy->SGNTy->Bool
nty_lti nt1 nt2 = (not $ nt1 `elem` [Nenum, Nprxy]) && nt2 /= Nopt 
    && ((nt2 == Nenum && nt1 == Nval) || nt2 == Nprxy  || nt1 == Nnrml || (nt1 == Nopt && nt2 == Nvirt) || ([nt1, nt2] `subseteq` [Nvirt, Nabst]))
    

-- Ordering which underpins the compliance of refinement relations; says which node types can be refinement related
nty_leqr:: SGNTy->SGNTy->Bool
nty_leqr nt1 nt2    = nt1 == nt2 || nt1 == Nprxy || (nt2 `elem` [Nnrml, Nvirt] && nt1 `elem` [Nnrml, Nvirt, Nabst]) 
   || nt2 `elem` [Nnrml, Nopt] || (nt1 == Nnrml && nt2 == Nprxy)
--nty_leqr _ Nnrml    = True
--nty_leqr _ Nopt     = True
--nty_leqr Nprxy _    = True
--nty_leqr nt Nabst   = nt `elem` [Nnrml, Nvirt]
--nty_leqr nt Nvirt   = nt `elem` [Nnrml, Nabst]
--nty_leqr Nnrml nt   = nt `elem` [Nprxy]
--nty_leqr nt1 nt2    = nt1 == nt2 

instance Ord SGNTy where
    (<) = nty_lti
    (<=) = nty_leqr

ety_eq (Erel _) (Erel _)   = True
ety_eq (Ecomp _) (Ecomp _) = True
ety_eq ety1 ety2           = ety1 == ety2

-- Relation used for refinement: wander edges are refined by any non-inheritance edges
ety_leq et1 Ewander  = True
-- ety_leq Eder et2     = et2 `elem` [e d | e<-[Ecomp, Erel], d<-[Duni, Dbi]]
ety_leq (Ecomp _) (Erel Dbi)  = True
ety_leq (Ecomp Duni) (Erel Duni)  = True
ety_leq et1 et2      = (not $ [et1, et2] `subseteq` [Einh, Edep]) && ((et1 `ety_eq` et2) || (et1 `elem` [Erefm, Epath] && et2 `elem` [e d | e<-[Ecomp, Erel], d<-[Duni, Dbi]]))

instance Ord SGETy where
    (<=) = ety_leq