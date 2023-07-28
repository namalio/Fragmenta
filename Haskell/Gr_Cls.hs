{-# LANGUAGE MultiParamTypeClasses #-}
module Gr_Cls(GR(..), TK(..), isKTotal, MK(..), GRM(..), GrM, G_WF_CHK(..), GM_CHK(..), 
   GM_CHK'(..)
   , consGM
   , isEmptyGM
   , emptyGM
   , tyOfN
   , tyOfE
   , tyOfNM
   , domg
   , codg) where

import Relations
import ErrorAnalysis
import MyMaybe
import Sets ( filterS, Set(..) )
import TheNil

data TK = Total | Partial deriving (Eq, Show)

isKTotal t = t == Total

--The three kinds of morphism: weak, partial, full (either total or partial) 
data MK = WeakM | PartialM | TotalM deriving (Eq, Show)

class GR g where
   ns ::  (Eq a, Eq b) =>g a b-> Set a
   es ::  (Eq a, Eq b) =>g a b-> Set b
   src::  (Eq a, Eq b) =>g a b-> Rel b a
   tgt::  (Eq a, Eq b) =>g a b-> Rel b a
   esId:: (Eq a, Eq b) =>g a b-> Set b
   empty:: g a b
   els :: (Eq a, Eq b) =>g a b-> (Set a, Set b)
   els g = (ns g, es g)
   esId g = filterS (\e-> appl (src g) e == appl (tgt g) e)(es g)

class GRM gm where
   fV :: (Eq a, Eq b)=> gm a b->Rel a a
   fE :: (Eq a, Eq b)=> gm a b->Rel b b

domg:: (Eq a, Eq b, GRM gm)=> gm a b->(Set a, Set b)
domg gm = (dom_of . fV $ gm, dom_of . fE $ gm) 
codg:: (Eq a, Eq b, GRM gm)=> gm a b->(Set a, Set b)
codg gm = (ran_of . fV $ gm, ran_of . fE $ gm) 

class G_WF_CHK g where
   okayG::(Eq a, Eq b) => (Maybe TK)->g a b-> Bool
   faultsG::(Eq a, Eq b, Show a, Show b) => String->(Maybe TK)->g a b-> ErrorTree

data GrM a b = GrM {mV_ :: Rel a a, mE_:: Rel b b} deriving(Eq, Show) 

consGM :: Rel a a -> Rel b b -> GrM a b
consGM vf ef = GrM {mV_ = vf, mE_ = ef}
emptyGM :: GrM a b
emptyGM = consGM EmptyS EmptyS

isEmptyGM::(Eq a, Eq b)=>GrM a b->Bool
isEmptyGM = (== emptyGM)
--fV_gm :: GrM a b -> Rel a a
--fV_gm GrM {mV_ = vf, mE_ = _} = vf
--fE_gm :: GrM a b -> Rel b b
--fE_gm GrM {mV_ = _, mE_ = ef} = ef

-- gets node type of a particular node
tyOfN :: (GRM gm, Eq a, Eq b) => a -> gm a b -> a
tyOfN n m = appl (fV m) n
tyOfNM :: (GRM gm, Eq a, Eq b) => a -> gm a b -> Maybe a
tyOfNM n m = applM (fV m) n

-- gets edge type of a particular edge
tyOfE :: (GRM gm, Eq b, Eq a) => b->gm a b-> b
tyOfE e m = appl (fE m) e

instance GRM GrM where
   fV :: (Eq a, Eq b) => GrM a b -> Rel a a
   fV GrM {mV_ = vf, mE_ = _} = vf
   fE :: (Eq a, Eq b) => GrM a b -> Rel b b
   fE GrM {mV_ = _, mE_ = ef} = ef

class GM_CHK g g' where
   okayGM::(Eq a, Eq b)=>(Maybe MK)->(g a b, GrM a b, g' a b)->Bool 
   faultsGM::(Eq a, Eq b, Show a, Show b) => String->(Maybe MK)->(g a b, GrM a b, g' a b)->ErrorTree

class GM_CHK' g g' where
   okayGM'::(Eq a, Eq b)=>(Maybe MK)->(g a b, g' a b)->Bool 
   faultsGM'::(Eq a, Eq b, Show a, Show b) => String->(Maybe MK)->(g a b, g' a b)->ErrorTree

-- data GrMSs a = GrMSs {fV_ :: [(a, a)], fE_:: [(a, Int, a)]} deriving(Eq, Show) 
-- cons_gmss fv fe = GrMSs {fV_ = fv, fE_ = fe}
-- empty_gmss = cons_gmss [] []
-- fV_gmss GrMSs {fV_ = vf, fE_ = _} = vf
-- fE_gmss GrMSs {fV_ = _, fE_ = ef} = ef

-- class GRM' gm where
--    fV' :: Eq a=> gm a->[(a, a)]
--    fE' :: Eq a=> gm a->[(a, Int, a)]

-- instance GRM' GrMSs where
--    fV' = fV_gmss
--    fE' = fE_gmss
