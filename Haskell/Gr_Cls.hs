{-# LANGUAGE MultiParamTypeClasses #-}
module Gr_Cls(GR(..), TK(..), isKTotal, MK(..), GRM(..), GrM, G_WF_CHK(..), GM_CHK(..), GM_CHK'(..), cons_gm, empty_gm, tyOfN, tyOfE, 
   tyOfNM) where

import Relations
import ErrorAnalysis
import MyMaybe

data TK = Total | Partial deriving (Eq, Show)

isKTotal t = t == Total

--The three kinds of morphism: weak, partial, full (either total or partial) 
data MK = WeakM | PartialM | TotalM deriving (Eq, Show)

class GR g where
   ns ::  (Eq a, Eq b) =>g a b-> [a]
   es ::  (Eq a, Eq b) =>g a b-> [b]
   src::  (Eq a, Eq b) =>g a b-> [(b, a)]
   tgt::  (Eq a, Eq b) =>g a b-> [(b, a)]
   esId:: (Eq a, Eq b) =>g a b-> [b]
   empty:: (Eq a, Eq b) => g a b
   esId g = filter (\e-> appl (src g) e == appl (tgt g) e)(es g)

class GRM gm where
   fV :: (Eq a, Eq b)=> gm a b->[(a, a)]
   fE :: (Eq a, Eq b)=> gm a b->[(b, b)]

class G_WF_CHK g where
   is_wf::(Eq a, Eq b) => (Maybe TK)->g a b-> Bool
   check_wf::(Eq a, Eq b, Show a, Show b) => String->(Maybe TK)->g a b-> ErrorTree

data GrM a b = GrM {mV_ :: [(a, a)], mE_:: [(b, b)]} deriving(Eq, Show) 

cons_gm vf ef = GrM {mV_ = vf, mE_ = ef}
empty_gm = cons_gm [] [] 
fV_gm GrM {mV_ = vf, mE_ = _} = vf
fE_gm GrM {mV_ = _, mE_ = ef} = ef

-- gets node type of a particular node
tyOfN n m = appl (fV m) n
tyOfNM n m = applM (fV m) n

-- gets edge type of a particular edge
tyOfE e m = appl (fE m) e

instance GRM GrM where
   fV = fV_gm
   fE = fE_gm

class GM_CHK g g' where
   is_wf_gm::(Eq a, Eq b)=>(Maybe MK)->(g a b, GrM a b, g' a b)->Bool 
   check_wf_gm::(Eq a, Eq b, Show a, Show b) => String->(Maybe MK)->(g a b, GrM a b, g' a b)->ErrorTree

class GM_CHK' g g' where
   is_wf_gm'::(Eq a, Eq b)=>(Maybe MK)->(g a b, g' a b)->Bool 
   check_wf_gm'::(Eq a, Eq b, Show a, Show b) => String->(Maybe MK)->(g a b, g' a b)->ErrorTree

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
