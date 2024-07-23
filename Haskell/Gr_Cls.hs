{-# LANGUAGE MultiParamTypeClasses #-}
module Gr_Cls(
   GR(..)
   , TK(..)
   , isKTotal
   , MK(..)
   , GRM(..)
   , GrM
   , GWT(..)
   , GWET(..)
   , G_WF_CHK(..)
   , GM_CHK(..)
   , GM_CHK'(..)
   , ET_GM_CHK(..)
   , Gr(..)
   , Ok_ETC_CHK(..)
   , GET(..)
   , GNodesNumConv(..)
   , GNumSets(..)
   , consG
   , gOf
   , consGM
   , isEmptyGM
   , emptyGM
   , tyOfN
   , tyOfE
   , tyOfNM
   , domg
   , codg) where

import Relations ( appl, applM, dom_of, ran_of, Rel )
import ErrorAnalysis ( ErrorTree )
import Sets ( filterS, Set(..) )

data Gr a b = Gr {
   ns_ :: Set a, 
   es_ ::  Set b,
   src_ :: Rel b a,
   tgt_ :: Rel b a} 
   deriving(Eq, Show) 

-- constructor
consG :: Set a -> Set b -> Rel b a -> Rel b a -> Gr a b
consG ns' es' s t =  Gr {ns_ = ns', es_ = es', src_ = s, tgt_ = t}

data TK = Total | Partial deriving (Eq, Show)

isKTotal :: TK -> Bool
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

gOf::(GR g, Eq a, Eq b)=>g a b->Gr a b
gOf g = consG (ns g) (es g) (src g) (tgt g)

class GRM gm where
   fV :: (Eq a, Eq b)=> gm a b->Rel a a
   fE :: (Eq a, Eq b)=> gm a b->Rel b b

domg:: (Eq a, Eq b, GRM gm)=> gm a b->(Set a, Set b)
domg gm = (dom_of . fV $ gm, dom_of . fE $ gm) 
codg:: (Eq a, Eq b, GRM gm)=> gm a b->(Set a, Set b)
codg gm = (ran_of . fV $ gm, ran_of . fE $ gm) 

class G_WF_CHK g where
   okayG::(Eq a, Eq b, GNumSets a) =>Maybe TK->g a b-> Bool
   faultsG::(Eq a, Eq b, Show a, Show b, GNumSets a) =>String->Maybe TK->g a b-> ErrorTree

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

-- Gets node type of a particular node
tyOfN :: (GRM gm, Eq a, Eq b) => a -> gm a b -> a
tyOfN n m = appl (fV m) n
tyOfNM :: (GRM gm, Eq a, Eq b) => a -> gm a b -> Maybe a
tyOfNM n m = applM (fV m) n

-- Gets edge type of a particular edge
tyOfE :: (GRM gm, Eq b, Eq a) => b->gm a b-> b
tyOfE e m = appl (fE m) e

instance GRM GrM where
   fV :: (Eq a, Eq b) => GrM a b -> Rel a a
   fV GrM {mV_ = vf, mE_ = _} = vf
   fE :: (Eq a, Eq b) => GrM a b -> Rel b b
   fE GrM {mV_ = _, mE_ = ef} = ef

class GM_CHK g g' where
   okayGM::(Eq a, Eq b, GNodesNumConv a, GNumSets a)
      =>Maybe MK->(g a b, GrM a b, g' a b)->Bool 
   faultsGM::(Eq a, Eq b, Show a, Show b, GNodesNumConv a, GNumSets a)
      => String->Maybe MK->(g a b, GrM a b, g' a b)->ErrorTree

class GM_CHK' g g' where
   okayGM'::(Eq a, Eq b, Read a, GNodesNumConv a, GNumSets a)=>Maybe MK->(g a b, g' a b)->Bool 
   faultsGM'::(Eq a, Eq b, Read a, Show a, Show b, GNodesNumConv a, GNumSets a) => String->Maybe MK->(g a b, g' a b)->ErrorTree

class GWT gwt where
   ty:: GR gwt=>gwt a b->GrM a b
   
class GWET gwt where  
   etm::(Eq a, Eq b, GWT gwt)=>gwt a b->GrM a b 

class GET get where
   etc::(Eq a, Eq b)=>get a b->GrM a b 

class Ok_ETC_CHK gt where
   okETC::(Eq a, Eq b, GET gt)=>gt a b->gt a b->Bool
   faultsETC::(Eq a, Eq b, Show a, Show b, GET gt)=>String->gt a b->gt a b->ErrorTree

class ET_GM_CHK gi gi' gt where
   okayETGM::(Eq a, Eq b, Read a, GWET gi, GWT gi', GNodesNumConv a, GNumSets a)=>(gi a b, gt a b)->(gi' a b, gt a b)->Bool 
   faultsETGM::(Eq a, Eq b, Read a, Show a, Show b, GWET gi, GWT gi', GNodesNumConv a, GNumSets a)=>String->(gi a b, gt a b)->(gi' a b, gt a b)->ErrorTree

-- Numerical conversion for graphs
class GNodesNumConv a where
   toInt::Read a=>a->Maybe Int
   toReal::Read a=>a->Maybe Float

class GNumSets a where
   nNatS::Eq a=>a
   nIntS::Eq a=>a
   nRealS::Eq a=>a
