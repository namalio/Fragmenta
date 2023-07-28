---------------------
-- Project: PCs/Fragmenta
-- Module: 'Path_Expressions'
-- Description: Module dedicated to path expressions used in structural graphs (SGs)
-- Author: Nuno Amálio
---------------------

module PathExpressions (PEA(..), PE(..), PEC(..)
   , ePEA
   , srcPE
   , srcPEC
   , tgtPE
   , tgtPEC
   , rsrcPE
   , rtgtPE
   , startEA
   , startEAC
   , endEA
   , endEAC
   , fmap2PE) where

import Sets
import Gr_Cls
import Relations ( appl )
import Grs

data PEA e = Edg e | Inv e 
   deriving (Eq, Show)
data PEC v e = At (PEA e) | Dres v (PEA e) | Rres (PEA e) v 
   deriving (Eq, Show)
data PE v e = Ec (PEC v e)| SCmp (PEC v e) (PE v e) 
   deriving (Eq, Show)

instance Functor PEA where
   fmap f (Edg e) = Edg(f e)
   fmap f (Inv e) = Inv(f e)

fmap2PEC::(a->b)->(c->d)->PEC a c->PEC b d
fmap2PEC f g (At pea) = At (fmap g pea)
fmap2PEC f g (Dres v pea) = Dres (f v) (fmap g pea)
fmap2PEC f g (Rres pea v) = Rres (fmap g pea) (f v)

fmap2PE::(a->b)->(c->d)->PE a c->PE b d
fmap2PE f g (Ec pec) = Ec (fmap2PEC f g pec)
fmap2PE f g (SCmp pec pe) = SCmp (fmap2PEC f g pec) (fmap2PE f g pe)

ePEA :: (Eq a) => PEA a -> a
ePEA (Edg e) = e
ePEA (Inv e) = e

--esPE :: (Eq a, Eq b) => PE a b -> [b]
--esPE (At pea) = esPEA pea
--esPE (Dres _ pea) = esPEA pea
--esPE (Rres pea _) = esPEA pea
--esPE (SCmp pe1 pe2) = (esPE pe1) `union` (esPE pe2)

srcPEA :: (Eq a, Eq b, GR g) => g a b->PEA b -> a
srcPEA g (Edg e) = appl (src g) e
srcPEA g (Inv e) = appl (tgt g) e

srcPEC :: (Eq a, Eq b, GR g) => g a b->PEC a b -> a
srcPEC g (At pea) = srcPEA g pea
srcPEC g (Dres _ pea) = srcPEA g pea
srcPEC g (Rres pea _) = srcPEA g pea
srcPE :: (Eq a, Eq b, GR g) => g a b->PE a b -> a
srcPE g (Ec pe) = srcPEC g pe
srcPE g (SCmp pe1 _) = srcPEC g pe1

tgtPEA :: (Eq a, Eq b, GR g) => g a b->PEA b -> a
tgtPEA g (Edg e) = appl (tgt g) e
tgtPEA g (Inv e) = appl (src g) e

tgtPEC :: (Eq a, Eq b, GR g) => g a b->PEC a b -> a
tgtPEC g (At pea) = tgtPEA g pea
tgtPEC g (Dres _ pea) = tgtPEA g pea
tgtPEC g (Rres pea _) = tgtPEA g pea
tgtPE :: (Eq a, Eq b, GR g) => g a b->PE a b -> a
tgtPE g (Ec pe) = tgtPEC g pe
tgtPE g (SCmp _ pe) = tgtPE g pe


-- The start or source edge (leftmost) of a path expression
startEAC :: PEC a b -> PEA b
startEAC (At pea) = pea 
startEAC (Dres _ pea) = pea 
startEAC (Rres pea _) = pea
startEA :: PE a b -> PEA b
startEA (Ec pe) = startEAC pe
startEA (SCmp pe _) = startEAC pe

-- The end or target edge (rightmost) of a path expression
endEAC :: PEC a b -> PEA b
endEAC (At pea) = pea 
endEAC (Dres _ pea) = pea 
endEAC (Rres pea _) = pea
endEA :: PE a b -> PEA b
endEA (Ec pe) = endEAC pe
endEA (SCmp _ pe) = endEA pe

-- reduces to the source edge (leftmost) of a path expression
rsrcPE :: (Eq a, Eq b) => PE a b -> b
rsrcPE = ePEA . startEA

-- reduces to the target edge (rightmost) of a path expression
rtgtPE :: (Eq a, Eq b) => PE a b -> b
rtgtPE = ePEA . endEA
