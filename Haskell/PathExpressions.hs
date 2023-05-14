---------------------
-- Project: PCs/Fragmenta
-- Module: 'Path_Expressions'
-- Description: Module dedicated to path expressions used in structural graphs (SGs)
-- Author: Nuno Amálio
---------------------

module PathExpressions (PEA(..), PE(..), srcPE, tgtPE, rsrcPE, rtgtPE) where

import Sets
import Gr_Cls
import Relations ( appl )
import Grs

data PEA e = Edg e | Inv e 
   deriving (Eq, Show)
data PE v e = At (PEA e) | Dres v (PEA e) | Rres (PEA e) v | SCmp (PE v e) (PE v e) 
   deriving (Eq, Show)

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

srcPE :: (Eq a, Eq b, GR g) => g a b->PE a b -> a
srcPE g (At pea) = srcPEA g pea
srcPE g (Dres _ pea) = srcPEA g pea
srcPE g (Rres pea _) = srcPEA g pea
srcPE g (SCmp pe1 _) = srcPE g pe1

tgtPEA :: (Eq a, Eq b, GR g) => g a b->PEA b -> a
tgtPEA g (Edg e) = appl (tgt g) e
tgtPEA g (Inv e) = appl (src g) e

tgtPE :: (Eq a, Eq b, GR g) => g a b->PE a b -> a
tgtPE g (At pea) = tgtPEA g pea
tgtPE g (Dres _ pea) = tgtPEA g pea
tgtPE g (Rres pea _) = tgtPEA g pea
tgtPE g (SCmp _ pe2) = tgtPE g pe2


-- reduces to the source edge (leftmost) of a path expression
rsrcPE :: (Eq a, Eq b) => PE a b -> b
rsrcPE (At pea) = ePEA pea 
rsrcPE (Dres _ pea) = ePEA pea
rsrcPE (Rres pea _) = ePEA pea
rsrcPE (SCmp pe1 _) = rsrcPE pe1

-- reduces to the target edge (rightmost) of a path expression
rtgtPE :: (Eq a, Eq b) => PE a b -> b
rtgtPE (At pea) = ePEA pea 
rtgtPE (Dres _ pea) = ePEA pea
rtgtPE (Rres pea _) = ePEA pea
rtgtPE (SCmp _ pe) = rtgtPE pe
