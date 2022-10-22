---------------------
-- Project: PCs/Fragmenta
-- Module: 'Path_Expressions'
-- Description: Module dedicated to path expressions used in structural graphs (SGs)
-- Author: Nuno Amálio
---------------------

module Path_Expressions (PEA(..), PE(..), srcPE, tgtPE) where

import Sets
import Gr_Cls
import Relations
import Grs

data PEA e = Edg e | Inv e 
   deriving (Eq, Show)
data PE v e = At (PEA e) | Dres v (PEA e) | Rres (PEA e) v | SCmp (PE v e) (PE v e) 
   deriving (Eq, Show)

--esPEA :: (Eq a, Eq b) => PEA a b -> [b]
--esPEA (Edg e) = [e]
--esPEA (Inv e) = [e]

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



