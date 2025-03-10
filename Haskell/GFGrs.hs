-------------------------
-- Project: PCs/Fragmenta
-- Module: 'GFGrs'
-- Description: Fragmenta's Global Fragment Graphs (GFGs)
-- Author: Nuno Amálio
--------------------------

module GFGrs(GFGr, consGFG, refsOf) where

import Gr_Cls
import Grs
import Relations
import Sets
import ErrorAnalysis 
import Utils
import TheNil

newtype GFGr a b = GFGr {gOf_ :: Gr a b} deriving (Eq, Show)

consGFG::Set a->Set b->Rel b a->Rel b a->GFGr a b
consGFG ns es s t = GFGr (consG ns es s t)

instance GR GFGr where
   ns :: (Eq a, Eq b) => GFGr a b -> Set a
   ns = ns . gOf_
   es :: (Eq a, Eq b) => GFGr a b -> Set b
   es = es . gOf_
   src :: (Eq a, Eq b) => GFGr a b -> Rel b a
   src = src . gOf_
   tgt :: (Eq a, Eq b) => GFGr a b -> Rel b a
   tgt = tgt . gOf_
   empty :: GFGr a b
   empty = consGFG nil nil nil nil

-- the refsOf
refsOf::(Eq a, Eq b)=> GFGr a b->Rel a a
refsOf = trancl . relOfG . gOf

okayGFG:: (Eq a, Eq b, Show a, GNumSets a) => GFGr a b -> Bool
okayGFG gfg = okayG Nothing (gOf gfg) && acyclicG (restrict gfg $ (es gfg) `sminus` (esId gfg))

errsGFG::(Eq a, Eq b, Show a, Show b, GNumSets a) => String->GFGr a b -> [ErrorTree]
errsGFG id gfg =
    let err1 = faultsG id Nothing (gOf gfg) in
    let err2 = if acyclicG (restrict gfg $ (es gfg) `sminus` (esId gfg)) then nile else consSET "The GFG has cycles." in
    [err1, err2]

reportGFG :: (Eq a, Eq b, Show a, Show b, GNumSets a) => 
   String -> GFGr a b -> ErrorTree
reportGFG id gfg = reportWF gfg id okayGFG (errsGFG id)

--is_wf_gfg' _ = is_wf_gfg

reportGFG' :: (Eq a, Eq b, GNumSets a, Show a, Show b) =>String -> p -> GFGr a b -> ErrorTree
reportGFG' id _ = reportGFG id

instance G_WF_CHK GFGr where
   okayG :: (Eq a, Eq b, Show a, GNumSets a)=>
      Maybe TK->GFGr a b->Bool
   okayG _ = okayGFG
   faultsG :: (Eq a, Eq b, Show a, Show b, GNumSets a)=>
      String->Maybe TK->GFGr a b->ErrorTree
   faultsG = reportGFG'