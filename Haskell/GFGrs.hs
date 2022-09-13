-------------------------
-- Project: PCs/Fragmenta
-- Module: 'GFGrs'
-- Description: Fragmenta's Global Fragment Graphs (GFGs)
-- Author: Nuno Amálio
--------------------------

module GFGrs(GFGr, cons_gfg, refsOf) where

import Gr_Cls
import Grs
import Relations
import Sets
import ErrorAnalysis 
import Utils

newtype GFGr a b = GFGr {gOf :: Gr a b} deriving (Eq, Show)

cons_gfg::(Eq a, Eq b)=> [a]->[b]->[(b, a)]->[(b, a)]->GFGr a b
cons_gfg ns es s t = GFGr (cons_g ns es s t)

instance GR GFGr where
   ns = ns . gOf
   es = es . gOf
   src = src . gOf
   tgt = tgt . gOf
   empty = cons_gfg [] [] [] []

-- the refsOf
refsOf::(Eq a, Eq b)=> GFGr a b->[(a, a)]
refsOf = (trancl . relOfG . gOf)

is_wf_gfg:: (Eq a, Eq b) => GFGr a b -> Bool
is_wf_gfg gfg = is_wf Nothing (gOf gfg) && acyclicG (restrict gfg $ (es gfg) `diff` (esId gfg))

errors_wf_gfg::(Eq a, Eq b, Show a, Show b) => String->GFGr a b -> [ErrorTree]
errors_wf_gfg id gfg =
    let err1 = check_wf id Nothing (gOf gfg) in
    let err2 = if acyclicG (restrict gfg $ (es gfg) `diff` (esId gfg)) then nile else cons_se "The GFG has cycles." in
    [err1, err2]

check_wf_gfg id gfg = check_wf_of gfg id (is_wf_gfg) (errors_wf_gfg id)

is_wf_gfg' _ = is_wf_gfg

check_wf_gfg' id _ = check_wf_gfg id

instance G_WF_CHK GFGr where
   is_wf = is_wf_gfg'
   check_wf = check_wf_gfg'