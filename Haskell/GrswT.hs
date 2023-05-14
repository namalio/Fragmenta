-------------------------
-- Project: PCs/Fragmenta
-- Module: 'GrswT'
-- Description: Fragmenta's graphs with typing (GrswT)
-- Author: Nuno Amálio
---------------------------
module GrswT (consGWT, gOf, ty, GrwT, unionGWT) where

import Sets
import Relations ( dom_of )
import Grs
import Gr_Cls
import ErrorAnalysis

data GrwT a b = GrwT {
    g_ :: Gr a b
    , t_ :: GrM a b
    } deriving(Eq, Show) 

consGWT :: Gr a b -> GrM a b -> GrwT a b
consGWT g t = GrwT  {g_ = g, t_ = t}

gOf GrwT  {g_ = g, t_ = _} = g
ty GrwT  {g_ = _, t_ = t} = t

--emptyGWT :: GrwT a b
--emptyGWT = consGWT empty emptyGM 

instance GR GrwT where
   ns = ns . gOf
   es = es . gOf
   src = src . gOf
   tgt = tgt . gOf
   empty :: GrwT a b
   empty = consGWT empty emptyGM 


instance GRM GrwT where
    fV = fV . ty
    fE = fE . ty

-- well-formedness
wfGWT :: (Eq a, Eq b)=>GrwT a b -> Bool
wfGWT gwt = (okayG Nothing $ gOf gwt) && (dom_of . fV $ gwt) == ns gwt && (dom_of . fE $ gwt) == es gwt

errsGWT :: (Show a, Show b, Eq b, Eq a) => String -> GrwT a b -> ErrorTree
errsGWT id gwt = 
    let err1 = faultsG id Nothing $ gOf gwt in
    let err2 = if (dom_of . fV $ gwt) == ns gwt then nile else reportSEq (dom_of . fV $ gwt) (ns gwt) in
    let err3 = if (dom_of . fE $ gwt) == es gwt then nile else reportSEq (dom_of . fE $ gwt) (es gwt) in
    add_to_err err1 [err2, err3]

reportGWT :: (Eq a, Eq b, Show a, Show b) => String -> GrwT a b -> ErrorTree
reportGWT id gwt = (faultsG id Nothing $ gOf gwt)

--is_wf' _ = is_wf_gwt
--check_wf' id _ = check_wf_gwt id

unionGWT gwt1 gwt2 = consGWT (gwt1 `unionG` gwt2) (gwt1 `unionGM` gwt2)

instance G_WF_CHK GrwT where
   okayG _ = wfGWT
   faultsG id _ = reportGWT  id