-------------------------
-- Project: PCs/Fragmenta
-- Module: 'GrswT'
-- Description: Fragmenta's graphs with typing (GrswT)
-- Author: Nuno Amálio
---------------------------
module GrswT (consGWT, gof, ty, GrwT, unionGWT) where

import Sets
import Relations ( dom_of )
import Grs
import Gr_Cls
import ErrorAnalysis
import Utils ( reportWF )

data GrwT a b = GrwT {
    g_ :: Gr a b
    , t_ :: GrM a b
    } deriving(Eq, Show) 

consGWT :: Gr a b -> GrM a b -> GrwT a b
consGWT g t = GrwT  {g_ = g, t_ = t}

gof GrwT  {g_ = g, t_ = _} = g
t' GrwT  {g_ = _, t_ = t} = t

--emptyGWT :: GrwT a b
--emptyGWT = consGWT empty emptyGM 

instance GR GrwT where
   ns = ns . gof
   es = es . gof
   src = src . gof
   tgt = tgt . gof
   empty :: GrwT a b
   empty = consGWT empty emptyGM 

instance GRM GrwT where
    fV = fV . ty
    fE = fE . ty

instance GWT GrwT where
    ty = t'

-- well-formedness
okGWT :: (Eq a, Eq b)=>GrwT a b -> Bool
okGWT gwt = 
    okayG Nothing (gOf gwt) && domg gwt == els gwt 

errsGWT :: (Show a, Show b, Eq b, Eq a) => String -> GrwT a b -> [ErrorTree]
errsGWT id gwt = 
    let err1 = faultsG id Nothing $ gOf gwt 
        err2 = if (dom_of . fV $ gwt) == ns gwt then nile else reportSEq (dom_of . fV $ gwt) (ns gwt) 
        err3 = if (dom_of . fE $ gwt) == es gwt then nile else reportSEq (dom_of . fE $ gwt) (es gwt) in
    [err1, err2, err3]

rOkGWT :: (Eq a, Eq b, Show a, Show b) => String -> GrwT a b -> ErrorTree
rOkGWT id gwt = reportWF gwt id okGWT (errsGWT id)


--is_wf' _ = is_wf_gwt
--check_wf' id _ = check_wf_gwt id

unionGWT :: (Eq a, Eq b) =>GrwT a b -> GrwT a b -> GrwT a b
unionGWT gwt1 gwt2 = consGWT (gwt1 `unionG` gwt2) (gwt1 `unionGM` gwt2)

instance G_WF_CHK GrwT where
   okayG _ = okGWT
   faultsG id _ = rOkGWT id