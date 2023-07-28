-------------------------
-- Project: PCs/Fragmenta
-- Module: 'GrswET'
-- Description: Fragmenta's graphs with extra typing (GrswET)
-- Author: Nuno Amálio
---------------------------
module GrswET (
    consGWET
    , GrwET
    , unionGWET
    , ggwt
    , gty
    , get
    , gg) where

import GrswT ( consGWT, gOf, ty, GrwT )
import Relations ( dom_of )
import Grs
import Gr_Cls
import ErrorAnalysis
import Utils ( reportWF )

data GrwET a b = GrwET {
    g_ :: GrwT a b
    , t_ :: GrM a b
    } deriving(Eq, Show) 

consGWET :: Gr a b -> GrM a b -> GrM a b ->GrwET a b
consGWET g t pt = GrwET  {g_ = consGWT g t, t_ = pt}

ggwt :: GrwET a b -> GrwT a b
ggwt GrwET  {g_ = g, t_ = _} = g
gg :: GrwET a b -> Gr a b
gg GrwET  {g_ = g, t_ = _} = gOf g
gty :: GrwET a b -> GrM a b
gty GrwET  {g_ = g, t_ = _} = ty g
get :: GrwET a b -> GrM a b
get GrwET  {g_ = _, t_ = t} = t
--emptyGWT :: GrwT a b
--emptyGWT = consGWT empty emptyGM 

instance GR GrwET where
   ns = ns . ggwt
   es = es . ggwt
   src = src . ggwt
   tgt = tgt . ggwt
   empty :: GrwET a b
   empty = consGWET empty emptyGM emptyGM 

instance GRM GrwET where
    fV = fV . ggwt
    fE = fE . ggwt

-- well-formedness
okGWET :: (Eq a, Eq b)=>GrwET a b -> Bool
okGWET gwet = okayG Nothing (ggwt gwet) && (domg gwet <= els gwet)

errsGWET :: (Show a, Show b, Eq b, Eq a) => String -> GrwET a b -> [ErrorTree]
errsGWET id gwet = 
    let err1 = faultsG id Nothing (ggwt gwet) in
    let err2 = if (dom_of . fV $ gwet) <= ns gwet then nile else reportSSEq (dom_of . fV $ gwet) (ns gwet) in
    let err3 = if (dom_of . fE $ gwet) <= es gwet then nile else reportSSEq (dom_of . fE $ gwet) (es gwet) in
    [err1, err2, err3]

reportGWET :: (Eq a, Eq b, Show a, Show b) => String -> GrwET a b -> ErrorTree
reportGWET id gwet = reportWF gwet id okGWET (errsGWET id)
--faultsG id Nothing $ ggwt gwet

--is_wf' _ = is_wf_gwt
--check_wf' id _ = check_wf_gwt id

unionGWET :: (Eq a, Eq b) =>GrwET a b -> GrwET a b -> GrwET a b
unionGWET gwet1 gwet2 = consGWET (gwet1 `unionG` gwet2) (gwet1 `unionGM` gwet2) (get gwet1 `unionGM` get gwet2)

instance G_WF_CHK GrwET where
   okayG :: (Eq a, Eq b) => Maybe TK -> GrwET a b -> Bool
   okayG _ = okGWET
   faultsG id _ = reportGWET  id