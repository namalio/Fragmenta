module FrParsingToWET(
    PInfoWET
    , nsm
    , esm
    , sf
    , tf
    , nsem
    , esem
    , consPIWET
    , emptyPIWET
    , single4Fst
    , singleNP
    , singleNET
    , singleEET
    , singleEPs
    , join
    , joinNP
    , joinNET
    , gJoin) where
import Relations
import Sets
import TheNil

-- Information derived from parsing for a graph with extra typing
data PInfoWET a = PInfoWET {
    nsm_::Rel a a       -- node to type mapping
    , esm_::Rel a a     -- edge to type mapping
    , sm_::Rel a a      -- source mapping
    , tm_::Rel a a      -- target mapping
    , nsem_::Rel a a    -- node extra maping
    , esem_ :: Rel a a} -- edge extra mapping

consPIWET ::Rel a a->Rel a a->Rel a a->Rel a a->Rel a a->Rel a a->PInfoWET a
consPIWET mns mes ms mt emns emes = 
    PInfoWET { nsm_ = mns, esm_ = mes, sm_ = ms, tm_ = mt, nsem_ = emns, esem_ = emes}

emptyPIWET :: PInfoWET a
emptyPIWET = consPIWET nil nil nil nil nil nil

nsm::PInfoWET a->Rel a a
nsm PInfoWET { nsm_ = m, esm_ = _, sm_ = _, tm_ = _, nsem_ = _, esem_ = _} = m

esm::PInfoWET a->Rel a a
esm PInfoWET { nsm_ = _, esm_ = m, sm_ = _, tm_ = _, nsem_ = _, esem_ = _} = m

sf::PInfoWET a->Rel a a
sf PInfoWET { nsm_ = _, esm_ = _, sm_ = m, tm_ = _, nsem_ = _, esem_ = _} = m

tf::PInfoWET a->Rel a a
tf PInfoWET { nsm_ = _, esm_ = _, sm_ = _, tm_ = m, nsem_ = _, esem_ = _} = m

nsem::PInfoWET a->Rel a a
nsem PInfoWET { nsm_ = _, esm_ = _, sm_ = _, tm_ = _, nsem_ = m, esem_ = _} = m

esem::PInfoWET a->Rel a a
esem PInfoWET { nsm_ = _, esm_ = _, sm_ = _, tm_ = _, nsem_ = _, esem_ = m} = m

single4Fst::(a, a)->(a, a)->(a, a)->(a, a)->PInfoWET a
single4Fst nsp esp sp tp = 
    consPIWET (singles nsp) (singles esp) (singles sp) (singles tp) nil nil

singleNP::(a,a)->PInfoWET a
singleNP nsp = consPIWET (singles nsp) nil nil nil nil nil

singleNET::(a,a)->PInfoWET a
singleNET netp = consPIWET nil nil nil nil (singles netp)  nil

singleEET::(a,a)->PInfoWET a
singleEET eetp = consPIWET nil nil nil nil nil (singles eetp)

singleEPs::(a,a)->(a,a)->(a,a)->PInfoWET a
singleEPs ep sp tp = consPIWET nil (singles ep) (singles sp) (singles tp) nil nil

join::Eq a=>PInfoWET a->PInfoWET a->PInfoWET a
join pi1 pi2 = 
    consPIWET (nsm pi1 `union` nsm pi2) (esm pi1 `union` esm pi2) (sf pi1 `union` sf pi2) (tf pi1 `union` tf pi2) (nsem pi1 `union` nsem pi2) (esem pi1 `union` esem pi2)

joinNP::Eq a=>(a,a)->PInfoWET a->PInfoWET a
joinNP p pi = consPIWET (p `intoSet` nsm pi) (esm pi) (sf pi) (tf pi) (nsem pi) (esem pi)

joinNET::Eq a=>(a,a)->PInfoWET a->PInfoWET a
joinNET p pi = consPIWET (nsm pi) (esm pi) (sf pi) (tf pi) (p `intoSet` nsem pi) (esem pi)

gJoin::Eq a=>[PInfoWET a]->PInfoWET a
gJoin = foldl join emptyPIWET