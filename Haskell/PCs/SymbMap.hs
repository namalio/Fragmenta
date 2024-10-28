module PCs.SymbMap 
    (SymMap
    , emptySM
    , smap
    , rel
    , put
    , PCs.SymbMap.lookup
    , keys
    , keyOf)
where

import Relations
import Sets

newtype SymMap a b = SymMap (Rel a b)
    deriving (Show)

smap::Rel a b->SymMap a b
smap = SymMap

emptySM::SymMap a b
emptySM = smap EmptyS

rel::SymMap a b->Rel a b
rel (SymMap r) = r

instance Functor (SymMap a) where
    fmap f (SymMap r) = smap $ fmap (\(x, y)->(x, f y)) r 

--instance Applicative (SymMap a) where
    --pure r = smap r
--instance Monad (SymMap a) where
    --return = smap
   -- sm >>= f = f . rel $ sm

put::(Eq a, Eq b)=>SymMap a b->a->b->SymMap a b
put sm s o = 
    let r = rel sm in
    smap $ if s `elem` dom_of r then override r (singles (s, o)) else (s, o) `intoSet` r

 
lookup::(Eq a, Eq b)=>SymMap a b->a->Maybe b
lookup sm = applM (rel sm)

keys::Eq a=>SymMap a b->Set a
keys = dom_of . rel

keyOf::Eq a=>a->SymMap a b->Bool
keyOf x sm = x `elem` keys sm 