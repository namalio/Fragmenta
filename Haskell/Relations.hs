module Relations (Rel, dom_of, ran_of, img, inv, dres, rres, dsub, rsub, override, id_on, rcomp, bcomp, functional, 
    total, fun_total, pfun, fun_total', fun_pinj, fun_inj, fun_bij, injective, relation, cl_override, mktotal_in, 
    appl, find_monces, acyclic, trancl, rtrancl, rtrancl_on, reflexive, antireflexive, antireflexive_on, symmetric, 
    transitive, surjective, eq_rel, cross, flatten, tree) where

import SimpleFuns ( pair_up, swap )
import Sets ( Set(..), set, filterS, zipS, singles, union, gunion, intersec, intoSet, sminus, toList,
            first )
import TheNil

type Rel a b = Set (a, b)

dom_of :: Rel a b -> Set a
dom_of r = fst <$> r

ran_of :: Rel a b -> Set b
ran_of r = snd <$> r

-- Inverts a relation (as a list of pairs)
inv :: Rel a b -> Rel b a
inv r = swap <$> r

-- Identity on a given set
id_on :: Eq a => Set a -> Rel a a 
id_on a = zipS a a 

--domain restriction
dres :: (Foldable t, Eq a, Eq b) =>Rel a b -> t a -> Rel a b
dres r a = filterS ((`elem` a) . fst) r
    --foldr (\p r'->if fst p `elem` a then p `intoSet` r' else r') nilSet r

--range restriction
rres :: (Foldable t, Eq a, Eq b) =>Rel a b -> t b -> Rel a b
rres r a = filterS ((`elem` a) . snd) r
    --foldr (\p r'->if snd p `elem` a then p `intoSet` r' else r') nilSet r

-- domain subtraction
dsub :: (Eq a, Eq b) => Rel a b -> Set a -> Rel a b
dsub r a = dres r (dom_of r `sminus` a)
--foldr (\p r'->if fst p `elem` a then r' else p `intoSet` r') nilSet r
--filter ((\x -> not $ x `elem` xs) . fst) r

-- range subtraction
rsub :: (Eq a, Eq b) =>Rel a b -> Set b -> Rel a b
rsub r a = rres r (ran_of r `sminus` a)
--filter ((\y -> not $ y `elem` ys) . snd) r

--relation image
img :: (Foldable t, Eq a, Eq b)=>Rel a b -> t a -> Set b
img r xs = ran_of (dres r xs)

--takes first element of image (appropriate when doing function application)
appl :: (Eq a, Eq b)=>Rel a b -> a -> b
appl r x = first $ img r (singles x)

-- relational overriding
override::(Eq a, Eq b)=>Rel a b ->Rel a b ->Rel a b
override s r = dsub s (dom_of r) `union` r
--override EmptyS s = s
--override ((x,y) `Set` r) s 
--   | x `elem` (dom_of s) = override r s
--   | otherwise =  (x,y) `Set` (override r s)
--


rcomp::(Eq a, Eq b, Eq c)=>Rel a b-> Rel b c->Rel a c
rcomp r1 r2 = foldr (\(x, y) r'-> fmap (pair_up x) (img r2 $ singles y) `union` r') nil r1
--rcomp0 r1 r2 

-- backwards relation composition
bcomp :: (Eq a, Eq b, Eq c)=>Rel b c -> Rel a b -> Rel a c
bcomp r1 r2 = rcomp r2 r1
--foldr (\(x, y) r'->map (pair_up x) (img r1 [y]) `union` r') [] r2


functional :: Eq a=>Rel a b -> Bool
functional EmptyS = True
functional (Set (x, _) r) 
   | x `elem` (dom_of r) = False
   | otherwise           = functional r

total :: Eq a=>Rel a b -> Set a -> Bool
total r xs = dom_of r ==  xs

range_ok :: Eq b=>Rel a b -> Set b -> Bool
range_ok r ys = (ran_of r) <= ys
fun_total :: (Eq a, Eq b)=>Rel a b -> Set a -> Set b -> Bool
fun_total f xs ys = functional f && total f xs && range_ok f ys
--fun_total_seq f xs ys = functional f && total f xs && (gunion . ran_of $ f) `subseteq` ys

fun_total' :: Eq a => Rel a b -> Set a -> Bool
fun_total' r xs = functional r && total r xs

injective :: Eq a => Rel b a -> Bool
injective r = (functional . inv) r

surjective :: Eq b => Rel a b -> Set b -> Bool
surjective r ys = ys == (ran_of r)

relation :: (Eq a, Eq b) => Rel a b -> Set a -> Set b -> Bool
relation r xs ys = (dom_of r) <= xs && range_ok r ys
pfun :: (Eq a, Eq b) => Rel a b -> Set a -> Set b -> Bool
pfun f xs ys = functional f && relation f xs ys

-- A partial injection (pinj)
fun_pinj :: (Eq b, Eq a) => Rel a b -> Set a -> Set b -> Bool
fun_pinj f xs ys = injective f && pfun f xs ys
fun_inj :: (Eq b, Eq a) => Rel a b -> Set a -> Set b -> Bool
fun_inj f xs ys = injective f && fun_total f xs ys

inj_fun r xs ys = injective r && fun_total r xs ys
--inj_surj_fun r xs ys = injective r && surjective r ys && fun_total r xs ys

total_fun_surj r xs ys = fun_total r xs ys && surjective r ys
fun_bij :: (Eq a, Eq b) => Rel a b -> Set a -> Set b -> Bool
fun_bij r xs ys = fun_total r xs ys && injective r && surjective r ys

-- Checks that a relation is anti-reflexive
antireflexive :: Eq a => Rel a a -> Bool
antireflexive r = all (\(x,y)-> x /= y) r
antireflexive_on :: Eq a => Rel a a -> Set a -> Bool
antireflexive_on r xs = relation r xs xs && antireflexive r

--Checks that a relation is reflexive 
reflexive::Eq a =>Rel a a -> Bool
reflexive r = id_on (dom_of r) <= r

--Checks that a relation is symmetric 
symmetric::Eq a =>Rel a a -> Bool
symmetric r = inv r <= r

--Checks that a relation is transitive
transitive::Eq a =>Rel a a -> Bool
transitive r = r `rcomp` r <= r 

-- transitive closure
trancl :: Eq a => Rel a a -> Rel a a
trancl r = let r' = r `union` (r `rcomp` r) in if r' == r then r else trancl r'

rtrancl :: Eq a => Rel a a -> Rel a a
rtrancl r = (trancl r) `union` (id_on ((dom_of r) `union` (ran_of r)))

rtrancl_on :: Eq a => Rel a a -> Set a-> Rel a a
rtrancl_on r xs= (trancl r) `union` (id_on xs)

-- Checks whether a relation forms a tree
tree :: Eq b => Rel b b -> Bool
tree r = acyclic r && functional r

-- An equivalence relation over r
eq_rel :: Eq a => Rel a a -> Rel a a
eq_rel r = rtrancl_on (r `union` (inv r)) ((dom_of r) `union` (ran_of r))

-- Says whether a relation is acyclic
acyclic :: Eq a => Rel a a -> Bool
acyclic r = null $ trancl r `intersec` (id_on $ dom_of r `union` ran_of r)

-- closure of a relation ovveride
cl_override r = let r' = r `override` (rcomp r r) in if r' == r then r else cl_override r'
cl_override2 r = 
    let is_intermediate x y = (x, y) `elem` r && x /= y && y `elem` (dom_of r) && (not $ (y, y) `elem` r) in
    (trancl r) `sminus` (foldr (\(x, y) r'->if is_intermediate x y then Set (x, y) r' else r') nil r)

-- Totalises a relation within a set by using identity to stand for undefinedness
mktotal_in r s = (id_on s) `override` r

-- Those domain elements which are mapped more than once in a relation
find_monces r = foldr (\x xs->if length (img r $ singles x) > 1 then x `intoSet` xs else xs) nil (dom_of r)

--find_multi_map_xs [] = []
--find_multi_map_xs ((x, y):r)
--   | not (null (img r [x])) = x:(find_multi_map_xs r)
--   | otherwise              = find_multi_map_xs r

cross :: (Eq a, Eq b) => Set a -> Set b -> Set (a, b)
cross EmptyS _ = nil
cross (Set x a) b = (fmap (pair_up x) b) `union` (cross a b)

flatten :: (Eq a, Eq b)=>Set (a, [b]) -> Set (a, b)
flatten EmptyS = EmptyS
flatten (Set (x, ys) r) = (set $ map (pair_up x) ys) `union` (flatten r)