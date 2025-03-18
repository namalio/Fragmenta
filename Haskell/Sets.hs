module Sets (
   Set(..)
   , singles
   , set1
   , filterS
   , zipS
   , set
   , toList
   , intoSet
   , rest
   , card
   , sminus
   , union
   , gunion
   , reduce
   , intersec
   , gintersec
   , disjoint
   , power
   , first
   , dups) where

import TheNil
import GHC.Base(Alternative(..), MonadPlus(..))

data Set a = EmptyS | Set a (Set a) 

instance The Set where
   the :: Set a -> a
   the (x `Set` xs) = x

instance Nil Set where
   nil = EmptyS
   isNil EmptyS = True
   isNil _ = False

singles :: a -> Set a
singles x = x `Set` EmptyS

set1 :: a -> Set a
set1 = singles

joinS::Set a->Set a->Set a
joinS EmptyS s = s
joinS s EmptyS = s
joinS (x `Set` xs) s  = Set x (joinS xs s)

inSet::(Eq a) => a->Set a ->Bool
inSet x EmptyS = False
inSet x (y `Set` s) 
   | x == y  = True
   | otherwise = inSet x s

-- adds element to set
intoSet :: Eq a => a -> Set a -> Set a
intoSet x EmptyS = x `Set` EmptyS
intoSet x s@(Set y s') 
   | x == y = s
   | otherwise = y `Set` (x `intoSet` s')

toList :: Set a -> [a]
toList = foldr (:) []

set:: (Foldable t, Eq a)=> t a->Set a
set = foldr intoSet nil

first::Set a->a
first (Set x _) = x

rest::Set a->Set a
rest (Set _ xs) = xs

-- removes duplicates
reduce :: Eq a => Set a -> Set a
reduce = foldl (\s e->if e `elem` s then s else Set e s) nil
--reduce (Set []) = nilSet
--reduce (Set (x:xs))
--   | x `elem` xs = reduce (Set xs)
--   | otherwise = intoSet x (reduce (Set xs))

--set cardinality
card :: Eq a => Set a -> Int
card s = foldl (\c _->c+ 1) 0 (reduce s)
--   length . toList . reduce

subseteq :: (Eq a) => Set a -> Set a -> Bool
subseteq s1 s2 = all (`elem` s2) s1

instance Eq a => Ord (Set a) where
   (<=) :: Eq a => Set a -> Set a -> Bool
   (<=) = subseteq

seteq :: (Eq a) => Set a -> Set a -> Bool
seteq s1 s2 = s1 <= s2 && s2 <= s1

instance Eq a => Eq (Set a) where
   (==) :: Eq a => Set a -> Set a -> Bool
   (==) = seteq  

instance Show a => Show (Set a) where
   show :: Show a => Set a -> String
   show s = "{" ++ foldr (\e str->show e ++ if null str then "" else "," ++ str) "" s ++ "}"

instance Foldable Set where
   elem :: Eq a => a -> Set a -> Bool
   elem = inSet
   null :: Set a -> Bool
   null EmptyS = True
   null _ = False
   foldr :: (a -> b -> b) -> b -> Set a -> b
   foldr _ z EmptyS = z
   foldr f z (Set x s) = f x (foldr f z s)
   foldl :: (b -> a -> b) -> b -> Set a -> b
   foldl _ z EmptyS = z
   foldl f z (Set x s) = f (foldl f z s) x
   length :: Set a -> Int
   length EmptyS = 0
   length (Set x xs) = 1 + length xs
   

filterS:: Eq a=>(a -> Bool) -> Set a -> Set a
filterS p = foldr (\e s'->if p e then e `intoSet` s' else s') EmptyS

--anyS :: (a -> Bool) -> Set a -> Bool
--anyS p s = foldr (\x ob->p x || ob) False s
   
zipS::Set a -> Set b->Set (a, b)
zipS EmptyS _ = EmptyS
zipS _ EmptyS = EmptyS
zipS (Set x xs) (Set y ys) = Set (x, y) $ zipS xs ys

concatMapS::(a->Set b)->Set a->Set b
concatMapS f EmptyS = EmptyS
concatMapS f (Set x xs) = f x `joinS` (concatMapS f xs)

instance Functor Set where
   fmap :: (a -> b) -> Set a -> Set b
   fmap _ EmptyS = EmptyS
   fmap f (Set x s) = Set (f x) (fmap f s)

instance Applicative Set where
   pure :: a -> Set a
   pure x = Set x EmptyS
   (<*>) :: Set (a -> b) -> Set a -> Set b
   EmptyS <*> _ = EmptyS
   (Set f fs) <*> as = joinS (fmap f as) (fs <*> as)
 
instance Traversable Set where
   traverse :: Applicative f => (a -> f b) -> Set a -> f (Set b)
   traverse _ EmptyS = pure EmptyS
   traverse f (Set x s) = Set <$> f x <*> traverse f s

instance Monad Set where
   return = pure
   s >>= f = concatMapS f s

instance Alternative Set where
   empty = EmptyS
   (<|>) = joinS 

instance MonadPlus Set where
   mzero = empty
   mplus = (<|>)

-- set difference
sminus :: Eq a => Set a -> Set a -> Set a
sminus EmptyS _ = EmptyS
sminus a EmptyS = a
sminus (Set x a) b 
  | x `elem` b = a `sminus` b
  | otherwise  = intoSet x ( a `sminus` b)

union :: Eq a => Set a -> Set a -> Set a
union = foldr intoSet

-- generalised union
gunion :: (Foldable t, Eq a) => t (Set a) -> Set a
gunion = foldl union nil

-- intersection
intersec :: Eq a => Set a -> Set a -> Set a
intersec sa = foldl (\s e->if e `elem` sa then e `intoSet` s else s) EmptyS
--intersec _ [] = []
--intersec [] _ = []
--intersec (x:xs) ys 
--   | x `elem` ys  = x:(intersec xs ys)
--   | otherwise    = (intersec xs ys)

-- generalised intersection
gintersec ::Eq a=>[Set a]-> Set a
gintersec ss = if null ss then nil else foldl intersec (head ss) (tail ss)
   --if null ss then [] else foldr (\s si->(s `intersec` si)) (head ss) (tail ss)

--disjoint_set :: Eq a => Set a -> Bool
--disjoint_set xs = null $ dups xs
disjoint::Eq a =>  [Set a]->Bool
disjoint [] = True
disjoint (s:ss) = 
    (foldr (\s' si->(null $ s `intersec` s') && si) True ss) && disjoint ss 

combine::Eq a =>Set a->Set a->Set (Set a)
combine s EmptyS = singles s
combine s (Set x xs) = gunion[singles s, combine (x `intoSet` s) xs, combine s xs]

power :: Eq a => Set a -> Set (Set a)
power EmptyS = singles EmptyS 
power (Set x xs) = combine (singles x) xs `union` power xs
--(singles (singles x)) 

-- Gives elements of a set which are duplicated
dups :: Eq a => Set a -> Set a
dups EmptyS = EmptyS
dups (Set x xs) 
   | x `elem` xs  = Set x (dups xs)
   | otherwise    = dups xs