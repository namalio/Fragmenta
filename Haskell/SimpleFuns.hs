module SimpleFuns(swap
    , pairUp
    , equalLs
    , quicksortp
    , quicksort
    , fstT
    , sndT
    , thdT
    , fst_Q
    , mapP
    , mapT
    , applyPToP
    , butLast
    , ext_P_to_T
    , toIdxC
    , combineTwAppend
    , combineTwInsert
    , combineTwIntoS
    , combineQwInsert
    , combineQwIntoS
    , combineQwAppend
    , combineQwUnion
    , combineQWUnionLs
    , makeQFrTFst
    , nilQl
    , nilQS
    , replace
    , unique
    , dupsL) where

import Sets (union, intoSet, Set )
import Data.List(insert)
import TheNil

--inverts the pair
swap :: (b, a) -> (a, b)
swap (x, y) = (y, x)

pairUp::a->b->(a,b)
pairUp x y = (x, y)

-- Extends a pair to a triple
ext_P_to_T::(a,b)->c->(a,b,c)
ext_P_to_T (x, y) z = (x, y, z)

-- Projections for triples
fstT :: (a, b, c) -> a
fstT (x, _, _) = x
sndT :: (a, b, c) -> b
sndT (_, y, _) = y
thdT :: (a, b, c) -> c
thdT (_, _, z) = z

-- Projections for quadruples
fst_Q :: (a, b, c, d) -> a
fst_Q (x, _, _, _) = x

-- Combines triples with an operator
combineTwOp op (x, y, z) (x', y' , z') = (op x x', op y y', op z z')
combineTwAppend = combineTwOp (++) 
combineTwInsert::(Ord a1, Ord a2, Ord a3) =>(a1, a2, a3) -> ([a1], [a2], [a3]) -> ([a1], [a2], [a3])
combineTwInsert (x, y, z) (x', y' , z') = (insert x x', insert y y', insert z z')
combineTwIntoS::(Eq a, Eq b, Eq c)=>(a, b, c) -> (Set a, Set b, Set c) -> (Set a, Set b, Set c)
combineTwIntoS (x, y, z) (x', y' , z') =(x `intoSet` x', y `intoSet` y', z `intoSet` z')

-- A quadruple with empty lists
nilQl :: ([a1], [a2], [a3], [a4])
nilQl = ([], [], [], [])
nilQS:: (Set a1, Set a2, Set a3, Set a4)
nilQS = (nil, nil, nil, nil)

-- Makes quadruple out of an element and a triple
makeQFrTFst :: a -> (b, c, d) -> (a, b, c, d)
makeQFrTFst x (y, z, w) = (x, y, z, w)

-- Combines quadruples with an operator
combineQwOp op (x, y, z, w) (x', y' , z', w') = (op x x', op y y', op z z', op w w')
combineQwAppend = combineQwOp (++) 
combineQwUnion :: (Eq a1, Eq a2, Eq a3, Eq a4) =>(Set a1, Set a2, Set a3, Set a4)->(Set a1, Set a2, Set a3, Set a4)-> (Set a1, Set a2, Set a3, Set a4)
combineQwUnion (x, y, z, w) (x', y' , z', w') = (x `union` x', y `union` y', z `union` z', w `union` w')
combineQwInsert :: (Ord a1, Ord a2, Ord a3, Ord a4) => (a1, a2, a3, a4) -> ([a1], [a2], [a3], [a4]) -> ([a1], [a2], [a3], [a4])
combineQwInsert (x, y, z, w) (x', y' , z', w') = (insert x x', insert y y', insert z z', insert w w')
combineQwIntoS (x, y, z, w) (x', y' , z', w') = (x `intoSet` x', y `intoSet` y', z `intoSet` z', w `intoSet` w')
combineQWUnionLs :: (Eq a1, Eq a2, Eq a3, Eq a4) =>[(Set a1, Set a2, Set a3, Set a4)] -> (Set a1, Set a2, Set a3, Set a4)
combineQWUnionLs = foldr combineQwUnion nilQS

-- Maps a function onto a triple
mapP :: (a -> b) -> (a, a) -> (b, b)
mapP f (x, y) = (f x, f y)
mapT :: (a -> c) -> (a, a, a) -> (c, c, c)
mapT f (x, y, z) = (f x, f y, f z)

-- Indexing within  a list
--kth :: Int -> [a] -> a
--kth k (x:xs) = if k == 0 then x else kth (k-1) xs

equalLs::(Eq a)=>[a]->[a]->Bool
equalLs [][] = True
equalLs _ [] = False
equalLs [] _ = False
equalLs (x:xs) (y:ys) 
   | x == y = equalLs xs ys
   | otherwise = False

quicksortp :: (a->a->Bool)->[a] -> [a]    
quicksortp _ [] = []    
quicksortp p (x:xs) =     
    let smallerSorted = quicksortp p (filter (`p` x) xs)  
        biggerSorted = quicksortp p (filter (\y-> not (y `p` x)) xs)   
    in  smallerSorted ++ [x] ++ biggerSorted 

quicksort :: (Ord a) => [a] -> [a]    
quicksort = quicksortp (<=)

--quicksort [] = []    
--quicksort (x:xs) =     
--    let smallerSorted = quicksort (filter (<=x) xs)  
--        biggerSorted = quicksort (filter (>x) xs)   
--    in  smallerSorted ++ [x] ++ biggerSorted 


applyPToP :: (t1 -> a, t2 -> b) -> (t1, t2) -> (a, b)
applyPToP (f, g)(x, y)= (f x, g y) 

butLast :: [a] -> [a]
butLast l = take (length l - 1) l

toIdxC::Eq a=>[a]->[(a, Int)]
toIdxC xs = toIdxC' xs 0
    where  toIdxC' [] _ = []
           toIdxC' (x:xs) k = (x, k):toIdxC' xs (k+1)

--dups :: Eq a => [a] -> [a]
--dups [] = []
--dups (x:xs) 
--   | x `elem` xs  = x:(dups xs)
--   | otherwise    = dups xs

--gapp :: (Foldable t) => t [a] -> [a]
--gapp = foldr (++) []

replace :: Eq t => t -> t -> [t] -> [t]
replace x y [] = []
replace x y (z:zs) 
   | x == z    = y:(replace x y zs)
   | otherwise = z:(replace x y zs)

-- Checks whether a list has unique values
--unique :: (Foldable t, Eq a) => t a -> Bool
--unique xs = foldr (\x br->if x `elem` xs then False else br) True xs
--instance Unique [] where
unique :: Eq a => [a] -> Bool
unique [] = True
unique (x:xs) = if x `elem` xs then False else unique xs

test1 = combineTwInsert (1, 2, 3) ([2, 3], [4, 5], [6, 7])
test2 = combineQwInsert (1, 2, 3, 4) ([2, 3], [4, 5], [6, 7], [8, 9])

-- Gives elements of a set which are duplicated
dupsL :: Eq a => [a] -> [a]
dupsL [] = []
dupsL (x:xs) 
   | x `elem` xs  = x:dupsL xs
   | otherwise    = dupsL xs