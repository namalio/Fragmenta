module SimpleFuns(swap, pair_up, equalLs, quicksort, fst_T, snd_T, thd_T, fst_Q, mapT, applyPToP, butLast, 
    ext_P_to_T, toIdxC, combineTwAppend, combineTwInsert, combineQwInsert, combineQwAppend, combineQwUnion, 
    makeQFrTFst, nilQl,  gapp, replace, unique) where

import Sets ( insert, union )

--inverts the pair
swap :: (b, a) -> (a, b)
swap (x, y) = (y, x)

pair_up::a->b->(a,b)
pair_up x y = (x, y)

-- Extends a pair to a triple
ext_P_to_T::(a,b)->c->(a,b,c)
ext_P_to_T (x, y) z = (x, y, z)

-- Projections for triples
fst_T :: (a, b, c) -> a
fst_T (x, _, _) = x
snd_T :: (a, b, c) -> b
snd_T (_, y, _) = y
thd_T :: (a, b, c) -> c
thd_T (_, _, z) = z

-- Projections for quadruples
fst_Q :: (a, b, c, d) -> a
fst_Q (x, _, _, _) = x

-- Combines triples with an operator
combineTwOp op (x, y, z) (x', y' , z') = (op x x', op y y', op z z')
combineTwAppend = combineTwOp (++) 
combineTwInsert (x, y, z) (x', y' , z') = (insert x x', insert y y', insert z z')

-- A quadruple with empty lists
nilQl :: ([a1], [a2], [a3], [a4])
nilQl = ([], [], [], [])

-- Makes a quadruple out of an element and a triple
makeQFrTFst :: a -> (b, c, d) -> (a, b, c, d)
makeQFrTFst x (y, z, w) = (x, y, z, w)

-- Combines quadruples with an operator
combineQwOp op (x, y, z, w) (x', y' , z', w') = (op x x', op y y', op z z', op w w')
combineQwAppend = combineQwOp (++) 
combineQwUnion (x, y, z, w) (x', y' , z', w') = (x `union` x', y `union` y', z `union` z', w `union` w')
combineQwInsert (x, y, z, w) (x', y' , z', w') = (insert x x', insert y y', insert z z', insert w w')

-- Maps a function onto a triple
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

quicksort :: (Ord a) => [a] -> [a]    
quicksort [] = []    
quicksort (x:xs) =     
    let smallerSorted = quicksort (filter (<=x) xs)  
        biggerSorted = quicksort (filter (>x) xs)   
    in  smallerSorted ++ [x] ++ biggerSorted 

applyPToP (f, g)(x, y)= (f x, g y) 

butLast l = take ((length l) - 1) l

toIdxC::Eq a=>[a]->[(a, Int)]
toIdxC xs = toIdxC' xs 0
    where  toIdxC' [] _ = []
           toIdxC' (x:xs) k = (x, k):toIdxC' xs (k+1)

gapp ls = foldr (++) [] ls

replace x y [] = []
replace x y (z:zs) 
   | x == z    = y:(replace x y zs)
   | otherwise = z:(replace x y zs)

-- Checks whether a list has unique values
unique [] = True
unique (x:xs) = if x `elem` xs then False else unique xs

test1 = combineTwInsert (1, 2, 3) ([2, 3], [4, 5], [6, 7])
test2 = combineQwInsert (1, 2, 3, 4) ([2, 3], [4, 5], [6, 7], [8, 9])