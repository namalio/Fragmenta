module SimpleFuns(swap, pair_up, kth, equalLs, quicksort, fst_T, snd_T, thd_T, fst_Q, mapT, applyPToP, allButLast, 
    toIdxC, combineTwAppend, combineTwInsert, combineQwInsert, combineQwAppend, combineQwUnion, 
    makeQFrTFst, nilQl) where

import Sets

--inverts the pair
swap (x, y) = (y, x)

pair_up::a->b->(a,b)
pair_up x y = (x, y)

-- Projections for triples
fst_T (x, _, _) = x
snd_T (_, y, _) = y
thd_T (_, _, z) = z

-- Projections for quadruples
fst_Q (x, _, _, _) = x

-- Combines triples with an operator
combineTwOp op (x, y, z) (x', y' , z') = (op x x', op y y', op z z')
combineTwAppend = combineTwOp (++) 
combineTwInsert (x, y, z) (x', y' , z') = (insert x x', insert y y', insert z z')

-- A quadruple with empty lists
nilQl = ([], [], [], [])
-- Makes a quadruple out of an element and a triple
makeQFrTFst x (y, z, w) = (x, y, z, w)

-- Combines quadruples with an operator
combineQwOp op (x, y, z, w) (x', y' , z', w') = (op x x', op y y', op z z', op w w')
combineQwAppend = combineQwOp (++) 
combineQwUnion (x, y, z, w) (x', y' , z', w') = (x `union` x', y `union` y', z `union` z', w `union` w')
combineQwInsert (x, y, z, w) (x', y' , z', w') = (insert x x', insert y y', insert z z', insert w w')

-- Maps a function onto a triple
mapT f (x, y, z) = (f x, f y, f z)

-- Does the indexing within  a list
kth k (x:xs) = if k == 0 then x else kth (k-1) xs

equalLs [][] = True
equalLs _ [] = False
equalLs [] _ = False
equalLs (x:xs) (y:ys) 
   | x == y = (equalLs xs ys) 
   | otherwise = False

quicksort :: (Ord a) => [a] -> [a]    
quicksort [] = []    
quicksort (x:xs) =     
    let smallerSorted = quicksort (filter (<=x) xs)  
        biggerSorted = quicksort (filter (>x) xs)   
    in  smallerSorted ++ [x] ++ biggerSorted 

applyPToP (f, g)(x, y)= (f x, g y) 

allButLast l = take ((length l) - 1) l

toIdxC::Eq a=>[a]->[(a, Int)]
toIdxC xs = toIdxC' xs 0
    where  toIdxC' [] _ = []
           toIdxC' (x:xs) k = (x, k):toIdxC' xs (k+1)

test1 = combineTwInsert (1, 2, 3) ([2, 3], [4, 5], [6, 7])
test2 = combineQwInsert (1, 2, 3, 4) ([2, 3], [4, 5], [6, 7], [8, 9])