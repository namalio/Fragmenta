module Sets (subseteq, seteq, diff, union, gunion, dups, no_dups, intersec, gintersec, insert, disjoint) where

subseteq :: (Foldable t1, Foldable t2, Eq a) => t1 a -> t2 a -> Bool
subseteq s1 s2 = all (`elem` s2) s1

seteq :: (Foldable t2, Foldable t1, Eq a) => t2 a -> t1 a -> Bool
seteq l1 l2 = (subseteq l1 l2) && (subseteq l2 l1) 

diff :: Eq a => [a] -> [a] -> [a]
diff [] b = []
diff a [] = a
diff (x:xs) b 
  | x `elem` b = diff xs b
  | otherwise  = x:(diff xs b)

-- inserts only if not in the list
insert :: Eq a => a -> [a] -> [a]
insert e l 
   | e `elem` l = l
   | otherwise = e:l

union :: Eq a => [a] -> [a] -> [a]
union sa sb = foldr insert [] (sa++sb)

-- generalised union
gunion :: (Foldable t, Eq a) => t [a] -> [a]
gunion ss = foldr union [] ss

-- removes duplicates
no_dups [] = []
no_dups [x] = [x]
no_dups (x:xs) 
   | x `elem` xs = no_dups xs
   | otherwise = x:(no_dups xs)

-- intersection
intersec _ [] = []
intersec [] _ = []
intersec (x:xs) ys 
   | x `elem` ys  = x:(intersec xs ys)
   | otherwise    = (intersec xs ys)

-- generalised intersection
gintersec ss = if null ss then [] else foldr (\s si->(s `intersec` si)) (head ss) (tail ss)

dups [] = []
dups (x:xs) 
   | x `elem` xs  = x:(dups xs)
   | otherwise    = dups xs

disjoint_set xs = null $ dups xs

disjoint [] = True
disjoint (s:ss) = 
    (foldr (\s' si->(null $ s `intersec` s') && si) True ss) && disjoint ss 