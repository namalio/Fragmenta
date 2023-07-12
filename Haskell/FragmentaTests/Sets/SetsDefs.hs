
module FragmentaTests.Sets.SetsDefs
where

import Test.QuickCheck
import Sets ( set, Set )

instance (Arbitrary a, Eq a)=>Arbitrary (Set a) where
    arbitrary :: Gen (Set a)
    arbitrary = do set <$> (arbitrary :: Gen [a])

-- :: (Arbitrary a, Eq a) => Int->Gen (Set a)
--arbitrarySet 0 = return EmptyS
--arbitrarySet k = do
--    s <- arbitrarySet (k-1)
--    x <- genUnique s
--    return $ Set x s

--genUnique :: (Arbitrary a, Eq a)=>Set a->Gen a
--genUnique s = arbitrary  `suchThat` (`notElem` s)
--    do 
--    l <- fmap (take n . nub) (infiniteListOf arbitrary)
--    return $ set l
--    = do
--        ts <-(arbitrary::Gen [a])
--        return (set ts)

--instance Arbitrary (Set (Int, Int)) where
--    arbitrary :: Gen (Set (Int, Int))
--    arbitrary = do
--        xs <- (arbitrary::Gen [Int])
--        ys <- (arbitrary::Gen [Int])
--        return (set $ zip xs ys)