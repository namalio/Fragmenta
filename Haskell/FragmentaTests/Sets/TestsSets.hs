
--import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Sets (singles, set, card, toList, intoSet, reduce, sminus, union, gunion, gintersec, intersec, Set (EmptyS),
            filterS, disjoint, power, intoSet)
import FragmentaTests.Sets.SetsDefs
import TheNil
import Data.List(nub)
import SimpleFuns ( dupsL )

--       ts <-(arbitrary::Gen [a])
--       return (set ts)

--instance (Arbitrary a, Eq a)=>Arbitrary(Set a) where
--    arbitrary :: (Arbitrary a, Eq a) => Gen (Set a)
--    arbitrary = sized arbitrarySet

--arbitrarySet :: (Arbitrary a, Eq a) => Int->Gen (Set a)
--arbitrarySet n = do 
--    l <- fmap (take n . nub) (infiniteListOf arbitrary)
--    return $ set l


testSetEq::Assertion
testSetEq = assertBool "An empty set is equal to itself" ((nil::Set Int) == (EmptyS::Set Int))

propSetEq1::Eq a=>Set a->Bool
propSetEq1 a = a == a

propSetEq2::Eq a=>Set a->Bool
propSetEq2 a = if null a then a == nil else a /= nil

propSetEq3::Eq a=>Set a->Bool
propSetEq3 xs = xs == set (reverse $ toList xs)

--propSetEq2::Set Int->Set Int->Property
--propSetEq2 a b = (a == b) ==> a <= b && b <= a

--propSetEq2::Set Int->Set Int->Property
--propSetEq2 a b = (a == b) ==> b <= a

--propSetEq4::Set Int->Set Int->Set Int->Property
--propSetEq4 a b c = a == b && b == c ==> a == c

--propSetEqEmpty::Bool
--propSetEqEmpty = (nil::Set Int) == (conss []::Set Int)

--propCard1::Bool
--propCard1 = card (nil::Set Int) == 0

--propCard2::Bool
--propCard2 = card (conss ([]::[Int])) == 0

testCard1::Assertion
testCard1 = assertEqual "Cardinality of empty set" (card(nil::Set Int)) 0

propCard1::Eq a=>a->Bool
propCard1 k = card(singles[k]) == 1 

propCard2::Eq a=>a->Set a->Bool
propCard2 k s = card (k `intoSet` s) == if k `elem` s then card s else card s + 1

propElem1::Eq a=>a->Bool
propElem1 k = k `elem` (singles k)

propElem2::Eq a=>a->Bool
propElem2 k = k `notElem` (nil::Set a)

propElem3::Eq a=>a->Set a->Bool
propElem3 x xs = x `elem` (x `intoSet` xs)

propElem4::Eq a=>Set a->Bool
propElem4 xs = all (`elem` xs) xs
--propset2 x xs = x `elem` xs ==> x `elem` set xs 

propElem5::Eq a=>a->Set a->Bool
propElem5 x xs = x `elem` xs || x `notElem` xs 

propIntoSet1::Eq a=>a->Set a->Property
propIntoSet1 x xs = x `elem` xs ==> x `intoSet` xs == xs 

propIntoSet2::Eq a=>a->Set a->Property
propIntoSet2 x xs = not (x `elem` xs) ==> x `elem` (x `intoSet` xs)

propIntoSet3::Eq a=>a->Set a->Bool
propIntoSet3 x xs = x `elem` (x `intoSet` xs)

propIntoSet4::Eq a=>Set a->a->a->Bool
propIntoSet4 s x y = y `intoSet` (x `intoSet` s) ==  x `intoSet` (y `intoSet` s)

propToList1::Eq a=>Set a->Bool
propToList1 as = all (`elem` (toList as)) as

propToList2::Eq a=>Set a->Bool
propToList2 as = dupsL (toList as) == []

testToList1::Assertion
testToList1 = assertEqual "The list of an empty set" (toList (nil::Set Int)) []

testsBasic :: TestTree
testsBasic = testGroup "tests related to basic set operations" [
    testCase "Equality on emptysets" testSetEq
    , testProperty "Equality on sets" (propSetEq1::Set Int->Bool)
    , testProperty "Equality on sets" (propSetEq2::Set Int->Bool)
    , testProperty "Equality on sets" (propSetEq3::Set Int->Bool)
    , testCase "Cardinality of empty set" testCard1
    , testProperty "Cardinality of a singleton set" (propCard1::Int->Bool)
    , testProperty "Cardinality on a general set" (propCard2::Int->Set Int->Bool)
    , testProperty "Element of a singleton set" (propElem1::Int->Bool)
    , testProperty "No Element of an empty set" (propElem2::Int->Bool)
    , testProperty "Element of a general set" (propElem3::Int->Set Int->Bool)
    , testProperty "All the elements of a general set" (propElem4::Set Int->Bool)
    , testProperty "Either an element of some set or not" (propElem5::Int->Set Int->Bool)
    , testProperty "Adding an element into a set that already contains the element" (propIntoSet1::Int->Set Int->Property)
    , testProperty "Once a new element is added, it becomes part of the set" (propIntoSet2::Int->Set Int->Property)
    , testProperty "An added element is always a member of the resulting set" (propIntoSet3::Int->Set Int->Bool)
    , testProperty "Order of insertion does not matter" (propIntoSet4::Set Int->Int->Int->Bool)
    , testProperty "Elements of a set are also elements of the list resulting from the set" (propToList1::Set Int->Bool)
    , testProperty "A list resulting from a set has no duplicates" (propToList2::Set Int->Bool)
    , testCase "list of an empty set" testToList1
    ]

propSubsetEq1::Eq a=>Set a->Bool
propSubsetEq1 = (nil <=)

propSubsetEq2::Eq a=>Set a->Bool
propSubsetEq2 s = s<=s

propSubsetEq3::Eq a=>Set a->Property
propSubsetEq3 s = 
    not (null s) ==> all (\e->singles e <= s) s

propSubsetEq4::Eq a=>a->Set a->Property
propSubsetEq4 x s = x `notElem` s ==> not $ (x `intoSet` s) <= s

testsSubsets :: TestTree
testsSubsets = testGroup "tests related to subsets" [
    testProperty "Emptyset is subset of any set" (propSubsetEq1::Set Int->Bool)
    , testProperty "Any set is subset of itself" (propSubsetEq2::Set Int->Bool)
    , testProperty "The singletons formed by the elemments of the set are subsets of the original set" (propSubsetEq3::Set Int->Property)
    , testProperty "A set cannot be a subset of the set with a new element" (propSubsetEq4::Int->Set Int->Property)
    ]


--propSetElem2::Set Int->Property
--propSetElem2 as = (not . null $ as) ==> all (\a->a `elem` as) as


propSetMinus1::Eq a=>Set a->Bool
propSetMinus1 s = s `sminus` nil == s

propSetMinus2::Eq a=>Set a->Bool
propSetMinus2 s = null $ nil `sminus` s

propSetMinus3::Eq a=>Set a->Bool
propSetMinus3 s = null $ s `sminus` s

propSetMinus4::Eq a=>Set a->Property
propSetMinus4 s = 
    not (null s) ==> all(\e-> s `sminus` singles e ==  filterS (e /=) s) s

testsSMinus :: TestTree
testsSMinus = testGroup "tests related to set difference" [
    testProperty "Taking the Emptyset from any set gives the set itself" (propSetMinus1::Set Int->Bool)
    , testProperty "Taking any set from the Emptyset gives the empty set" (propSetMinus2::Set Int->Bool)
    , testProperty "Taking a set from itself (difference) gives the empty set" (propSetMinus3::Set Int->Bool)
    , testProperty "Removing a singleton made from any element of a set from the set itself gives the set without the element" (propSetMinus4::Set Int->Property)
    ]

propSetUnion1::Eq a=>Set a->Set a->Bool
propSetUnion1 a b = a `union` b == b `union` a

propSetUnion2::Eq a=>Set a->Bool
propSetUnion2 s = s `union` nil == s

propSetUnion3::Eq a=>Set a->Bool
propSetUnion3 s = s `union` s == s

propSetUnion4::Eq a=>Set a->Set a->Bool
propSetUnion4 a b = (a `union` b) `sminus` b == a `sminus` b

propSetUnion5::Eq a=>Set a->Set a->Bool
propSetUnion5 a b = gunion [a, b] == a `union` b 

testsSUnion :: TestTree
testsSUnion = testGroup "tests related to set union" [
    testProperty "Union is commutative" (propSetUnion1::Set Int->Set Int->Bool)
    , testProperty "The union of set with the Emptyset is the set" (propSetUnion2::Set Int->Bool)
    , testProperty "The union of set with itself is the set" (propSetUnion3::Set Int->Bool)
    , testProperty "A U B \\ B = A \\ B" (propSetUnion4::Set Int->Set Int->Bool)
    , testProperty "The generalised union of two sets is their union" (propSetUnion5::Set Int->Set Int->Bool)
    ]

propIntersec1::Eq a=>Set a->Set a->Bool
propIntersec1 a b = a `intersec` b == b `intersec` a

propIntersec2::Eq a=>Set a->Bool
propIntersec2 s = s `intersec` nil == nil

propIntersec3::Eq a=>Set a->Bool
propIntersec3 s = s `intersec` s == s

propIntersec4::Set Int->Set Int->Set Int->Bool
propIntersec4 s1 s2 s3 = s1 `intersec` (s2 `union` s3) == (s1 `intersec` s2) `union` (s1 `intersec` s3)

propIntersec5::Set Int->Set Int->Set Int->Bool
propIntersec5 s1 s2 s3 = s1 `intersec` (s2 `sminus` s3) == (s1 `sminus` s3) `intersec` (s2 `sminus` s3)

propCardUnion::Set Int->Set Int->Bool
propCardUnion a b = card (a `union` b) == card a + card b - card(a `intersec` b)

propGIntersec::Set Int->Set Int->Bool
propGIntersec a b = gintersec [a, b] == a `intersec` b 

testsInsersection :: TestTree
testsInsersection = testGroup "tests related to set intersection" [
    testProperty "Intersection is commutative" (propIntersec1::Set Int->Set Int->Bool)
    , testProperty "The intersection of a set with the Emptyset is the emptyset" (propIntersec2::Set Int->Bool)
    , testProperty "The intersection of a set with itself is the set" (propIntersec3::Set Int->Bool)
    , testProperty "A ∩ (B U C) = (A ∩ B) U (A ∩ C) " (propIntersec4::Set Int->Set Int->Set Int->Bool)
    , testProperty "A ∩ (B\\C) = (A\\B) ∩ (B\\C)" (propIntersec5::Set Int->Set Int->Set Int->Bool)
    , testProperty "Cardinaliy of the union is the is the cardinality of the sets minus the cardinality of the intersection" (propCardUnion::Set Int->Set Int->Bool)
    , testProperty "The generalised intersection of two sets is their intersection" (propGIntersec::Set Int->Set Int->Bool)
    ]

propDisjoint::Eq a=>Set a->Set a->Bool
propDisjoint a b = if disjoint [a, b] then null $ a `intersec` b else not . null $ a `intersec` b

propPower1::Eq a=>Set a->Property
propPower1 as = length as <= 9 ==> card (power as) == 2^(card as)

propPower2::Eq a=>Set a->Property
propPower2 s = length s <= 9 ==> s `elem` power s

propPower3::Eq a=>Set a->Property
propPower3 as = length as < 8 ==> as `elem` pa && nil `elem` pa && all (\a->singles a `elem` pa) as
   where pa = power as 

testPowerEmptyS::Assertion
testPowerEmptyS = assertEqual "Power of empty set" (power (nil::Set Int)) (singles (nil::Set Int))

testPowerSingleton::Assertion
testPowerSingleton = assertEqual "Power of singleton set" (power (singles 5)) (set[singles 5, nil])

testPower::Assertion
testPower = assertBool "power of a reasonably sized set" (all (`elem` ps) ps)
            where ps = power $ set [1..9]

testsPower :: TestTree
testsPower = testGroup "tests related to disjointness and powersets" [
    testProperty "Two sets are disjoint if and only if their interction is empty" (propDisjoint::Set Int->Set Int->Bool)
    , testProperty "The cardinality of a powerset is 2 to the power of the cardinality of the set" (propPower1::Set Int->Property)
    , testProperty "Any set is an element of its powerset" (propPower2::Set Int->Property)
    , testProperty "The Empty set, the set itself, and any singleton built from elements of a set are elements of a powerset" (propPower3::Set Int->Property)
    , testCase "Powerset of emptyset" testPowerEmptyS
    , testCase "Powerset of singleton set" testPowerSingleton
    , testCase "Powerset of a reasonably sized set" testPower
    ]

tests :: TestTree
tests =  testGroup "Overall tests" [
    testsBasic
    , testsSubsets
    , testsSMinus
    , testsSUnion
    , testsInsersection 
    , testsPower
    ]

main :: IO ()
main = do
    defaultMain tests
--    quickCheck propsingles1
--    quickCheck propSetEq1
--    quickCheck propSetEq2
    --quickCheck propSetEq3
    --quickCheck propSetEq4
--   quickCheck propset1
--    quickCheck propset2
--    quickCheck propset3
--    quickCheck propToList
--    quickCheck propCard1
--    quickCheck propCard2
--    quickCheck propSubsetEq1
--   quickCheck propsinglessSubsetEq
--    quickCheck propLargerNotSubsetEq
--    quickCheck propSetElem1
--    quickCheck propSetElem2
--    quickCheck propintoSet1
--   quickCheck propintoSet2
--    quickCheck propSetElemintoSet
--    quickCheck propSetMinus1
--    quickCheck propSetMinus2
--    quickCheck propSetMinus3
--    quickCheck propSetMinus4
--    quickCheck propUnion1
--    quickCheck propUnion2
--    quickCheck propUnion3
--    quickCheck propUnion4
--    quickCheck propUnionSetMinus
--    quickCheck propGUnion
--    quickCheck propIntersec1
--    quickCheck propIntersec2
--    quickCheck propIntersec3
--    quickCheck propIntersec4
--    quickCheck propIntersecUnion
--    quickCheck propIntersecSetMinus
--    quickCheck propCardUnion
--    quickCheck propGIntersec
--    quickCheck propDisjoint1
--    quickCheck propDisjoint2
--    quickCheck propPower1
--    quickCheck propPower2