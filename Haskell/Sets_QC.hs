import Test.QuickCheck
import Sets (subseteq, seteq, diff, insert, union)

propEmptySubsetEqAnything::[Int]->Bool
propEmptySubsetEqAnything = subseteq [] 

propSingletonsSubsetEq::[Int]->Property
propSingletonsSubsetEq s = 
    not (null s) ==> property(all (\e->[e] `subseteq` s) s)

propLargerNotSubsetEq::[Int]->[Int]->Property
propLargerNotSubsetEq s1 s2 =
    length (s2) > length (s1) ==> property(not $ s2 `subseteq` s1)

propSetEqEmpty::Bool
propSetEqEmpty =
    ([]::[Int]) `seteq` ([]::[Int]) 

propSetEqSingleton::Int->Bool
propSetEqSingleton k = [k] `seteq` [k]

propDiff1::[Int]->Bool
propDiff1 s = seteq (diff s []) s

propDiff2::[Int]->Bool
propDiff2 s = null $ diff [] s

propDiff3::[Int]->Bool
propDiff3 s = seteq (diff s s) []

propDiff4::[Int]->Property
propDiff4 s = 
    not (null s) ==> property(all(\e-> (diff s [e]) `seteq` (filter (e /=) s)) s)

propInsert1::Int->Bool
propInsert1 k = seteq (insert k []) [k]

propInsert2::Int->[Int]->Property
propInsert2 k s = 
    k `elem` s ==> property(seteq (insert k s) s)

propInsert3::Int->[Int]->Property
propInsert3 k s = 
    not (k `elem` s) ==> property(seteq (diff (insert k s) [k]) s)

propUnion1::[Int]->Bool
propUnion1 s = seteq (union s []) s

propUnion2::[Int]->Bool
propUnion2 s = seteq (union [] s) s

main :: IO ()
main = do
    quickCheck propEmptySubsetEqAnything
    quickCheck propSingletonsSubsetEq
    quickCheck propLargerNotSubsetEq
    quickCheck propSetEqEmpty
    quickCheck propSetEqSingleton
    quickCheck propDiff1
    quickCheck propDiff2
    quickCheck propDiff3
    quickCheck propDiff4
    quickCheck propInsert1
    quickCheck propInsert2
    quickCheck propInsert3
    quickCheck propUnion1
    quickCheck propUnion2