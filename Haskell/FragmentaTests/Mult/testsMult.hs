------------------
-- Module: 'Mult'
-- Description: Tests which exercises multiplicity module
-- Author: Nuno Amálio
-----------------
import Mult
import SimpleFuns
import ErrorAnalysis
import Sets
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import FragmentaTests.Mult.MultCommon

genMVNum::Int->Gen MultVal
genMVNum k = elements [mval n|n<-[0..k]]

genMVMany::Gen MultVal
genMVMany = elements [mmany]

genMV::Gen MultVal
genMV = do
    k <- getSize
    oneof([genMVNum k,genMVMany])

instance Arbitrary MultVal where
  arbitrary = genMV

genMCAny::Gen MultC
genMCAny = do
    k <- getSize
    mv<-genMVNum k
    return $ msingle mv

genMCRange::Gen MultC
genMCRange = do
    lb<-fmap abs arbitrary 
    mv<-genMV `suchThat` ((mval lb) <=)
    return $ mrange lb mv

genMC::Gen MultC
genMC = oneof([return mopt, return $ msole_k 1, return $ msole_many, genMCAny, genMCRange])

instance Arbitrary MultC where
  arbitrary = genMC

propMultV1::Int->Property
propMultV1 k = k < 0 ==> not . mvok . mval $ k

propMultV2::Int->Property
propMultV2 k = k >= 0 ==> mvok . mval $ k

propMultV3::MultVal->Bool
propMultV3 mv = mv <= mmany

testsMultVal :: TestTree
testsMultVal = testGroup "Multiplicity values" [
    testProperty "Negative integers make invalid multiplicities" propMultV1
    , testProperty "Natural numbers make valid multiplicities" propMultV2
    , testProperty "Any value multiplicity is less than many" propMultV3
    ]

testMC1::Assertion
testMC1 = assertBool "0 <= *" (msole_k 0 <= msole_many)

testMC2::Assertion
testMC2 = assertBool "¬ * <= 0" (not $ msole_many <= msole_k 0)

testMC3::Assertion
testMC3 = assertBool "0..1 <= *" (mopt <= msole_many)

testMC4::Assertion
testMC4 = assertBool "¬ *  <= 0..1" (not $ msole_many <= mopt)

testMC5::Assertion
testMC5 = assertBool "3..5 <= *" (mrange 3 (mval 5) <= msole_many)

testMC6::Assertion
testMC6 = assertBool "¬ * <= 3..5" (not $ msole_many <= (mrange 3 (mval 5)))

testMC7::Assertion
testMC7 = assertBool "3..* <= *" (mrange 3 mmany <= msole_many)

testMC8::Assertion
testMC8 = assertBool "¬ * <= 3..*" (not $ msole_many <= mrange 3 mmany)

testMC9::Assertion
testMC9 = assertBool "0 <= 0..1" (msole_k 0 <= mopt)

testMC10::Assertion
testMC10 = assertBool "1 <= 0..1" (msole_k 1 <= mopt)

testMC11::Assertion
testMC11 = assertBool "¬2 <= 0..1" (not $ msole_k 2 <= mopt)

propMC1::MultC->Bool
propMC1 mc = mc <= msole_many

propMC2::MultC->Property
propMC2 mc = (not. isMultManyMC $ mc)  ==> not $ msole_many <= mc 

testsMultC :: TestTree
testsMultC = testGroup "Multiplicity constraints" [
    testCase "0 <= *" testMC1
    , testCase "¬ * <= 0" testMC2
    , testCase "0..1 <= *" testMC3
    , testCase "¬ *  <= 0..1" testMC4
    , testCase "3..5 <= *" testMC5
    , testCase "¬ * <= 3..5" testMC6
    , testCase "3..* <= *" testMC7
    , testCase "¬ * <= 3..*" testMC8
    , testCase "0 <= 0..1" testMC9
    , testCase "1 <= 0..1" testMC10
    , testCase "¬2 <= 0..1" testMC11
    , testProperty "mc<= *" propMC1
    , testProperty "¬ * <= mc" propMC2
    ]

testM1::Assertion
testM1 = assertBool "{0} <= {*}" (singles (msole_k 0) `mcsLeq` singles(msole_many))

testM2::Assertion
testM2 = assertBool "{0, 1, 2} <= {*}" ((set $ fmap msole_k [0, 1, 2]) `mcsLeq` singles(msole_many))

testM3::Assertion
testM3 = assertBool "{0, 1, 2} <= {0..10}" ((set $ fmap msole_k [0, 1, 2]) `mcsLeq` singles(mrange 0 (mval 10)))

testM4::Assertion
testM4 = assertBool "{1, 2, 3} <= {0..10}" ((set $ fmap msole_k [1, 2, 3]) `mcsLeq` singles(mrange 0 (mval 10)))

testM5::Assertion
testM5 = assertBool "¬{1, 2, 3, 11} <= {0..10}" (not $ set (fmap msole_k [1, 2, 3, 11]) `mcsLeq` singles(mrange 0 (mval 10)))

propM6::[Int]->Property
propM6 ks = (not . null $ ks) ==> set (fmap (msole_k . abs) ks) `mcsLeq` (singles(msole_many))

testsMult :: TestTree
testsMult = testGroup "Multiplicities" [
    testCase "{0} <= {*}" testM1
    , testCase "{0, 1, 2} <= {*}" testM2
    , testCase "{0, 1, 2} <= {0..10}" testM3
    , testCase "{1, 2, 3} <= {0..10}" testM4
    , testCase "¬{1, 2, 3, 11} <= {0..10}" testM5
    , testProperty "{i, j, .., k} <= {*}" propM6
    ]

testAssoc1a::Assertion
testAssoc1a = assertBool "Association one" (multOk (fst_T r1_s1) (snd_T r1_s1) (thd_T r1_s1) (singles $ msole_k 1) (singles $ msole_k 1))

testAssoc1b::Assertion
testAssoc1b = assertBool "Association one" (multOk (fst_T r1_s1) (snd_T r1_s1) (thd_T r1_s1) (singles mopt) (singles mopt))

testAssoc1c::Assertion
testAssoc1c = assertBool "Association one" (multOk (fst_T r1_s1) (snd_T r1_s1) (thd_T r1_s1) (singles msole_many) (singles msole_many))

testAssoc1d::Assertion
testAssoc1d = assertBool "Association one" (not $ multOk (fst_T r1_s1) (snd_T r1_s1) (thd_T r1_s1) (singles mopt) (singles $ mrange 2 mmany))

testAssoc2a::Assertion
testAssoc2a = assertBool "Association two" (not $ multOk (fst_T r1_s2) (snd_T r1_s2) (thd_T r1_s2) (singles $ msole_k 1) (singles $ msole_k 1))

testAssoc3a::Assertion
testAssoc3a = assertBool "Association three" (not $ multOk (fst_T r2_s1) (snd_T r2_s1) (thd_T r2_s1) (singles $ msole_k 1) (singles $ msole_k 1))

testAssoc3b::Assertion
testAssoc3b = assertBool "Association three" (not $ multOk (fst_T r2_s1) (snd_T r2_s1) (thd_T r2_s1) (singles mopt) (singles mopt))

testAssoc3c::Assertion
testAssoc3c = assertBool "Association three" ( multOk (fst_T r2_s1) (snd_T r2_s1) (thd_T r2_s1) (singles mopt) (singles $ mrange 1 mmany))

testAssoc4::Assertion
testAssoc4 = assertBool "Association four " (not $ multOk (fst_T r2_s2) (snd_T r2_s2) (thd_T r2_s2) (singles mopt) (singles $ mrange 1 mmany))

testAssoc5a::Assertion
testAssoc5a = assertBool "Association five " (multOk (fst_T r3_s1) (snd_T r3_s1) (thd_T r3_s1) (singles mopt) (set [msole_k 0, msole_k 2]))

testAssoc5b::Assertion
testAssoc5b = assertBool "Association five " (not $ multOk (fst_T r3_s1) (snd_T r3_s1) (thd_T r3_s1) (singles $ msole_k 1) (set [msole_k 0, msole_k 2]))

testAssoc6a::Assertion
testAssoc6a = assertBool "Association six " (not $ multOk (fst_T r4_s1) (snd_T r4_s1) (thd_T r4_s1) (singles mopt) (set [msole_k 0, msole_k 2]))

testAssoc6b::Assertion
testAssoc6b = assertBool "Association six " (multOk (fst_T r4_s1) (snd_T r4_s1) (thd_T r4_s1) (singles mopt) (singles mopt))

testsMultOk :: TestTree
testsMultOk = testGroup "Multiplicity checking" [
    testCase "Multiplicity of association one: 1 to 1" testAssoc1a
    , testCase "Multiplicity of association one: 0..1 to 0..1" testAssoc1b
    , testCase "Multiplicity of association one: * to *" testAssoc1c
    , testCase "Multiplicity of association one is not 0..1 to 2..*" testAssoc1d
    , testCase "Multiplicity of association two is not 1 to 1" testAssoc2a
    , testCase "Multiplicity of association three is not 1 to 1" testAssoc3a
    , testCase "Multiplicity of association three is not 0..1 to 0..1" testAssoc3b
    , testCase "Multiplicity of association three is 0..1 to 1..*" testAssoc3c
    , testCase "Multiplicity of association four is not 0..1 to 1..*" testAssoc4
    , testCase "Multiplicity of association five is 0..1 to 0, 2" testAssoc5a
    , testCase "Multiplicity of association five is not 1 to 0, 2" testAssoc5b
    , testCase "Multiplicity of association six is not 0..1 to 0, 2" testAssoc6a
    , testCase "Multiplicity of association six is 0..1 to 0..1" testAssoc6b
    ]

--main :: IO ()
--main = do
--    test_one
--    test_two
--    test_three

tests :: TestTree
tests =  testGroup "Overall tests" [
    testsMultVal
    , testsMultC
    , testsMult
    , testsMultOk
    ]

main :: IO ()
main = do
    defaultMain tests