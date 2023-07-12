------------------
-- Module: 'Mult'
-- Description: Tests which exercises multiplicity module
-- Author: Nuno Amálio
-----------------
import Mult
import SimpleFuns
import ErrorAnalysis
import Sets
import FragmentaTests.Mult.MultCommon

eval_expectation et True = if et == nile then "(OK)" else "(Fail)"
eval_expectation et False = if et /= nile then "(OK)" else "(Fail)"

eval_test et b = eval_expectation et b 
    ++ if et == nile then " No errors!" else " The following errors were found:\n" ++ (showErr et) 

test_one = do
    let et1 = check_multOk "Assoc1" (fst_T r1_s1) (snd_T r1_s1) (thd_T r1_s1) (singles $ msole_k 1) (singles $ msole_k 1)
    putStrLn $ eval_test et1 True
    let et2 = check_multOk "Assoc1" (fst_T r1_s1) (snd_T r1_s1) (thd_T r1_s1) (singles mopt) (singles mopt)
    putStrLn $ eval_test et2 True
    let et3 = check_multOk "Assoc1" (fst_T r1_s1) (snd_T r1_s1) (thd_T r1_s1) (singles msole_many) (singles msole_many)
    putStrLn $ eval_test et3 True
    let et4 = check_multOk "Assoc1" (fst_T r1_s1) (snd_T r1_s1) (thd_T r1_s1) (singles mopt) (singles $ mrange 2 mmany)
    putStrLn $ eval_test et4 False
    let et5 = check_multOk "Assoc2" (fst_T r1_s2) (snd_T r1_s2) (thd_T r1_s2) (singles $ msole_k 1) (singles $ msole_k 1)
    putStrLn $ eval_test et5 False

test_two = do
    let et1 = check_multOk "Assoc3" (fst_T r2_s1) (snd_T r2_s1) (thd_T r2_s1) (singles $ msole_k 1) (singles $ msole_k 1)
    putStrLn $ eval_test et1 False
    let et2 = check_multOk "Assoc3" (fst_T r2_s1) (snd_T r2_s1) (thd_T r2_s1) (singles mopt) (singles mopt)
    putStrLn $ eval_test et2 False
    let et3 = check_multOk "Assoc3" (fst_T r2_s1) (snd_T r2_s1) (thd_T r2_s1) (singles mopt) (singles $ mrange 1 mmany)
    putStrLn $ eval_test et3 True
    let et4 = check_multOk "Assoc4" (fst_T r2_s2) (snd_T r2_s2) (thd_T r2_s2) (singles mopt) (singles $ mrange 1 mmany)
    putStrLn $ eval_test et4 False

test_three = do
    let et1 = check_multOk "Assoc5" (fst_T r3_s1) (snd_T r3_s1) (thd_T r3_s1) (singles mopt) (set [msole_k 0, msole_k 2])
    putStrLn $ eval_test et1 True
    let et2 = check_multOk "Assoc6" (fst_T r3_s1) (snd_T r3_s1) (thd_T r3_s1) (singles $ msole_k 1) (set [msole_k 0, msole_k 2])
    putStrLn $ eval_test et2 False
    --putStrLn . show $ multOk (fst_T r4_s1) (snd_T r4_s1) (thd_T r4_s1) (Mc $ mopt) (Ml $ [msole_k 0, msole_k 2])
    let et3 = check_multOk "Assoc7" (fst_T r4_s1) (snd_T r4_s1) (thd_T r4_s1) (singles mopt) (set [msole_k 0, msole_k 2])
    putStrLn $ eval_test et3 False
    --putStrLn . show $ multOk (fst_T r4_s1) (snd_T r4_s1) (thd_T r4_s1) [mopt] [msole_k 0] 
    --putStrLn . show $ multOk (fst_T r4_s1) (snd_T r4_s1) (thd_T r4_s1) [mopt] [msole_k 2] 
    --putStrLn . show $ anybounded (fst_T r4_s1) (snd_T r4_s1) [msole_k 0, msole_k 2]
    --multOk (fst_T r4_s1) (snd_T r4_s1) (thd_T r4_s1) [mopt] [msole_k 0, msole_k 2]
    let et4 = check_multOk "Assoc8" (fst_T r4_s1) (snd_T r4_s1) (thd_T r4_s1) (singles mopt) (singles mopt)
    putStrLn $ eval_test et4 True

main :: IO ()
main = do
    test_one
    test_two
    test_three
