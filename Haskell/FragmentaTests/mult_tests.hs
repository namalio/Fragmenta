------------------
-- Module: 'Mult'
-- Description: Tests which exercises multiplicity module
-- Author: Nuno Amálio
-----------------
import Mult
import SimpleFuns
import ErrorAnalysis

r1 = [("A1", "B1"), ("A2", "B2")]
r1_s1 = (r1, ["A1", "A2"], ["B1", "B2"])
r1_s2 = (r1, ["A1", "A2", "A3"], ["B1", "B2"])

r2 = [("A1", "B1"), ("A2", "B2"), ("A2", "B3")]
r2_s1 = (r2, ["A1", "A2"], ["B1", "B2", "B3", "B4"])
r2_s2 = (r2, ["A1", "A2", "A3"], ["B1", "B2", "B3", "B4"])


eval_expectation et True = if et == nile then "(OK)" else "(Fail)"
eval_expectation et False = if et /= nile then "(OK)" else "(Fail)"

eval_test et b = eval_expectation et b 
    ++ if et == nile then " No errors!" else " The following errors were found:\n" ++ (show_err et) 

test_one = do
    let et1 = check_multOk (fst_T r1_s1) (snd_T r1_s1) (thd_T r1_s1) (msole_k 1)(msole_k 1)
    putStrLn $ eval_test et1 True
    let et2 = check_multOk (fst_T r1_s1) (snd_T r1_s1) (thd_T r1_s1) (mopt) (mopt)
    putStrLn $ eval_test et2 True
    let et3 = check_multOk (fst_T r1_s1) (snd_T r1_s1) (thd_T r1_s1) (msole_many) (msole_many)
    putStrLn $ eval_test et3 True
    let et4 = check_multOk (fst_T r1_s1) (snd_T r1_s1) (thd_T r1_s1) (mopt) (mrange 2 mmany)
    putStrLn $ eval_test et4 False
    let et5 = check_multOk (fst_T r1_s2) (snd_T r1_s2) (thd_T r1_s2) (msole_k 1)(msole_k 1)
    putStrLn $ eval_test et5 False

test_two = do
    let et1 = check_multOk (fst_T r2_s1) (snd_T r2_s1) (thd_T r2_s1) (msole_k 1)(msole_k 1)
    putStrLn $ eval_test et1 False
    let et2 = check_multOk (fst_T r2_s1) (snd_T r2_s1) (thd_T r2_s1) (mopt) (mopt)
    putStrLn $ eval_test et2 False
    let et3 = check_multOk (fst_T r2_s1) (snd_T r2_s1) (thd_T r2_s1) (mopt) (mrange 1 mmany)
    putStrLn $ eval_test et3 True
    let et4 = check_multOk (fst_T r2_s2) (snd_T r2_s2) (thd_T r2_s2) (mopt) (mrange 1 mmany)
    putStrLn $ eval_test et4 False

main = do
    test_one
    test_two
