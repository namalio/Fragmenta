------------------
-- Project: PCs/Fragmenta
-- Module: 'SG_ty_tests'
-- Description: Test which focus on the typing of graphs by SGs
-- Author: Nuno Amálio
-----------------
{-# LANGUAGE UnicodeSyntax #-}


import SGrs
import Grs
import GrswT
import LoadCheckDraw
import CheckUtils
import Utils



def_path = "FragmentaTests/SGTyTests/"
img_path = "FragmentaTests/SGTyTests/img/"

saveDrawings = do
   draw_def def_path img_path "mm_1.sg"
   draw_def def_path img_path "mm_2.sg"
   draw_def def_path img_path "g_1.gwt"
   draw_def def_path img_path "g_2.gwt"
   draw_def def_path img_path "mm_3.sg"
   draw_def def_path img_path "g_3.gwt"
   draw_def def_path img_path "g_4.gwt"
   draw_def def_path img_path "g_5.gwt"
   draw_def def_path img_path "mm_4.sg"
   draw_def def_path img_path "g_6.gwt"
   draw_def def_path img_path "g_7.gwt"
   draw_def def_path img_path "g_8.gwt"
   draw_def def_path img_path "g_9.gwt"
   draw_def def_path img_path "mm_5.sg"
   draw_def def_path img_path "g_10.gwt"
   draw_def def_path img_path "g_11.gwt"

-- evalExpectationStr e r = if e == r then "Ok" else "Fail"

-- check_typing id m g mm b = 
--    let errs = check_typing_g_sg m g mm in
--    if is_wf_ty_g_sg m g mm
--       then putStrLn $ id ++ " is well formed with respect to metamodel (" ++ (evalExpectationStr b True) ++ ")"
--       else putStrLn $ id ++ " is not well formed with respect to metamodel (" ++ (evalExpectationStr b False) ++ ")" ++ (show errs)

-- expectation id b msg = if b 
--    then putStrLn $ "Expectation: " ++ id ++ " should be well typed"
--    else putStrLn $ "Expectation: " ++ id ++ " should not be well typed (" ++ msg ++ ")"

do_test1 = do
   (nmw, sgw)<-load_sg_def def_path "mm_1.sg"
   putStrLn "Test 1"
   check_report_wf nmw (Just Total) sgw False

do_test2 = do
   (nmw, sgw)<-load_sg_def def_path "mm_2.sg"
   (nm_g1, gwt1)<-load_gwt_def def_path "g_1.gwt"
   (nm_g2, gwt2)<-load_gwt_def def_path "g_2.gwt"
   putStrLn "Test 2"
   check_report_wf nmw (Just Total) sgw True
   check_report_wf nm_g1 (Just Total) gwt1 True
   check_report_wf nm_g2 (Just Total) gwt2 True
   check_ty_morphism (nm_g1 ++ " morphism (Total)") (Just TotalM) gwt1 sgw True
   check_ty_morphism (nm_g2 ++ " morphism (Weak)") (Just WeakM) gwt2 sgw True
   check_ty_morphism (nm_g2 ++ " morphism (Total)") (Just TotalM) gwt2 sgw False
   --putStrLn $ show $ ape sgw "EAssoc"
   --putStrLn $ show $ rPE gwt1 sgw $ ape sgw "EAssoc"

do_test3 = do
   (nmw, sgw)<-load_sg_def def_path "mm_3.sg"
   (nm_g1, gwt1)<-load_gwt_def def_path "g_3.gwt"
   (nm_g2, gwt2)<-load_gwt_def def_path "g_4.gwt"
   (nm_g3, gwt3)<-load_gwt_def def_path "g_5.gwt"
   putStrLn "Test 3"
   check_report_wf nmw (Just Total) sgw True
   check_report_wf nm_g1 (Just Total) gwt1 True
   check_report_wf nm_g2 (Just Total) gwt2 True
   check_report_wf nm_g3 (Just Total) gwt3 True
   check_ty_morphism (nm_g1 ++ " (Total)") (Just TotalM) gwt1 sgw False
   check_ty_morphism (nm_g2 ++ " (Total)") (Just TotalM) gwt2 sgw False
   check_ty_morphism (nm_g3 ++ " (Total)") (Just TotalM) gwt3 sgw False

do_test4 = do
   (nmw, sgw)<-load_sg_def def_path "mm_4.sg"
   (nm_g1, gwt1)<-load_gwt_def def_path "g_6.gwt"
   (nm_g2, gwt2)<-load_gwt_def def_path "g_7.gwt"
   (nm_g3, gwt3)<-load_gwt_def def_path "g_8.gwt"
   (nm_g4, gwt4)<-load_gwt_def def_path "g_9.gwt"
   putStrLn "Test 4"
   check_report_wf nmw (Just Total) sgw True
   check_report_wf nm_g1 (Just Total) gwt1 True
   check_report_wf nm_g2 (Just Total) gwt2 True
   check_report_wf nm_g3 (Just Total) gwt3 True
   check_report_wf nm_g4 (Just Total) gwt4 True
   check_ty_morphism (nm_g1 ++ " (Total)") (Just TotalM) gwt1 sgw True
   check_ty_morphism (nm_g2 ++ " (Total)") (Just TotalM) gwt2 sgw False
   check_ty_morphism (nm_g3 ++ " (Total)") (Just TotalM) gwt3 sgw True
   check_ty_morphism (nm_g4 ++ " (Total)") (Just TotalM) gwt4 sgw False

do_test5 = do
   (nmw, sgw)<-load_sg_def def_path "mm_5.sg"
   (nm_g1, gwt1)<-load_gwt_def def_path "g_10.gwt"
   (nm_g2, gwt2)<-load_gwt_def def_path "g_11.gwt"
   putStrLn "Test 5"
   check_report_wf nmw (Just Total) sgw True
   check_report_wf nm_g1 (Just Total) gwt1 True
   check_report_wf nm_g2 (Just Total) gwt2 True
   check_ty_morphism (nm_g1 ++ " (Total)") (Just TotalM) gwt1 sgw False
   check_ty_morphism (nm_g2 ++ " (Total)") (Just TotalM) gwt2 sgw True

do_main = do
   do_test1
   do_test2
   do_test3
   do_test4
   do_test5

main = do
   option_main_save do_main saveDrawings

-- main = do
--    expectation "metamodel 1" False "inheritance cycle"
--    check_gr_wf "metamodel 1" mm_1
--    expectation "metamodel 2" True ""
--    check_gr_wf "metamodel 2" mm_2
--    check_gr_wf "G1" g1
--    expectation "G1" True ""
--    check_typing "G1" ty_morph_1 g1 mm_2 True
--    check_gr_wf "G2" g2
--    expectation "G2" False "mutiplicity constraint is breached"
--    check_typing "G2" ty_morph_2 g2 mm_2 False
--    expectation "metamodel 3" True ""
--    check_gr_wf "metamodel 3" mm_3
--    check_gr_wf "G3" g3
--    expectation "G3" True ""
--    check_typing "G3" ty_morph_3 g3 mm_3 True
--    check_gr_wf "G4" g4
--    expectation "G4" False "mutiplicity constraint is breached"
--    check_typing "G4" ty_morph_4 g4 mm_3 False
--    check_gr_wf "G5" g5
--    expectation "G5" False "mutiplicity constraint is breached"
--    check_typing "G5" ty_morph_5 g5 mm_3 False
--    expectation "metamodel 4" True ""
--    check_gr_wf "metamodel 4" mm_4
--    check_gr_wf "G6" g6
--    expectation "G6" True ""
--    check_typing "G6" ty_morph_6 g6 mm_4 True
--    check_gr_wf "G7" g7
--    expectation "G7" False "Abstract class constraint is breached"
--    check_typing "G7" ty_morph_7 g7 mm_4 False
--    check_gr_wf "G8" g8
--    expectation "G8" True "" 
--    check_typing "G8" ty_morph_8 g8 mm_4 True
--    check_gr_wf "G9" g9
--    expectation "G9" False "mutiplicity constraint is breached"
--    check_typing "G9" ty_morph_9 g9 mm_4 False
--    expectation "metamodel 5" True ""
--    check_gr_wf "metamodel 5" mm_5
--    check_gr_wf "G10" g10
--    expectation "G10" False "Composition constraint is breached (shared instance)"
--    check_typing "G10" ty_morph_10 g10 mm_5 False
--    check_gr_wf "G11" g11
--    expectation "G11" True ""
--    check_typing "G11" ty_morph_11 g11 mm_5 True