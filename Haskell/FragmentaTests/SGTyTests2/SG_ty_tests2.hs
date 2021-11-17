------------------
-- Project: PCs/Fragmenta
-- Module: 'SG_Ty_tests'
-- Description: Test which focus on the typing of graphs by SGs which are given in the PCs paper
-- Author: Nuno Amálio
-----------------
{-# LANGUAGE UnicodeSyntax #-}

import Gr_Cls
import SGrs
import Grs
import GrswT
import LoadCheckDraw
import CheckUtils
import Utils



def_path = "Tests/SGTyTests2/"
img_path = "Tests/SGTyTests2/img/"

saveDrawings = do
   draw_def def_path img_path "SG_Person_Vehicle_I.sg"
   draw_def def_path img_path "SG_Person_Vehicle_Ib.sg"
   draw_def def_path img_path "SG_PVMI.sg"
   draw_def def_path img_path "SG_HBP.sg"
   draw_def def_path img_path "g1.gwt"
   draw_def def_path img_path "g2.gwt"
   draw_def def_path img_path "g3.gwt"
   draw_def def_path img_path "g4.gwt"
   draw_def def_path img_path "g5.gwt"
   draw_def def_path img_path "g6.gwt"
   draw_def def_path img_path "g7.gwt"

-- evalExpectationStr e r = if e == r then "Ok" else "Fail"

-- check_typing id m g mm b = 
--    let errs = check_typing_g_sg m g mm in
--    if is_wf_ty_g_sg m g mm
--       then putStrLn $ id ++ " is well formed with respect to metamodel (" ++ (evalExpectationStr b True) ++ ")"
--       else putStrLn $ id ++ " is not well formed with respect to metamodel (" ++ (evalExpectationStr b False) ++ ")" ++ (show errs)

-- expectation id b msg = if b 
--    then putStrLn $ "Expectation: " ++ id ++ " should be well typed"
--    else putStrLn $ "Expectation: " ++ id ++ " should not be well typed (" ++ msg ++ ")"

-- Checks that the different graphs are morphisms (only one isn't, g4)
do_test1 = do
   (nmt, sgt)<-load_sg_def def_path "SG_Person_Vehicle_I.sg"
   (nmt2, sgt2)<-load_sg_def def_path "SG_Person_Vehicle_Ib.sg"
   (nmt3, sgt3)<-load_sg_def def_path "SG_PVMI.sg"
   (nmt4, sgt4)<-load_sg_def def_path "SG_HBP.sg"
   (nm_g1, gwt1)<-load_gwt_def def_path "g1.gwt"
   (nm_g2, gwt2)<-load_gwt_def def_path "g2.gwt"
   (nm_g3, gwt3)<-load_gwt_def def_path "g3.gwt"
   (nm_g4, gwt4)<-load_gwt_def def_path "g4.gwt"
   (nm_g5, gwt5)<-load_gwt_def def_path "g5.gwt"
   (nm_g6, gwt6)<-load_gwt_def def_path "g6.gwt"
   (nm_g7, gwt7)<-load_gwt_def def_path "g7.gwt"
   check_report_wf nmt (Just Total) sgt True
   check_report_wf nmt2 (Just Total) sgt2 True
   check_report_wf nmt3 (Just Total) sgt3 True
   check_report_wf nm_g1 (Just Total) gwt1 True
   check_report_wf nm_g2 (Just Total) gwt2 True
   check_report_wf nm_g3 (Just Total) gwt3 True
   check_report_wf nm_g4 (Just Total) gwt4 True
   check_report_wf nm_g5 (Just Total) gwt5 True
   check_report_wf nm_g6 (Just Total) gwt6 True
   check_report_wf nm_g7 (Just Total) gwt7 True
   check_ty_morphism (nm_g1 ++ " typing morphism (Weak)") (Just WeakM) gwt1 sgt True
   check_ty_morphism (nm_g2 ++ " typing morphism (Weak)") (Just WeakM) gwt2 sgt True
   check_ty_morphism (nm_g3 ++ " typing morphism (Weak)") (Just WeakM) gwt3 sgt2 True
   check_ty_morphism (nm_g4 ++ " typing morphism (Weak)") (Just WeakM) gwt4 sgt3 False
   check_ty_morphism (nm_g5 ++ " typing morphism (Weak)") (Just WeakM) gwt5 sgt3 True
   check_ty_morphism (nm_g6 ++ " typing morphism (Weak)") (Just WeakM) gwt6 sgt4 True
   check_ty_morphism (nm_g7 ++ " typing morphism (Weak)") (Just WeakM) gwt7 sgt4 True


-- Checks that the different graphs are well-typed
do_test2 = do
   (nmt, sgt)<-load_sg_def def_path "SG_Person_Vehicle_I.sg"
   (nmt2, sgt2)<-load_sg_def def_path "SG_Person_Vehicle_Ib.sg"
   (nmt3, sgt3)<-load_sg_def def_path "SG_PVMI.sg"
   (nmt4, sgt4)<-load_sg_def def_path "SG_HBP.sg"
   (nm_g1, gwt1)<-load_gwt_def def_path "g1.gwt"
   (nm_g2, gwt2)<-load_gwt_def def_path "g2.gwt"
   (nm_g3, gwt3)<-load_gwt_def def_path "g3.gwt"
   (nm_g5, gwt5)<-load_gwt_def def_path "g5.gwt"
   (nm_g6, gwt6)<-load_gwt_def def_path "g6.gwt"
   (nm_g7, gwt7)<-load_gwt_def def_path "g7.gwt"
   check_report_wf nmt (Just Total) sgt True
   check_report_wf nmt2 (Just Total) sgt2 True
   check_report_wf nmt3 (Just Total) sgt3 True
   check_report_wf nm_g1 (Just Total) gwt1 True
   check_report_wf nm_g2 (Just Total) gwt2 True
   check_report_wf nm_g3 (Just Total) gwt3 True
   check_report_wf nm_g5 (Just Total) gwt5 True
   check_report_wf nm_g6 (Just Total) gwt6 True
   check_report_wf nm_g7 (Just Total) gwt7 True
   check_ty_morphism (nm_g1 ++ " typing morphism (Total)") (Just TotalM) gwt1 sgt True
   check_ty_morphism (nm_g2 ++ " typing morphism (Total)") (Just TotalM) gwt2 sgt False
   check_ty_morphism (nm_g3 ++ " typing morphism (Total)") (Just TotalM) gwt3 sgt2 False
   check_ty_morphism (nm_g5 ++ " typing morphism (Total)") (Just TotalM) gwt5 sgt3 True
   check_ty_morphism (nm_g6 ++ " typing morphism (Total)") (Just TotalM) gwt6 sgt4 False
   check_ty_morphism (nm_g7 ++ " typing morphism (Total)") (Just TotalM) gwt7 sgt4 True


do_main = do
   do_test1

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