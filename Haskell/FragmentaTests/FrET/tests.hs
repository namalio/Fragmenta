-------------------------
-- Project: PCs/Fragmenta
-- Module: 'Fr_tests'
-- Description: Testing of fragments and simple morphisms (some examples come from MODELS 2015 paper)
-- Author: Nuno Amálio
-------------------------

import Gr_Cls
import Grs
import SGrs -- remove later
import ErrorAnalysis -- remove later
import Frs
import Utils ( option_main_save )
import Relations
import CheckUtils
import LoadCheckDraw
import Frs ( unionF )
import GrswET -- remove at some point
-- Based on the Example given on the Models 2015 paper
def_path = "FragmentaTests/FrET/"
img_path = "FragmentaTests/FrET/img/"

cons_acpf:: IO (String, Fr String String)
cons_acpf = do
   (nm_f1, f1)<-loadF def_path "F_ACP1.fr"
   (nm_f2, f2)<-loadF def_path "F_ACP2.fr"
   (nm_f3, f3)<-loadF def_path "F_ACP3.fr"
   let acpf = f1 `unionF` (f2 `unionF` f3) 
   let nm_acpf = nm_f1 ++ " U " ++ nm_f2 ++ " U " ++ nm_f3
   return (nm_acpf, acpf)

cons_scpf:: IO (String, Fr String String)
cons_scpf = do
   (nm_f1, f1)<-loadF def_path "F_SCP1.fr"
   (nm_f2, f2)<-loadF def_path "F_SCP2.fr"
   let scpf = f1 `unionF` f2
   let nm_scpf = nm_f1 ++ " U " ++ nm_f2
   return (nm_scpf, scpf)

saveDrawings :: IO ()
saveDrawings = do
   draw_def def_path img_path "F_ACP1.fr"
   draw_def def_path img_path "F_ACP2.fr"
   draw_def def_path img_path "f_ACP3.fr"
   draw_def def_path img_path "f_SCP1.fr"
   draw_def def_path img_path "f_SCP2.fr"
   draw_def def_path img_path "I_ACP1.gwt"
   draw_def def_path img_path "I_SCP1.gwet"
   (nm_acpf, acpf)<-cons_acpf
   saveFrDrawing img_path "F_ACPU" acpf
   (nm_scpf, scpf)<-cons_scpf
   saveFrDrawing img_path "F_SCPU" scpf

test1 :: IO ()
test1 = do
   putStrLn "Test 1: Well-formedness of fragments"
   (nm_f1, f1)<-loadF def_path "F_ACP1.fr"
   (nm_f2, f2)<-loadF def_path "F_ACP2.fr"
   (nm_f3, f3)<-loadF def_path "F_ACP3.fr"
   (nm_f4, f4)<-loadF def_path "f_SCP1.fr"
   (nm_f5, f5)<-loadF def_path "f_SCP2.fr"
   check_report_wf ("Fragment " ++ nm_f1) (Just Partial) f1 True
   check_report_wf ("Fragment " ++ nm_f2) (Just Partial) f2 True
   check_report_wf ("Fragment " ++ nm_f3) (Just Partial) f3 True
   check_report_wf ("Fragment " ++ nm_f4) (Just Partial) f4 True
   check_report_wf ("Fragment " ++ nm_f5) (Just Partial) f5 True
   (nm_acpf, acpf)<-cons_acpf
   check_report_wf ("Fragment " ++ nm_acpf) (Just Total) acpf True
   (nm_scpf, scpf)<-cons_scpf
   check_report_wf ("Fragment " ++ nm_scpf) (Just Total) scpf True

--checkOkayETFs::(Eq a, Eq b)=>(String, Fr a b)->(String,Fr a b)->Bool->IO() 
--checkOkayETFs (nm_fs, fs) (nm_ft, ft) b1 = do
--   let b2 = wfETFs fs ft 
--   if b2
--      then putStrLn $ " Fragment " ++ nm_fs ++" is ET compatible with " ++ nm_ft ++ " " ++ (evalExpectation b1 b2)
--      else putStrLn $ " Fragment " ++ nm_fs ++" is not ET compatible with " ++ nm_ft ++ " " ++ (evalExpectation b1 b2)
--   where evalExpectation b1 b2 = if b1 == b2 then "(Ok)" else "(Fail)"

test2 :: IO ()
test2 = do
   putStrLn "Test 2: Well-formedness of the extra typing"
   (nm_f2, f2)<-loadF def_path "F_ACP2.fr"
   (nm_f4, f4)<-loadF def_path "F_SCP1.fr"
   (nm_f5, f5)<-loadF def_path "f_SCP2.fr"
   checkOkayETFs (nm_f5, f5) (nm_f2, f2) True
   --putStrLn $ show (fet f5)
   (nm_scpf, scpf)<-cons_scpf
   checkOkayETFs (nm_scpf, scpf) (nm_f2, f2) True
   (nm_acpf, acpf)<-cons_acpf
   checkOkayETFs (nm_scpf, scpf) (nm_acpf, acpf) True
   checkOkayETFs (nm_f4, f4) (nm_f2, f2) False

test3 :: IO ()
test3 = do
   putStrLn "Test 3: Instances"
   (nm_gwt1, gwt1) <- loadGwT def_path "I_ACP1.gwt"
   (nm_gwt2, gwt2) <- loadGwET def_path "I_SCP1.gwet"
   (nm_acpf, acpf)<-cons_acpf
   (nm_scpf, scpf)<-cons_scpf
   check_report_wf ("GwT " ++ nm_gwt1) Nothing gwt1 True
   check_report_wf ("GwET " ++ nm_gwt2) Nothing gwt2 True
   check_ty_morphism (nm_gwt1 ++ " ⋑ " ++ nm_acpf) (Just TotalM) gwt1 acpf True
   check_ty_morphism (nm_gwt2 ++ " ⋑ " ++ nm_scpf) (Just TotalM) gwt2 scpf True
   checkETCompliance ("Extra typing compliance of GwET " ++ nm_gwt2) gwt2 scpf acpf gwt1 True
   --putStrLn $ show (get gwt2)
   --putStrLn $ show (ns gwt1)

do_main :: IO ()
do_main = do
   test1
   test2
   test3

main :: IO ()
main = do
   option_main_save do_main saveDrawings

