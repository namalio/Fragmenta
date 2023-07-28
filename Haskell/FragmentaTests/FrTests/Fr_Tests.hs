-------------------------
-- Project: PCs/Fragmenta
-- Module: 'Fr_tests'
-- Description: Testing of fragments and simple morphisms (some examples come from MODELS 2015 paper)
-- Author: Nuno Amálio
-------------------------

import Gr_Cls
import Grs
import Frs
import SGrs ( g_sg, pe) 
import Utils ( option_main_save )
import Relations
import CheckUtils
import LoadCheckDraw
import Frs ( unionF )
import PathExpressions -- remove at some point

-- Based on the Example given on the Models 2015 paper
def_path = "FragmentaTests/FrTests/"
img_path = "FragmentaTests/FrTests/img/"

saveDrawings :: IO ()
saveDrawings = do
   draw_def def_path img_path "F_ECC.fr"
   draw_def def_path img_path "F_PVI.fr"
   draw_def def_path img_path "f_APerson1.fr"
   draw_def def_path img_path "f_Person1.fr"
   draw_def def_path img_path "f_AC1.fr"
   draw_def def_path img_path "f_AC2.fr"
   draw_def def_path img_path "f_AC3.fr"
   draw_def def_path img_path "f_CC.fr"

test1 :: IO ()
test1 = do
   putStrLn "Test 1: Example of Models 2015 paper"
   (nm_f1, f1)<-loadF def_path "F_ECC.fr"
   (nm_f2, f2)<-loadF def_path "F_PVI.fr"
   (nm_m1, m1)<-loadM def_path "m_ECC_PVI.gm"
   (nm_m2, m2)<-loadM def_path "m_PVI_ECC.gm"
   check_report_wf ("Fragment " ++ nm_f1) (Just Total) f1 True
   check_report_wf ("Fragment " ++ nm_f2) (Just Total) f2 True
   check_morphism ("(" ++ nm_f1 ++ ", " ++ nm_m1++ ") ⊒ " ++ nm_f2) (Just PartialM) f1 m1 f2 True
   check_morphism ("(" ++ nm_f1 ++ ", " ++ nm_m1++ ") ⊐ " ++ nm_f2) (Just TotalM) f1 m1 f2 False
   check_morphism ("(" ++ nm_f2 ++ ", " ++ nm_m2++ ") ⊐ " ++ nm_f1) (Just TotalM) f2 m2 f1 True

test2 :: IO ()
test2 = do
   putStrLn "Test 2: Example involving the virtual traits pattern"
   (nm_af, af)<-loadF def_path "f_APerson1.fr"
   (nm_f, f)<-loadF def_path "f_Person1.fr"
   (nm_m1, m1)<-loadM def_path "m_P_AP.gm"
   check_report_wf ("Fragment " ++ nm_af) (Just Total) af True
   check_report_wf ("Fragment " ++ nm_f) (Just Total) f True
   check_morphism ("(" ++ nm_f ++ ", " ++ nm_m1 ++ ") ⊐ " ++ nm_af)  (Just TotalM) f m1 af True

test3 :: IO ()
test3 = do
   putStrLn "Test 3: Composites example with derived edges in the abstract model"
   (nm_af1, af1)<-loadF def_path "f_AC1.fr"
   (nm_af2, af2)<-loadF def_path "f_AC2.fr"
   (nm_af3, af3)<-loadF def_path "f_AC3.fr"
   (nm_fcc, fcc)<-loadF def_path "f_CC.fr"
   (nm_m1, m1)<-loadM def_path "m_FCC_FAC.gm"
   (nm_m2, m2)<-loadM def_path "m_E_FCC_FAC.gm"
   check_report_wf ("Fragment " ++ nm_af1 ++ " (Partial)") (Just Partial) af1 True
   check_report_wf ("Fragment " ++ nm_af2 ++ " (Partial)") (Just Partial) af2 True
   check_report_wf ("Fragment " ++ nm_af3 ++ " (Partial)") (Just Partial) af3 True
   let af = af1 `unionF` (af2 `unionF` af3)
   let nm_af = nm_af1 ++ "∪" ++ nm_af2 ++ "∪" ++ nm_af3
   check_report_wf ("Fragment AC (" ++ nm_af++", total)") (Just Total) af True
   check_report_wf ("Fragment " ++ nm_fcc ++ " (Partial)") (Just Partial) fcc True
   check_morphism ("(" ++ nm_fcc ++ ", " ++ nm_m1++ ") ⊒ " ++ nm_af2) (Just PartialM) fcc m1 af2 True
   -- The morphism leads to a breach of an abstract fragment constraint
   check_morphism ("(" ++ nm_fcc ++ ", " ++ nm_m2++ ") ⊒ " ++ nm_af2) (Just PartialM) fcc m2 af2 False
   let asg = fsg . reso_f $ af2
   --putStrLn $ "Constraint edges: " ++ show (esCnt asg)
   --putStrLn $ "Source node of 'ECPs1': " ++ show (appl (src asg) "ECPs1")
   --putStrLn $ "Target node of 'ECPs1': " ++ show (appl (tgt asg) "ECPs1")
   let cf = af1 `unionF` (fcc `unionF` af3)
   let m2 = m1 `unionGM` ((gid (g_sg . fsg $ af1)) `unionGM` (gid (g_sg . fsg $ af3)))
   let nm_cf = nm_af1 ++ "∪" ++ nm_fcc ++ "∪" ++ nm_af3
   check_report_wf ("Fragment CC (" ++ nm_cf ++", total)") (Just Total) cf True
   check_morphism ("(" ++ nm_cf ++ ", " ++ nm_m1++ ") ⊐ " ++ nm_af) (Just TotalM) cf m2 af True

do_main :: IO ()
do_main = do
   test1
   test2
   test3

main :: IO ()
main = do
   option_main_save do_main saveDrawings

