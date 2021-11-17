------------------
-- Project: PCs/Fragmenta
-- Module: 'Fr_tests'
-- Description: Test which focus on the fragments and simple morphisms based on the examples given in the MODELS 2015 paper
-- Author: Nuno Amálio
-----------------

import Gr_Cls
import Frs
import Utils
import CheckUtils
import LoadCheckDraw

-- Based on the Example given on the Models 2015 paper
def_path = "Tests/FrTests/"
img_path = "Tests/FrTests/img/"

saveDrawings = do
   draw_def def_path img_path "F_ECC.fr"
   draw_def def_path img_path "F_PVI.fr"

do_main = do
   (nm_f1, f1)<-load_fr_def def_path "F_ECC.fr"
   (nm_f2, f2)<-load_fr_def def_path "F_PVI.fr"
   (nm_m1, m1)<-load_morphism_def def_path "m_ECC_PVI.gm"
   (nm_m2, m2)<-load_morphism_def def_path "m_PVI_ECC.gm"
   check_report_wf nm_f1 (Just Total) f1 True
   check_report_wf nm_f2 (Just Total) f2 True
   check_morphism (nm_m1++ " morphism (Weak)") (Just WeakM) f1 m1 f2 True
   check_morphism (nm_m1++ " refinement morphism (Partial)") (Just PartialM) f1 m1 f2 True
   check_morphism (nm_m2++ " morphism (Weak)") (Just WeakM) f2 m2 f1 True
   check_morphism (nm_m1++ " refinement morphism (Total)") (Just TotalM) f2 m2 f1 True

main = do
   option_main_save do_main saveDrawings

