------------------
-- Project: PCs/Fragmenta
-- Module: 'Fr_tests'
-- Description: Test which focus on fragments and refinement 
-- Author: Nuno Amálio
-----------------
import Gr_Cls
import SGrs
import Grs
import Frs
import CheckUtils
import Utils
import LoadCheckDraw

def_path = "Tests/FrTests2/"
img_path = "Tests/FrTests2/img/"

saveDrawings= do
    (nm_af, af)<-load_fr_def def_path "amm_1.fr"
    (nm_f1, f1)<-load_fr_def def_path "mm_1.fr"
    (nm_f2, f2)<-load_fr_def def_path "mm_2.fr"
    saveFrDrawing img_path nm_af af
    saveFrDrawing img_path nm_f1 f1 
    saveFrDrawing img_path nm_f2 f2 
    let ufs = f1 `union_f` f2
    saveFrDrawing img_path "UFs_MMs_1_2" ufs 
    let rf = reso_f ufs
    saveFrDrawing img_path "Rf_UFs_MMs_1_2" rf 

do_main = do
    (nm_af, af)<-load_fr_def def_path "amm_1.fr"
    (nm_f1, f1)<-load_fr_def def_path "mm_1.fr"
    (nm_f2, f2)<-load_fr_def def_path "mm_2.fr"
    (nm_m1, m1)<-load_morphism_def def_path "m_mm_1.gm"
    (nm_m2, m2)<-load_morphism_def def_path "m_mm_2.gm"
    check_report_wf nm_af (Just Total) af True
    check_report_wf nm_f1 (Just Partial) f1 True
    check_report_wf nm_f2 (Just Partial) f2 True
    check_morphism (nm_m1++ " morphism (Weak)") (Just WeakM) f1 m1 af True
    check_morphism (nm_m1++ " morphism (Partial)") (Just PartialM) f1 m1 af True
    check_morphism (nm_m2++ " morphism (Weak)") (Just WeakM) f2 m2 af True
    check_morphism (nm_m2++ " morphism (Partial)") (Just PartialM) f2 m2 af True
    let ufs = f1 `union_f` f2
    check_report_wf (nm_f1 ++ " UF " ++ nm_f2) (Just Partial) ufs True
    check_morphism (nm_m1++ " U " ++ nm_m2 ++ " morphism (Total)") (Just TotalM) ufs (m1 `union_gm` m2) af True
    let rf = reso_f ufs
    check_report_wf ("◉ " ++ nm_f1 ++ " UF " ++ nm_f2) (Just Partial) rf True
    let mr = mres (m1 `union_gm` m2) (ufs, af)
    check_morphism ("◉ " ++ nm_m1++ " U " ++ nm_m2 ++ " morphism (Total)") (Just TotalM) rf mr af True

main = do
   option_main_save do_main saveDrawings



 