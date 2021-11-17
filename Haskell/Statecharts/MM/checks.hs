
import Gr_Cls
import LoadCheckDraw
import CheckUtils
import Utils

def_path = "Statecharts/MM/"
img_path = "Statecharts/MM/img/"

saveDrawings = do
   draw_mdl def_path img_path "StCs_AMM"
   draw_mdl def_path img_path "StCs_MM"

check_AMM = do
    amdl<-load_mdl_def def_path "StCs_AMM"
    check_report_wf "StCs_AMM" (Just Total) amdl True

check_CMM = do
    cmdl<-load_mdl_def def_path "Stcs_MM"
    check_report_wf "Stcs_MM" (Just Total) cmdl True

check_morphisms = do
    (nm_af, af)<-load_fr_def def_path "F_AMM.fr"
    (nm_f1, f1)<-load_fr_def def_path "F_MM1.fr"
    (nm_f2, f2)<-load_fr_def def_path "F_MM2.fr"
    (nm_f3, f3)<-load_fr_def def_path "F_MM3.fr"
    check_report_wf nm_af (Just Total) af True
    check_report_wf nm_f1 (Just Partial) f1 True
    check_report_wf nm_f2 (Just Partial) f2 True
    check_report_wf nm_f3 (Just Partial) f3 True
    (nm_m1, m1)<-load_morphism_def def_path "F_MM1.gm"
    (nm_m2, m2)<-load_morphism_def def_path "F_MM2.gm"
    (nm_m3, m3)<-load_morphism_def def_path "F_MM3.gm"
    --putStrLn $ show m2
    check_morphism (nm_m1 ++ " (Partial)") (Just PartialM) f1 m1 af True
    check_morphism (nm_m2 ++ " (Partial)") (Just PartialM) f2 m2 af True
    check_morphism (nm_m3 ++ " (Partial)") (Just PartialM) f3 m3 af True

do_main = do
    amdl<-load_mdl_def def_path "StCs_AMM"
    cmdl<-load_mdl_def def_path "Stcs_MM"
    rms<-load_rm_cmdl_def def_path "Stcs_MM"
    check_report_wf "StCs_AMM" (Just Total) amdl True
    check_report_wf "StCs_MM" (Just Total) cmdl True
    check_morphism "Refinement of 'StCs_MM' by 'StCs_AMM'" (Just TotalM) cmdl rms amdl True

main = do
    option_main_save do_main saveDrawings
