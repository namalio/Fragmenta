
import Gr_Cls
import LoadCheckDraw
import CheckUtils
import Utils

def_path = "IntoSysML/MM/"
img_path = "IntoSysML/MM/img/"

saveDrawings = do
   draw_mdl def_path img_path "IntoSysML_AAD_MM"
   draw_mdl def_path img_path "IntoSysML_ASD_MM"
   draw_mdl def_path img_path "IntoSysML_CD_MM"

check_AMM = do
    amdl<-load_mdl_def def_path "IntoSysML_AAD_MM"
    check_report_wf "IntoSysML_AAD_MM" (Just Total) amdl True

check_ASD_MM = do
    cmdl<-load_mdl_def def_path "IntoSysML_ASD_MM"
    check_report_wf "IntoSysML_ASD_MM" (Just Total) cmdl True

check_CD_MM = do
    cmdl<-load_mdl_def def_path "IntoSysML_CD_MM"
    check_report_wf "IntoSysML_CD_MM" (Just Total) cmdl True

check_fragments = do
    (nm_af, af)<-load_fr_def def_path "F_AAD.fr"
    (nm_fb1, fb1)<-load_fr_def def_path "F_B1.fr"
    (nm_ft, ft)<-load_fr_def def_path "F_TYS.fr"
    (nm_f1, f1)<-load_fr_def def_path "F_ASD1.fr"
    (nm_f1, f1)<-load_fr_def def_path "F_ASD1.fr"
    (nm_f2, f2)<-load_fr_def def_path "F_ASD2.fr"
    (nm_f3, f3)<-load_fr_def def_path "F_ASD3.fr"
    (nm_f4, f4)<-load_fr_def def_path "F_ASD4.fr"
    (nm_f5, f5)<-load_fr_def def_path "F_ASD5.fr"
    (nm_f6, f6)<-load_fr_def def_path "F_ASD6.fr"
    (nm_f7, f7)<-load_fr_def def_path "F_ASD7.fr"
    (nm_fcd1, fcd1)<-load_fr_def def_path "F_CD1.fr"
    check_report_wf nm_af (Just Total) af True
    check_report_wf nm_fb1 (Just Partial) fb1 True
    check_report_wf nm_ft (Just Partial) ft True
    check_report_wf nm_f1 (Just Partial) f1 True
    check_report_wf nm_f2 (Just Partial) f2 True
    check_report_wf nm_f3 (Just Partial) f3 True
    check_report_wf nm_f4 (Just Partial) f4 True
    check_report_wf nm_f5 (Just Partial) f5 True
    check_report_wf nm_f6 (Just Partial) f6 True
    check_report_wf nm_f7 (Just Partial) f7 True
    check_report_wf nm_fcd1 (Just Partial) fcd1 True

check_morphisms = do
    (nm_af, af)<-load_fr_def def_path "F_AAD.fr"
    (nm_fb1, fb1)<-load_fr_def def_path "F_B1.fr"
    (nm_ft, ft)<-load_fr_def def_path "F_TYS.fr"
    (nm_f1, f1)<-load_fr_def def_path "F_ASD1.fr"
    (nm_f1, f1)<-load_fr_def def_path "F_ASD1.fr"
    (nm_f2, f2)<-load_fr_def def_path "F_ASD2.fr"
    (nm_f3, f3)<-load_fr_def def_path "F_ASD3.fr"
    (nm_f4, f4)<-load_fr_def def_path "F_ASD4.fr"
    (nm_f5, f5)<-load_fr_def def_path "F_ASD5.fr"
    (nm_f6, f6)<-load_fr_def def_path "F_ASD6.fr"
    (nm_f7, f7)<-load_fr_def def_path "F_ASD7.fr"
    (nm_fcd1, fcd1)<-load_fr_def def_path "F_CD1.fr"
    --(nm_f8, f8)<-load_fr_def def_path "F_ASD8.fr"
    --check_report_wf nm_af (Just Total) af True
    --check_report_wf nm_f1 (Just Partial) f1 True
    --check_report_wf nm_f2 (Just Partial) f2 True
    --check_report_wf nm_f3 (Just Partial) f3 True
    (nm_mb1, mb1)<-load_morphism_def def_path "F_B1.gm"
    (nm_mt, mt)<-load_morphism_def def_path "F_TYS.gm"
    (nm_m1, m1)<-load_morphism_def def_path "F_ASD1.gm"
    (nm_m2, m2)<-load_morphism_def def_path "F_ASD2.gm"
    (nm_m3, m3)<-load_morphism_def def_path "F_ASD3.gm"
    (nm_m4, m4)<-load_morphism_def def_path "F_ASD4.gm"
    (nm_m5, m5)<-load_morphism_def def_path "F_ASD5.gm"
    (nm_m6, m6)<-load_morphism_def def_path "F_ASD6.gm"
    (nm_m7, m7)<-load_morphism_def def_path "F_ASD7.gm"
    (nm_mcd1, mcd1)<-load_morphism_def def_path "F_CD1.gm"
    --(nm_m8, m8)<-load_morphism_def def_path "F_ASD8.gm"
    check_morphism ("Morphism '" ++ nm_mb1 ++ "' (Partial)") (Just PartialM) fb1 mb1 af True
    check_morphism ("Morphism '" ++ nm_mt ++ "' (Partial)") (Just PartialM) ft mt af True
    check_morphism ("Morphism '" ++ nm_m1 ++ "' (Partial)") (Just PartialM) f1 m1 af True
    check_morphism ("Morphism '" ++ nm_m2 ++ "' (Partial)") (Just PartialM) f2 m2 af True
    check_morphism ("Morphism '" ++ nm_m3 ++ "' (Partial)") (Just PartialM) f3 m3 af True
    check_morphism ("Morphism '" ++ nm_m4 ++ "' (Partial)") (Just PartialM) f4 m4 af True
    check_morphism ("Morphism '" ++ nm_m5 ++ "' (Partial)") (Just PartialM) f5 m5 af True
    check_morphism ("Morphism '" ++ nm_m6 ++ "' (Partial)") (Just PartialM) f6 m6 af True
    check_morphism ("Morphism '" ++ nm_m7 ++ "' (Partial)") (Just PartialM) f7 m7 af True
    check_morphism ("Morphism '" ++ nm_mcd1 ++ "' (Partial)") (Just PartialM) fcd1 mcd1 af True
    --check_morphism ("Morphism '" ++ nm_m8 ++ "' (Partial)") (Just PartialM) f8 m8 af True
    

do_main = do
    amdl<-load_mdl_def def_path "IntoSysML_AAD_MM"
    cmdl<-load_mdl_def def_path "IntoSysML_ASD_MM"
    --cmdl2<-load_mdl_def def_path "IntoSysML_ASD_CD_MM"
    cmdl2<-load_mdl_def def_path "IntoSysML_CD_MM"
    rms<-load_rm_cmdl_def def_path "IntoSysML_ASD_MM"
    --rms2<-load_rm_cmdl_def def_path "IntoSysML_ASD_CD_MM"
    rms2<-load_rm_cmdl_def def_path "IntoSysML_CD_MM"
    check_report_wf "IntoSysML_AAD_MM" (Just Total) amdl True
    check_report_wf "IntoSysML_ASD_MM" (Just Total) cmdl True
    --check_report_wf "IntoSysML_ASD_CD_MM" (Just Total) cmdl True
    check_report_wf "IntoSysML_CD_MM" (Just Total) cmdl2 True
    check_morphism "Refinement of 'IntoSysML_ASD_MM' by 'IntoSysML_AAD_MM'" (Just TotalM) cmdl rms amdl True
    --check_morphism "Refinement of 'IntoSysML_ASD_CD_MM' by 'IntoSysML_AAD_MM'" (Just TotalM) cmdl2 rms2 amdl True
    check_morphism "Refinement of 'IntoSysML_CD_MM' by 'IntoSysML_AAD_MM'" (Just PartialM) cmdl2 rms2 amdl True

main = do
    option_main_save do_main saveDrawings
