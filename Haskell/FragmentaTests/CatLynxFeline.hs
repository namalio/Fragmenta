------------------------------------------
-- Project: PCs/Fragmenta
-- Module: 'Fr_tests'
-- Description: Test focused on inheritance cycle example with fragments revolving 
--              around Cat, Feline and Lynx (from Fragmenta paper)
-- Author: Nuno Amálio
------------------------------------------
import Gr_Cls
import Frs
import Utils
import CheckUtils
import LoadCheckDraw
import Mdls

def_path = "FragmentaTests/CatLynxFeline/"
img_path = "FragmentaTests/CatLynxFeline/img/"

saveDrawings= do
    draw_mdl def_path img_path "m_felines"
    --(nm_f1, f1)<-load_fr_def def_path "cat_lynx_feline.fr"
    --(nm_f2, f2)<-load_fr_def def_path "feline_lynx.fr"
    --saveFrDrawing img_path nm_f1 f1 
    --saveFrDrawing img_path nm_f2 f2 
    --let ufs = f1 `union_f` f2
    --saveFrDrawing img_path "UFs_CatLynxFeline" ufs 
    --let rf = reso_f ufs
    --saveFrDrawing img_path "Rf_UFs_CatLynxFeline" rf 
    --draw_def def_path img_path "gfg_felines.gfg"

do_test_frs = do
    (nm_f1, f1)<-load_fr_def def_path "F_CLF.fr"
    (nm_f2, f2)<-load_fr_def def_path "F_FL.fr"
    check_report_wf nm_f1 (Just Partial) f1 True
    check_report_wf nm_f2 (Just Partial) f2 True
    let ufs = f1 `union_f` f2
    let rf = reso_f ufs
    check_report_wf "UFs_CatLynxFeline" (Just Total) ufs False
    check_report_wf "Rf_UFs_CatLynxFeline" (Just Total) rf False

do_test_mdl = do
    mdl<-load_mdl_def def_path "m_felines"
    check_report_wf "M_CLF" (Just Total) mdl False


do_main = do
    putStrLn "Inheritance cycle example with fragments revolving around Lynx, Cat, Feline"
    do_test_mdl

main = do
   option_main_save do_main saveDrawings



