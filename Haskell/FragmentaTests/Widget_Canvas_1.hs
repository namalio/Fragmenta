-------------------------
-- Project: PCs/Fragmenta
-- Module: 'WC' (Widget-Canvas)
-- Description: Example of Fragmenta paper ('Related Work' section), with a an example based on widgets
-- Author: Nuno Amálio
--------------------------
import Gr_Cls
import Grs
import Frs
import Mdls
import Utils
import CheckUtils
import LoadCheckDraw

def_path = "FragmentaTests/Widget_Canvas/"
img_path = "FragmentaTests/Widget_Canvas/img/"

saveDrawings= do
    draw_mdl def_path img_path "m_WC"

do_test_frs = do
    (nm_f1, f1)<-load_fr_def def_path "F_WC1.fr"
    (nm_f2, f2)<-load_fr_def def_path "F_WC2.fr"
    check_report_wf nm_f1 (Just Partial) f1 True
    check_report_wf nm_f2 (Just Partial) f2 False

do_main = do
    mdl<-load_mdl_def def_path "m_WC"
    check_report_wf "M_WC" (Just Total) mdl False

main = do
   option_main_save do_main saveDrawings
