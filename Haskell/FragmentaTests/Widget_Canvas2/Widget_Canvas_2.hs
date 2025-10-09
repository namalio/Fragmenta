-------------------------
-- Project: PCs/Fragmenta
-- Module: 'WC' (Widget-Canvas)
-- Description: Example of Fragmenta paper ('Related Work' section) based on widgets
-- Author: Nuno Amálio
--------------------------
import Gr_Cls
import Grs
import Frs
import Mdls
import Utils
import CheckUtils
import LoadCheckDraw
import NumString

def_path = "FragmentaTests/Widget_Canvas2/"
img_path = "FragmentaTests/Widget_Canvas2/img/"

saveDrawings= do
    draw_mdl def_path img_path "m_WC2"

do_test_frs = do
    (nm_f1, f1)<-loadF def_path "F_WC1.fr"
    (nm_f2, f2)<-loadF def_path "F_WC2.fr"
    (nm_f3, f3)<-loadF def_path "F_WC3.fr"
    check_report_wf nm_f1 (Just Partial) f1 True
    check_report_wf nm_f2 (Just Partial) f2 True
    check_report_wf nm_f3 (Just Partial) f3 True

do_main = do
    (nm_mdl, mdl)<-loadMdl def_path "m_WC2"
    check_report_wf nm_mdl (Just Total) mdl False

main = do
   option_main_save do_main saveDrawings
