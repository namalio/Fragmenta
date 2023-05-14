-------------------------
-- Project: PCs/Fragmenta
-- Module: 'Test_Feline_Canidae'
-- Description: Test which focus on the example of PCs paper in the Fragmenta/Fragments section 
--      with nodes Mammal, Feline and Canidae
-- Author: Nuno Amálio
--------------------------
import Gr_Cls
import Frs
import Utils ( option_main_save )
import CheckUtils
import LoadCheckDraw
import Mdls

def_path :: String
def_path = "FragmentaTests/MammalFelineCanidae/"
img_path :: String
img_path = "FragmentaTests/MammalFelineCanidae/img/"

saveDrawings :: IO ()
saveDrawings= do
    draw_mdl def_path img_path "m_feline_canidae"
    --(nm_f1, f1)<-load_fr_def def_path "F_M.fr"
    --(nm_f2, f2)<-load_fr_def def_path "F_FC.fr"
    --saveFrDrawing img_path nm_f1 f1 
    --saveFrDrawing img_path nm_f2 f2 
    --let ufs = f1 `union_f` f2
    --saveFrDrawing img_path "UFs_MammalFelineCanidae" ufs 
    --let rf = reso_f ufs
    --saveFrDrawing img_path "Rf_UFs_MammalFelineCanidae" rf
    --draw_def def_path img_path "feline-canidae.gfg"


-- Figures 9d and 9e 
do_tst_fr :: IO ()
do_tst_fr = do
    (nm_f1, f1)<-load_fr_def def_path "F_M.fr"
    (nm_f2, f2)<-load_fr_def def_path "F_FC.fr"
    check_report_wf nm_f1 (Just Partial) f1 True
    check_report_wf nm_f2 (Just Partial) f2 True
    let ufs = f1 `union_f` f2
    let rf = reso_f ufs
    check_report_wf "UFs_MammalFelineCanidae" (Just Total) ufs True
    check_report_wf "Rf_UFs_MammalFelineCanidae" (Just Total) rf True

do_tst_mdl :: IO ()
do_tst_mdl = do
    mdl<-load_mdl_def def_path "m_feline_canidae"
    --(nm_f1, f1)<-load_fr_def def_path "F_M.fr"
    --(nm_f2, f2)<-load_fr_def def_path "F_FC.fr"
    --(nm_gfg, gfg)<-load_gfg_def def_path "m_feline-canidae.gfg"
    --let mdl = cons_mdl gfg [(nm_f1, f1), (nm_f2, f2)]
    check_report_wf "M_MFC" (Just Total) mdl True

do_main :: IO ()
do_main = do
    do_tst_fr

main :: IO ()
main = do
    option_main_save do_main saveDrawings

