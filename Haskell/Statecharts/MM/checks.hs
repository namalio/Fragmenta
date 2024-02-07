
import Gr_Cls
import LoadCheckDraw
import CheckUtils
import Utils
import NumString

def_path :: String
def_path = "Statecharts/MM/"
img_path :: String
img_path = "Statecharts/MM/img/"

saveDrawings :: IO ()
saveDrawings = do
   draw_mdl def_path img_path "StCs_AMM"
   draw_mdl def_path img_path "StCs_MM"

check_AMM :: IO ()
check_AMM = do
    (nm_amdl,amdl) <-loadMdl def_path "StCs_AMM"
    check_report_wf nm_amdl (Just Total) amdl True

check_CMM :: IO ()
check_CMM = do
    (nm_cmdl, cmdl)<-loadMdl def_path "Stcs_MM"
    check_report_wf nm_cmdl (Just Total) cmdl True

check_morphisms :: IO ()
check_morphisms = do
    (nm_af, af)<-loadF def_path "F_AH.fr"
    (nm_f1, f1)<-loadF def_path "F_MM1.fr"
    (nm_f2, f2)<-loadF def_path "F_MM2.fr"
    (nm_f3, f3)<-loadF def_path "F_MM3.fr"
    (nm_f4, f4)<-loadF def_path "F_MM4.fr"
    (nm_f5, f5)<-loadF def_path "F_MM5.fr"
    check_report_wf nm_af (Just Total) af True
    check_report_wf nm_f1 (Just Partial) f1 True
    check_report_wf nm_f2 (Just Partial) f2 True
    check_report_wf nm_f3 (Just Partial) f3 True
    check_report_wf nm_f4 (Just Partial) f4 True
    (nm_m1, m1)<-loadM def_path "F_MM1.gm"
    (nm_m2, m2)<-loadM def_path "F_MM2.gm"
    (nm_m3, m3)<-loadM def_path "F_MM3.gm"
    (nm_m4, m4)<-loadM def_path "F_MM4.gm"
    (nm_m5, m5)<-loadM def_path "F_MM5.gm"
    --putStrLn $ show m2
    check_morphism (nm_m1 ++ " (Partial)") (Just PartialM) f1 m1 af True
    check_morphism (nm_m2 ++ " (Partial)") (Just PartialM) f2 m2 af True
    check_morphism (nm_m3 ++ " (Partial)") (Just PartialM) f3 m3 af True
    check_morphism (nm_m4 ++ " (Partial)") (Just PartialM) f4 m4 af True
    check_morphism (nm_m5 ++ " (Partial)") (Just PartialM) f5 m5 af True

do_main :: IO ()
do_main = do
    (nm_amdl, amdl)<-loadMdl def_path "StCs_AMM"
    (nm_cmdl, cmdl)<-loadMdl def_path "Stcs_MM"
    rms<-load_rm_cmdl_def def_path "Stcs_MM"
    check_report_wf nm_amdl (Just Total) amdl True
    check_report_wf nm_cmdl (Just Total) cmdl True
    check_morphism "Refinement of 'StCs_MM' by 'StCs_AMM'" (Just TotalM) cmdl rms amdl True

main :: IO ()
main = do
    option_main_save do_main saveDrawings
