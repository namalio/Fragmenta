
---------------------------
-- Project: Fragmenta
-- Module: 'PetsWorld'
-- Description: Module dedicated to the pets world example of the Fragmenta paper.
-- Author: Nuno Amálio
--------------------------
module FragmentaTests.PetsWorld.PetsWorldTest where

import Gr_Cls
import SGrs
import Frs
import Grs
import LoadCheckDraw
import CheckUtils
    ( check_morphism, check_report_wf, check_ty_morphism )
import Mdls
import Utils ( option_main_save )
import NumString

def_path :: String
def_path = "PetsWorld/"
img_path :: String
img_path = "PetsWorld/img/"

saveDrawings :: IO ()
saveDrawings = do
   draw_mdl def_path img_path "M_AHW"
   draw_mdl def_path img_path "M_PW"
   draw_def def_path img_path "PWI1.gwt"
   draw_def def_path img_path "PWI2.gwt"

load_mdl :: IO ((String, Mdl String String), (String, Mdl String String), GrM String String)
load_mdl = do
   amdlp<-loadMdl def_path "M_AHW"
   cmdlp<-loadMdl def_path "M_PW"
   rms<-load_rm_cmdl_def def_path "M_PW"
   return (amdlp, cmdlp, rms)

do_main :: IO ()
do_main = do 
   ((amdl_nm, amdl), (cmdl_nm ,cmdl),  rms)<- load_mdl 
   check_report_wf amdl_nm (Just Total) amdl True
   --putStrLn . show $  (pe . fsg . mufs $ cmdl)
   --putStrLn . show $  (esD . fsg . mufs $ cmdl)
   --let sg = fsg . mufs $ cmdl 
   --let g = restrict (g_sg sg) $ esA sg
   --putStrLn . show $ g
   --putStrLn . show $ appl (pe sg)  (head . esD $ sg)
   --putStrLn . show $ srcPE g (appl (pe sg)  (head . esD $ sg))
   --putStrLn . show $ is_wf (Just Total) cmdl
   check_report_wf cmdl_nm (Just Total) cmdl True
   check_morphism ("Refinement of " ++ amdl_nm ++ " by " ++ cmdl_nm) (Just TotalM) cmdl rms amdl True
   print "Checking the instances..."
   (nm_g1, gwt1)<-loadGwT def_path "PWI1.gwt"
   (nm_g2, gwt2)<-loadGwT def_path "PWI2.gwt"
   check_report_wf nm_g1 (Just Total) gwt1 True
   check_report_wf nm_g2 (Just Total) gwt2 True
   check_ty_morphism (nm_g1 ++ " (Weak)") (Just WeakM) gwt1 cmdl True
   check_ty_morphism (nm_g1 ++ " (Total)") (Just TotalM) gwt1 cmdl True
   check_ty_morphism (nm_g2 ++ " (Weak)") (Just WeakM) gwt2 cmdl True
   check_ty_morphism (nm_g2 ++ " (Total)") (Just TotalM) gwt2 cmdl False

check_fs_and_ms :: IO ()
check_fs_and_ms = do 
   (nm_af, af)<-loadF def_path "F_AH.fr"
   (nm_f1, f1)<-loadF def_path "F_PW1.fr"
   (nm_f2, f2)<-loadF def_path "F_PW2.fr"
   (nm_f3, f3)<-loadF def_path "F_PW3.fr"
   (nm_f4, f4)<-loadF def_path "F_PW4.fr"
   (nm_f5, f5)<-loadF def_path "F_PW5.fr"
   (nm_f6, f6)<-loadF def_path "F_PW6.fr"
   (nm_f7, f7)<-loadF def_path "F_PW7.fr"
   (nm_f8, f8)<-loadF def_path "F_PW8.fr"
   (nm_m1, m1)<-loadM def_path "F_PW1.gm"
   (nm_m2, m2)<-loadM def_path "F_PW2.gm"
   (nm_m3, m3)<-loadM def_path "F_PW3.gm"
   (nm_m4, m4)<-loadM def_path "F_PW4.gm"
   (nm_m5, m5)<-loadM def_path "F_PW5.gm"
   (nm_m6, m6)<-loadM def_path "F_PW6.gm"
   (nm_m7, m7)<-loadM def_path "F_PW7.gm"
   (nm_m8, m8)<-loadM def_path "F_PW8.gm"
   check_report_wf nm_af (Just Partial) af True
   check_report_wf nm_f1 (Just Partial) f1 True
   check_report_wf nm_f2 (Just Partial) f2 True
   check_report_wf nm_f3 (Just Partial) f3 True
   check_report_wf nm_f4 (Just Partial) f4 True
   check_report_wf nm_f5 (Just Partial) f5 True
   check_report_wf nm_f6 (Just Partial) f6 True
   check_report_wf nm_f7 (Just Partial) f7 True
   check_report_wf nm_f8 (Just Partial) f8 True
   check_morphism ("Morphism '" ++ nm_m1 ++ "' (Partial)") (Just PartialM) f1 m1 af True
   check_morphism ("Morphism '" ++ nm_m1 ++ "' (Partial)") (Just PartialM) f2 m2 af True
   check_morphism ("Morphism '" ++ nm_m2 ++ "' (Partial)") (Just PartialM) f3 m3 af True
   check_morphism ("Morphism '" ++ nm_m3 ++ "' (Partial)") (Just PartialM) f4 m4 af True
   check_morphism ("Morphism '" ++ nm_m4 ++ "' (Partial)") (Just PartialM) f5 m5 af True
   check_morphism ("Morphism '" ++ nm_m5 ++ "' (Partial)") (Just PartialM) f6 m6 af True
   check_morphism ("Morphism '" ++ nm_m6 ++ "' (Partial)") (Just PartialM) f7 m7 af True
   check_morphism ("Morphism '" ++ nm_m7 ++ "' (Partial)") (Just PartialM) f8 m8 af True

check_instances :: IO ()
check_instances = do 
   ((_, amdl), (_ ,cmdl),  rms)<- load_mdl 
   (nm_g1, gwt1)<-loadGwT def_path "PWI1.gwt"
   (nm_g2, gwt2)<-loadGwT def_path "PWI2.gwt"
   check_report_wf nm_g1 (Just Total) gwt1 True
   check_report_wf nm_g2 (Just Total) gwt2 True
   check_ty_morphism (nm_g1 ++ " (Weak)") (Just WeakM) gwt1 cmdl True
   check_ty_morphism (nm_g1 ++ " (Total)") (Just TotalM) gwt1 cmdl True
   check_ty_morphism (nm_g2 ++ " (Weak)") (Just WeakM) gwt2 cmdl True
   check_ty_morphism (nm_g2 ++ " (Total)") (Just TotalM) gwt2 cmdl False
   --putStrLn $ show gwt1
   --let sg = fsg . reso_m $ cmdl
   --print (esVCnt sg)
   --print (appl (vcei sg) $ "Enat1_geq")
   --print $ toInt "v13"
   --print $ toNum sg "v13" (appl (fV gwt2) "v13")
  -- print $ toNum sg "V12" "V12"
   --print $ appl (vcei sg) "Edays_leq_Date_V31"
   --print $ filterS (isVCEECnt sg) (esVCnt sg)
   --print $ filterS (isVCENCnt sg) (esVCnt sg)
   --print $ eVCntOk sg "Emonth_leq"
   --print $ filterS (not . esCntOk sg) (esVCnt sg) 
   --if ivcesOk sg gwt2 then putStrLn "Ok" else putStrLn "Fail"
   --print $ appl (tgt sg) "Emonth_leq"
   --print $ (maybeToSet . snd . appl (vcei sg) $ "Emonth_leq")
   --print $ img (inv . fE $ gwt2) (singles "Emonth")
   --check_ty_morphism (nm_g1 ++ " (Total)") (Just TotalM) gwt1 cmdl False


main :: IO ()
main = do
    option_main_save do_main saveDrawings
