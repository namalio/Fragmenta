
---------------------------
-- Project: PCs/Fragmenta
-- Module: 'PetsWorld'
-- Description: Module dedicated to the pets world example given in the Fragmenta paper.
-- Author: Nuno Amálio
--------------------------
module PetsWorldTest where

import Gr_Cls
import SGrs
import Frs
import Grs
import LoadCheckDraw
import CheckUtils
import Mdls
import Relations
import Sets
import Utils
import Path_Expressions

def_path = "FragmentaTests/PetsWorld/"
img_path = "FragmentaTests/PetsWorld/img/"

saveDrawings = do
   draw_mdl def_path img_path "M_AHW"
   draw_mdl def_path img_path "M_PW"
   draw_def def_path img_path "PWI1.gwt"

load_mdl = do
   amdl<-load_mdl_def def_path "M_AHW"
   cmdl<-load_mdl_def def_path "M_PW"
   rms<-load_rm_cmdl_def def_path "M_PW"
   return (amdl, cmdl, rms)

do_main = do 
   (amdl, cmdl, rms)<- load_mdl 
   check_report_wf "M_AHW" (Just Total) amdl True
   --putStrLn . show $  (pe . fsg . mufs $ cmdl)
   --putStrLn . show $  (esD . fsg . mufs $ cmdl)
   --let sg = fsg . mufs $ cmdl 
   --let g = restrict (g_sg sg) $ esA sg
   --putStrLn . show $ g
   --putStrLn . show $ appl (pe sg)  (head . esD $ sg)
   --putStrLn . show $ srcPE g (appl (pe sg)  (head . esD $ sg))
   --putStrLn . show $ is_wf (Just Total) cmdl
   check_report_wf "M_PW" (Just Total) cmdl True
   check_morphism "Refinement of M_AHW by M_PW " (Just TotalM) cmdl rms amdl True

check_fs_and_ms = do 
   (nm_af, af)<-load_fr_def def_path "F_AH.fr"
   (nm_f1, f1)<-load_fr_def def_path "F_PW1.fr"
   (nm_f2, f2)<-load_fr_def def_path "F_PW2.fr"
   (nm_f3, f3)<-load_fr_def def_path "F_PW3.fr"
   (nm_f4, f4)<-load_fr_def def_path "F_PW4.fr"
   (nm_f5, f5)<-load_fr_def def_path "F_PW5.fr"
   (nm_f6, f6)<-load_fr_def def_path "F_PW6.fr"
   (nm_m1, m1)<-load_morphism_def def_path "F_PW1.gm"
   (nm_m2, m2)<-load_morphism_def def_path "F_PW2.gm"
   (nm_m3, m3)<-load_morphism_def def_path "F_PW3.gm"
   (nm_m4, m4)<-load_morphism_def def_path "F_PW4.gm"
   (nm_m5, m5)<-load_morphism_def def_path "F_PW5.gm"
   (nm_m6, m6)<-load_morphism_def def_path "F_PW6.gm"
   check_report_wf nm_af (Just Partial) af True
   check_report_wf nm_f1 (Just Partial) f1 True
   check_report_wf nm_f2 (Just Partial) f2 True
   check_report_wf nm_f3 (Just Partial) f3 True
   check_report_wf nm_f4 (Just Partial) f4 True
   check_report_wf nm_f5 (Just Partial) f5 True
   check_report_wf nm_f6 (Just Partial) f6 True
   check_morphism ("Morphism '" ++ nm_m1 ++ "' (Partial)") (Just PartialM) f1 m1 af True
   check_morphism ("Morphism '" ++ nm_m2 ++ "' (Partial)") (Just PartialM) f2 m2 af True
   check_morphism ("Morphism '" ++ nm_m3 ++ "' (Partial)") (Just PartialM) f3 m3 af True
   check_morphism ("Morphism '" ++ nm_m4 ++ "' (Partial)") (Just PartialM) f4 m4 af True
   check_morphism ("Morphism '" ++ nm_m5 ++ "' (Partial)") (Just PartialM) f5 m5 af True
   check_morphism ("Morphism '" ++ nm_m6 ++ "' (Partial)") (Just PartialM) f6 m6 af True

check_instances = do 
   (amdl, cmdl, rms)<- load_mdl 
   (nm_g1, gwt1)<-load_gwt_def def_path "PWI1.gwt"
   check_report_wf nm_g1 (Just Total) gwt1 True
   check_ty_morphism (nm_g1 ++ " (Weak)") (Just WeakM) gwt1 cmdl True
   check_ty_morphism (nm_g1 ++ " (Total)") (Just TotalM) gwt1 cmdl True
   --putStrLn $ show gwt1
   --check_ty_morphism (nm_g1 ++ " (Total)") (Just TotalM) gwt1 cmdl False


main = do
    option_main_save do_main saveDrawings
