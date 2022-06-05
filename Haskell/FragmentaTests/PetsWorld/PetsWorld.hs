
------------------
-- Project: PCs/Fragmenta
-- Module: 'PetsWorld'
-- Description: Module dedicated to the pets world example.
-- Author: Nuno Amálio
-----------------
module PetsWorldTest where

import Gr_Cls
import Frs
import Grs
import LoadCheckDraw
import CheckUtils
import Mdls
import Relations
import Sets
import Utils

def_path = "FragmentaTests/PetsWorld/"
img_path = "FragmentaTests/PetsWorld/img/"

saveDrawings = do
   draw_mdl def_path img_path "M_AHW"
   draw_mdl def_path img_path "M_PW"

do_main = do 
   amdl<-load_mdl_def def_path "M_AHW"
   cmdl<-load_mdl_def def_path "M_PW"
   rms<-load_rm_cmdl_def def_path "M_PW"
   (nm_m1, m1)<-load_morphism_def def_path "F_PW1.gm"
   (nm_m2, m2)<-load_morphism_def def_path "F_PW2.gm"
   (nm_m3, m3)<-load_morphism_def def_path "F_PW3.gm"
   (nm_m4, m4)<-load_morphism_def def_path "F_PW4.gm"
   (nm_m5, m5)<-load_morphism_def def_path "F_PW5.gm"
   check_report_wf "M_AHW" (Just Total) amdl True
   check_report_wf "M_PW" (Just Total) cmdl True
   check_morphism "Refinement of M_AHW by M_PW " (Just TotalM) cmdl rms amdl True


main = do
    option_main_save do_main saveDrawings
