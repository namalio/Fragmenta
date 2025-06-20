---------------------------
-- Project: Fragmenta
-- Module: 'Product'
-- Description: Module dedicated to the products example of the Fragmenta paper.
-- Author: Nuno Amálio
--------------------------
module FragmentaTests.Products.ProductsTest where

import LoadCheckDraw
import CheckUtils
import Gr_Cls
import NumString
import Utils

def_path :: String
def_path = "FragmentaTests/Commerce/"
img_path :: String
img_path = "FragmentaTests/Commerce/img/"

saveDrawings :: IO ()
saveDrawings = do
   draw_mdl def_path img_path "M_AC"
   draw_mdl def_path img_path "M_CC"
   draw_def def_path img_path "CI1.gwt"
   draw_def def_path img_path "CI2.gwt"

check_fs_and_ms :: IO ()
check_fs_and_ms = do 
   (nm_fnf, fnf)<-loadF def_path "F_NF.fr"
   (nm_fp, fp)<-loadF def_path "F_P.fr"
   (nm_fap, fap)<-loadF def_path "F_AP.fr"
   (nm_fbts, fbts)<-loadF def_path "F_BTs.fr"
   (nm_fe, fe)<-loadF def_path "F_E.fr"
   (nm_fpp, fpp)<-loadF def_path "F_PP.fr"
   (nm_fbk, fbk)<-loadF def_path "F_PBk.fr"
   (nm_fpf, fpf)<-loadF def_path "F_PF.fr"
   (nm_fbe, fbe)<-loadF def_path "F_PBe.fr"
   (nm_fps, fps)<-loadF def_path "F_PS.fr"
   check_report_wf nm_fnf (Just Partial) fnf True
   check_report_wf nm_fp (Just Partial) fp True
   check_report_wf nm_fap (Just Partial) fap True
   check_report_wf nm_fbts (Just Partial) fbts True
   check_report_wf nm_fe (Just Partial) fe True
   check_report_wf nm_fpp (Just Partial) fpp True
   check_report_wf nm_fbk (Just Partial) fbk True
   check_report_wf nm_fpf (Just Partial) fpf True
   check_report_wf nm_fbe (Just Partial) fbe True
   --check_morphism ("Morphism '" ++ nm_m1 ++ "' (Partial)") (Just PartialM) f1 m1 af True
   --check_morphism ("Morphism '" ++ nm_m1 ++ "' (Partial)") (Just PartialM) f2 m2 af True
   --check_morphism ("Morphism '" ++ nm_m2 ++ "' (Partial)") (Just PartialM) f3 m3 af True
   --check_morphism ("Morphism '" ++ nm_m3 ++ "' (Partial)") (Just PartialM) f4 m4 af True
   --check_morphism ("Morphism '" ++ nm_m4 ++ "' (Partial)") (Just PartialM) f5 m5 af True
   --check_morphism ("Morphism '" ++ nm_m5 ++ "' (Partial)") (Just PartialM) f6 m6 af True
   --check_morphism ("Morphism '" ++ nm_m6 ++ "' (Partial)") (Just PartialM) f7 m7 af True
   --check_morphism ("Morphism '" ++ nm_m7 ++ "' (Partial)") (Just PartialM) f8 m8 af True

do_main :: IO ()
do_main = do 
    (amdl_nm, amdl)<-loadMdl def_path "M_AC"
    (cmdl_nm, cmdl)<-loadMdl def_path "M_CC"
    rms<-load_rm_cmdl_def def_path "M_CC"
    check_report_wf amdl_nm (Just Total) amdl True
    check_report_wf cmdl_nm (Just Total) cmdl True
    check_morphism ("Refinement of " ++ amdl_nm ++ " by " ++ cmdl_nm) (Just TotalM) cmdl rms amdl True
    print "Checking the instances..."
    (nm_g1, gwt1)<-loadGwT def_path "CI1.gwt"
    (nm_g2, gwt2)<-loadGwT def_path "CI2.gwt"
    check_report_wf nm_g1 (Just Total) gwt1 True
    check_report_wf nm_g2 (Just Total) gwt2 True
    check_ty_morphism (nm_g1 ++ " (Weak)") (Just WeakM) gwt1 cmdl True
    check_ty_morphism (nm_g1 ++ " (Total)") (Just TotalM) gwt1 cmdl True
    check_ty_morphism (nm_g2 ++ " (Weak)") (Just WeakM) gwt2 cmdl True
    check_ty_morphism (nm_g2 ++ " (Total)") (Just TotalM) gwt2 cmdl False

main :: IO ()
main = do
    option_main_save do_main saveDrawings

