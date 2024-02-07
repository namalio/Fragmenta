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

