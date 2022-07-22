-------------------------
-- Project: PCs/Fragmenta
-- Module: 'Intance_tests'
-- Description: Test focused on SGs and the instance of relation
-- Author: Nuno Amálio
-------------------------
import SGrs
import Grs
import CheckUtils
import LoadCheckDraw
import Control.Monad(when)
import FrParsing
import MyMaybe
import SGElemTys
import Mult
import SimpleFuns
import Utils
import GrswT
import Relations

def_path = "FragmentaTests/InstanceOf/"
img_path = "FragmentaTests/InstanceOf/img/"

-- This test does the instance of manually. Through a morphism at the graph level which is required to commute
do_test1 = do
   (nm1, sg1)<-load_sg_def def_path "SG_Block_Port.sg"
   (nm2, sg2)<-load_sg_def def_path "SG_Block_Conf.sg"
   (nm_g1, gwt1)<-load_gwt_def def_path "G_Blocks_I1.gwt"
   (nm_g2, gwt2)<-load_gwt_def def_path "G_Conf_I1.gwt"
   (nm_g3, gwt3)<-load_gwt_def def_path "G_Conf_I2.gwt"
   (nm_m1, m1)<-load_morphism_def def_path "m_Conf_Blocks_I1.gm"
   (nm_m2, m2)<-load_morphism_def def_path "m_Conf_Blocks_I2.gm"
   check_report_wf nm1 (Just Total) sg1 True
   check_report_wf nm2 (Just Total) sg2 True
   check_report_wf nm2 (Just Total) sg2 True
   check_report_wf nm_g1 (Just Total) gwt1 True
   check_report_wf nm_g2 (Just Total) gwt2 True
   check_report_wf nm_g3 (Just Total) gwt3 True
   check_ty_morphism (nm_g1 ++ " (Weak)") (Just WeakM) gwt1 sg1 True
   check_ty_morphism (nm_g1 ++ " (Total)") (Just TotalM) gwt1 sg1 True
   check_ty_morphism (nm_g2 ++ " (Weak)") (Just WeakM) gwt2 sg2 True
   check_ty_morphism (nm_g2 ++ " (Total)") (Just TotalM) gwt2 sg2 True
   check_ty_morphism (nm_g3 ++ " (Weak)") (Just WeakM) gwt3 sg2 True
   check_ty_morphism (nm_g3 ++ " (Total)") (Just TotalM) gwt3 sg2 True
   --putStrLn (show $ dom_of . fV $ m1)
   --putStrLn (show $ restrictNs (gOf gwt2) (dom_of . fV $ m1) )
   check_morphism (nm_m1 ++ ": " ++ nm_g2 ++ " -> " ++ nm_g1) Nothing (restrictNs (gOf gwt2) (dom_of . fV $ m1)) m1 (gOf gwt1) True
   check_morphism (nm_m2 ++ ": " ++ nm_g3 ++ " -> " ++ nm_g1) Nothing (restrictNs (gOf gwt3) (dom_of . fV $ m2)) m2 (gOf gwt1) False



--The first morphism should not be a refinement morphism because the concrete model (in that case SG_1) looses things out.
do_main = do
   do_test1
   --do_test2
   --do_test3
   --do_test_4
   --do_test_5
   --do_test_6
   --do_test_7

saveDrawings = do
   draw_def def_path img_path "SG_Block_Port.sg"
   draw_def def_path img_path "SG_Block_Conf.sg"
   draw_def def_path img_path "G_Blocks_I1.gwt"
   draw_def def_path img_path "G_Conf_I1.gwt"
   draw_def def_path img_path "G_Conf_I2.gwt"

main = do
   option_main_save do_main saveDrawings

