--------------------------
-- Project: PCs/Fragmenta
-- Module: 'vehicle_parts'
-- Description: Tests focused on example of vehicles, parts and wheels
-- Author: Nuno Amálio
---------------------------
import SGrs
import Grs
import Gr_Cls
import CheckUtils
import System.Environment
import Control.Monad(when)
import MyMaybe
import LoadCheckDraw
import GrswT
import Relations

def_path = "FragmentaTests/VehicleParts/"

saveDrawings = do
   draw_def def_path (def_path++"img/") "SG_Vehicle_Parts.sg"
   draw_def def_path (def_path++"img/") "SG_Car_Wheels.sg"
   draw_def def_path (def_path++"img/") "SG_Vehicle_Wheels.sg"
   draw_def def_path (def_path++"img/") "G_Car_Wheels_I1.gwt"
   draw_def def_path (def_path++"img/") "G_Car_Wheels_I2.gwt"
   draw_def def_path (def_path++"img/") "G_Vehicle_Wheels_I1.gwt"
   draw_def def_path (def_path++"img/") "G_Vehicle_Wheels_I2.gwt"

do_test1 = do
   (nm_asg, asg)<-load_sg_def def_path "SG_Vehicle_Parts.sg"
   (nm_csg, csg)<-load_sg_def def_path "SG_Car_Wheels.sg"
   (nm_m1, m1)<-load_morphism_def def_path "CW_VP.gm"
   check_report_wf nm_asg (Just Total) asg True
   check_report_wf nm_csg (Just Total) csg True
   check_morphism (nm_m1 ++ " morphism (Total)") (Just TotalM) csg m1 asg True

do_test2 = do
   (nm_asg, asg)<-load_sg_def def_path "SG_Vehicle_Parts.sg"
   (nm_csg, csg)<-load_sg_def def_path "SG_Vehicle_Wheels.sg"
   (nm_m1, m1)<-load_morphism_def def_path "VW_VP.gm"
   let m1' = totaliseForDer m1 csg 
   check_report_wf nm_asg (Just Total) asg True
   check_report_wf nm_csg (Just Total) csg True
   check_morphism (nm_m1 ++ " morphism (Weak)") (Just WeakM) csg m1' asg True
   check_morphism (nm_m1 ++ " morphism (Partial)") (Just PartialM) csg m1' asg True
   check_morphism (nm_m1 ++ " morphism (Total)") (Just TotalM) csg m1' asg True

do_test3 = do
   (nm_sg, sg)<-load_sg_def def_path "SG_Car_Wheels.sg"
   (nm_g, gwt)<-load_gwt_def def_path "G_Car_Wheels_I1.gwt"
   check_report_wf nm_sg (Just Total) sg True
   check_report_wf nm_g (Just Total) gwt True
   check_ty_morphism (nm_g ++ " (weak)") (Just WeakM) gwt sg True
   check_ty_morphism (nm_g ++ " (Total)") (Just TotalM) gwt sg True

do_test4 = do
   (nm_sg, sg)<-load_sg_def def_path "SG_Car_Wheels.sg"
   (nm_g, gwt)<-load_gwt_def def_path "G_Car_Wheels_I2.gwt"
   check_report_wf nm_sg (Just Total) sg True
   check_report_wf nm_g (Just Total) gwt True
   check_ty_morphism (nm_g ++ " (weak)") (Just WeakM) gwt sg True
   check_ty_morphism (nm_g ++ " (Total)") (Just TotalM) gwt sg False

do_test5 = do
   (nm_sg, sg)<-load_sg_def def_path "SG_Vehicle_Wheels.sg"
   (nm_g1, gwt1)<-load_gwt_def def_path "G_Vehicle_Wheels_I1.gwt"
   (nm_g2, gwt2)<-load_gwt_def def_path "G_Vehicle_Wheels_I2.gwt"
   check_report_wf nm_sg (Just Total) sg True
   check_report_wf nm_g1 (Just Total) gwt1 True
   check_report_wf nm_g2 (Just Total) gwt2 True
   check_ty_morphism (nm_g1 ++ " (weak)") (Just WeakM) gwt1 sg True
   check_ty_morphism (nm_g1 ++ " (Total)") (Just TotalM) gwt1 sg True
   check_ty_morphism (nm_g2 ++ " (weak)") (Just WeakM) gwt2 sg True
   check_ty_morphism (nm_g2 ++ " (Total)") (Just TotalM) gwt2 sg False



