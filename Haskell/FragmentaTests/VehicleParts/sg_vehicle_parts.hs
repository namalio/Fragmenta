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
import Utils

def_path = "FragmentaTests/SGVehicleParts/"
img_path = def_path ++ "img/"

saveDrawings = do
   draw_def def_path img_path "SG_Vehicle_Parts.sg"
   draw_def def_path img_path "SG_Car_Wheels.sg"
   draw_def def_path img_path "SG_Vehicle_Wheels.sg"
   draw_def def_path img_path "SG_Pair_Bicycle.sg"
   draw_def def_path img_path "G_Car_Wheels_I1.gwt"
   draw_def def_path img_path "G_Car_Wheels_I2.gwt"
   draw_def def_path img_path "G_Vehicle_Wheels_I1.gwt"
   draw_def def_path img_path "G_Vehicle_Wheels_I2.gwt"
   draw_def def_path img_path "SG_Vehicle_Wheels.sg"
   draw_def def_path img_path "SG_Vehicle_Wheels.sg"
   draw_def def_path img_path "G_Bicycle_I1.gwt"
   draw_def def_path img_path "G_Bicycle_I2.gwt"
   draw_def def_path img_path "SG_Pair_Bicycle_Car.sg"
   draw_def def_path img_path "G_Bicycle_Car_I1.gwt"
   draw_def def_path img_path "G_Bicycle_Car_I2.gwt"

test1 = do
   -- Checks the refinement
   (nm_asg, asg)<-load_sg_def def_path "SG_Vehicle_Parts.sg" -- SG_VP of Fig. 6d
   (nm_csg, csg)<-load_sg_def def_path "SG_Car_Wheels.sg" 
   (nm_m1, m1)<-load_morphism_def def_path "CW_VP.gm"
   putStrLn "Test 1"
   check_report_wf nm_asg (Just Total) asg True
   check_report_wf nm_csg (Just Total) csg True
   check_morphism (nm_m1 ++ ": " ++ nm_csg ++ "->" ++ nm_asg ++ " (Weak, morphism)") (Just WeakM) csg m1 asg True
   check_morphism (nm_m1 ++ ": " ++ nm_csg ++ "->" ++ nm_asg ++ " (Total, refinement)") (Just TotalM) csg m1 asg True

test2 = do
   (nm_asg, asg)<-load_sg_def def_path "SG_Vehicle_Parts.sg" -- SG_VP of Fig. 6d
   (nm_csg, csg)<-load_sg_def def_path "SG_Vehicle_Wheels.sg" -- SG_VWs of Fig. 6e
   (nm_m1, m1)<-load_morphism_def def_path "VW_VP.gm"
   putStrLn "Test 2"
   check_report_wf nm_asg (Just Total) asg True
   check_report_wf nm_csg (Just Total) csg True
   check_morphism (nm_m1 ++ " morphism (Weak)") (Just WeakM) csg m1 asg True
   check_morphism (nm_m1 ++ " morphism (Partial)") (Just PartialM) csg m1 asg True
   check_morphism (nm_m1 ++ " morphism (Total)") (Just TotalM) csg m1 asg True

test3 = do
   (nm_asg, asg)<-load_sg_def def_path "SG_Vehicle_Parts.sg" -- SG_VP of Fig. 6d
   (nm_csg, csg)<-load_sg_def def_path "SG_Pair_Bicycle.sg"  -- SG_BI of Fig. 6f
   (nm_m1, m1)<-load_morphism_def def_path "PB_VP.gm"
   putStrLn "Test 3"
   check_report_wf nm_asg (Just Total) asg True
   check_report_wf nm_csg (Just Total) csg True
   check_morphism (nm_m1 ++ " morphism (Weak)") (Just WeakM) csg m1 asg True
   check_morphism (nm_m1 ++ " morphism (Partial)") (Just PartialM) csg m1 asg True
   check_morphism (nm_m1 ++ " morphism (Total)") (Just TotalM) csg m1 asg True

test4 = do
   (nm_asg, asg)<-load_sg_def def_path "SG_Vehicle_Parts.sg" -- SG_VP of Fig. 6d
   (nm_csg, csg)<-load_sg_def def_path "SG_Pair_Bicycle_Car.sg" -- SG_BI of Fig. 6g
   (nm_m1, m1)<-load_morphism_def def_path "PBC_VP.gm"
   putStrLn "Test 4"
   check_report_wf nm_asg (Just Total) asg True
   check_report_wf nm_csg (Just Total) csg True
   check_morphism (nm_m1 ++ " morphism (Weak)") (Just WeakM) csg m1 asg True
   check_morphism (nm_m1 ++ " morphism (Partial)") (Just PartialM) csg m1 asg True
   check_morphism (nm_m1 ++ " morphism (Total)") (Just TotalM) csg m1 asg True

test5 = do
    (nm_sg, sg)<-load_sg_def def_path "SG_Car_Wheels.sg"
    (nm_g, gwt)<-load_gwt_def def_path "G_Car_Wheels_I1.gwt"
    check_report_wf nm_sg (Just Total) sg True
    check_report_wf nm_g (Just Total) gwt True
    check_ty_morphism (nm_g ++ " (weak)") (Just WeakM) gwt sg True
    check_ty_morphism (nm_g ++ " (Total)") (Just TotalM) gwt sg True

test6 = do
   (nm_sg, sg)<-load_sg_def def_path "SG_Car_Wheels.sg"
   (nm_g, gwt)<-load_gwt_def def_path "G_Car_Wheels_I2.gwt"
   check_report_wf nm_sg (Just Total) sg True
   check_report_wf nm_g (Just Total) gwt True
   check_ty_morphism (nm_g ++ " (weak)") (Just WeakM) gwt sg True
   check_ty_morphism (nm_g ++ " (Total)") (Just TotalM) gwt sg False

test7 = do
   (nm_sg, sg)<-load_sg_def def_path "SG_Vehicle_Wheels.sg" -- SGVWs in Fig. 8g
   (nm_g1, gwt1)<-load_gwt_def def_path "G_Vehicle_Wheels_I1.gwt" -- Fig 8i
   (nm_g2, gwt2)<-load_gwt_def def_path "G_Vehicle_Wheels_I2.gwt" -- Fig 8j
   check_report_wf nm_sg (Just Total) sg True
   check_report_wf nm_g1 (Just Total) gwt1 True
   check_report_wf nm_g2 (Just Total) gwt2 True
   check_ty_morphism (nm_g1 ++ " (weak)") (Just WeakM) gwt1 sg True
   check_ty_morphism (nm_g1 ++ " (Total)") (Just TotalM) gwt1 sg True
   check_ty_morphism (nm_g2 ++ " (weak)") (Just WeakM) gwt2 sg True
   check_ty_morphism (nm_g2 ++ " (Total)") (Just TotalM) gwt2 sg False

-- do_test8 = do
--    (nm_sg, sg)<-load_sg_def def_path "SG_Pair_Bicycle.sg"
--    (nm_g1, gwt1)<-load_gwt_def def_path "G_Bicycle_I1.gwt"
--    check_report_wf nm_sg (Just Total) sg True
--    check_ty_morphism (nm_g1 ++ " (weak)") (Just WeakM) gwt1 sg True
--    check_ty_morphism (nm_g1 ++ " (Total)") (Just TotalM) gwt1 sg True

-- do_test9 = do
--    (nm_sg, sg)<-load_sg_def def_path "SG_Pair_Bicycle.sg"
--    (nm_g1, gwt1)<-load_gwt_def def_path "G_Bicycle_I2.gwt"
--    check_report_wf nm_sg (Just Total) sg True
--    check_ty_morphism (nm_g1 ++ " (weak)") (Just WeakM) gwt1 sg True
--    check_ty_morphism (nm_g1 ++ " (Total)") (Just TotalM) gwt1 sg False

-- do_test10 = do
--    (nm_sg, sg)<-load_sg_def def_path "SG_Pair_Bicycle_Car.sg"
--    (nm_g1, gwt1)<-load_gwt_def def_path "G_Bicycle_Car_I1.gwt"
--    (nm_g2, gwt2)<-load_gwt_def def_path "G_Bicycle_Car_I2.gwt"
--    (nm_g3, gwt3)<-load_gwt_def def_path "G_Bicycle_Car_I3.gwt"
--    check_report_wf nm_sg (Just Total) sg True
--    check_ty_morphism (nm_g1 ++ " (Weak)") (Just WeakM) gwt1 sg True
--    check_ty_morphism (nm_g1 ++ " (Total)") (Just TotalM) gwt1 sg True
--    check_ty_morphism (nm_g2 ++ " (Weak)") (Just WeakM) gwt2 sg True
--    check_ty_morphism (nm_g2 ++ " (Total)") (Just TotalM) gwt2 sg False
--    check_ty_morphism (nm_g3 ++ " (Weak)") (Just WeakM) gwt3 sg True
--    check_ty_morphism (nm_g3 ++ " (Total)") (Just TotalM) gwt3 sg False

do_main = do
   test1
   test2
   test3
   test4
   test5
   test6
--   do_test7
--   do_test8
--   do_test9
--   do_test10

main = do
   option_main_save do_main saveDrawings




