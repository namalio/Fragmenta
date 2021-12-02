------------------
-- Project: PCs/Fragmenta
-- Module: 'Sg_tests'
-- Description: Test which focus on SGs, following many examples 
--    given in the SGs section of the Fragmenta paper
-- Author: Nuno Amálio
--------------------
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

def_path = "FragmentaTests/SGTests/"
img_path = "FragmentaTests/SGTests/img/"


-- Example used in the PCs paper with morphisms m_1..m7, just checks that the SG morphisms are valid
do_test_1 = do
   (nm1, sg1)<-load_sg_def def_path "SG_Person_Vehicle_Any.sg"
   (nm2, sg2)<-load_sg_def def_path "SG_Person_Vehicle_I.sg"
   (nm3, sg3)<-load_sg_def def_path "SG_Employee_Car.sg"
   (nm4, sg4)<-load_sg_def def_path "SG_PGC.sg"
   (nm5, sg5)<-load_sg_def def_path "SG_PVI.sg"
   (nm_m1, m1)<-load_morphism_def def_path "m_PVI_To_PV.gm"
   (nm_m2, m2)<-load_morphism_def def_path "m_EC_To_PV.gm"
   (nm_m3, m3)<-load_morphism_def def_path "m_Employee_Car.gm"
   (nm_m4, m4)<-load_morphism_def def_path "m_Employee_Car_Inv.gm"
   (nm_m5, m5)<-load_morphism_def def_path "m_PGC.gm"
   (nm_m6, m6)<-load_morphism_def def_path "m_PVI.gm"
   check_report_wf nm1 (Just Total) sg1 True
   check_report_wf nm2 (Just Total) sg2 True
   check_report_wf nm3 (Just Total) sg3 True
   check_report_wf nm4 (Just Total) sg4 True
   check_report_wf nm5 (Just Total) sg5 True
   check_morphism (nm_m1 ++ ": " ++ nm2 ++ "->" ++ nm1 ++ " (Weak)") (Just WeakM) sg2 m1 sg1 True
   check_morphism (nm_m2 ++ ": " ++ nm3 ++ "->" ++ nm1 ++ " (Weak)") (Just WeakM) sg3 m2 sg1 True
   check_morphism (nm_m3 ++ ": " ++ nm3 ++ "->" ++ nm2 ++ " (Weak)") (Just WeakM) sg3 m3 sg2 True
   check_morphism (nm_m4 ++ ": " ++ nm2 ++ "->" ++ nm3 ++ " (Weak)") (Just WeakM) sg2 m4 sg3 True
   check_morphism (nm_m5 ++ ": " ++ nm4 ++ "->" ++ nm1 ++ " (Weak)") (Just WeakM) sg4 m5 sg1 True
   check_morphism (nm_m6 ++ ": " ++ nm5 ++ "->" ++ nm1 ++ " (Weak)") (Just WeakM) sg5 m6 sg1 True
   check_morphism ("Union of morphisms: " ++ nm4 ++ " U " ++ nm5 ++ "->" ++ nm1 ++ " (Weak)") (Just WeakM) (sg4 `union_sg` sg5) (m5 `union_gm` m6) sg1 True

do_test_2 = do
   (nm1, sg1)<-load_sg_def def_path "SG_Person_Vehicle_Any.sg"
   (nm2, sg2)<-load_sg_def def_path "SG_Person_Vehicle_I.sg"
   (nm3, sg3)<-load_sg_def def_path "SG_Employee_Car.sg"
   (nm_m1, m1)<-load_morphism_def def_path "m_Employee_Car.gm"
   (nm_m2, m2)<-load_morphism_def def_path "m_Employee_Car_Inv.gm"
   (nm_m3, m3)<-load_morphism_def def_path "m_PVI_To_PV.gm"
   (nm_m4, m4)<-load_morphism_def def_path "m_EC_To_PV.gm"
   check_report_wf nm1 (Just Total) sg1 True
   check_report_wf nm2 (Just Total) sg2 True
   check_report_wf nm3 (Just Total) sg3 True
   check_morphism (nm_m1 ++ " (Partial)") (Just PartialM) sg3 m1 sg2 True
   check_morphism (nm_m1 ++ " (Total)") (Just TotalM) sg3 m1 sg2 False
   check_morphism (nm_m2 ++ " (Total)") (Just TotalM) sg2 m2 sg3 True
   check_morphism (nm_m3 ++ ": " ++ nm2 ++ "->" ++ nm1 ++ " (Total)") (Just TotalM) sg2 m3 sg1 True
   check_morphism (nm_m4 ++ ": " ++ nm3 ++ "->" ++ nm1 ++ " (Total)") (Just TotalM) sg3 m4 sg1 True

do_test_3 = do
   (nm1, sg1)<-load_sg_def def_path "SG_Person_Vehicle_Any.sg"
   (nm2, sg2)<-load_sg_def def_path "SG_PGC.sg"
   (nm3, sg3)<-load_sg_def def_path "SG_PVI.sg"
   (nm_m1, m1)<-load_morphism_def def_path "m_PGC.gm"
   (nm_m2, m2)<-load_morphism_def def_path "m_PVI.gm"
   check_report_wf nm1 (Just Total) sg1 True
   check_report_wf nm2 (Just Partial) sg2 True
   check_report_wf nm3 (Just Partial) sg3 True
   check_morphism (nm_m1 ++ ": " ++ nm2 ++ "->" ++ nm1 ++ " (Partial)") (Just PartialM) sg2 m1 sg1 True
   check_morphism (nm_m2 ++ ": " ++ nm3 ++ "->" ++ nm1 ++ " (Partial)") (Just PartialM) sg3 m2 sg1 True
   check_morphism ("Union of morphisms: " ++ nm3 ++ " U " ++ nm2 ++ "->" ++ nm1 ++ " (Total)") (Just TotalM) (sg3 `union_sg` sg2) (m1 `union_gm` m2) sg1 True

do_test_4 = do
   (nm1, sg1)<-load_sg_def def_path "SG_Employee_Car.sg"
   (nm2, sg2)<-load_sg_def def_path "SG_Person_Vehicle_I.sg"
   (nm_m1, m1)<-load_morphism_def def_path "m_Employee_Car.gm"
   (nm_m2, m2)<-load_morphism_def def_path "m_Employee_Car_Inv.gm"
   check_report_wf nm1 (Just Total) sg1 True
   check_report_wf nm2 (Just Total) sg2 True
   check_morphism (nm_m1 ++ " (Partial)") (Just PartialM) sg1 m1 sg2 True
   check_morphism (nm_m1 ++ " (Total)") (Just TotalM) sg1 m1 sg2 False
   check_morphism (nm_m2 ++ " (Total)") (Just TotalM) sg2 m2 sg1 True

do_test_5 = do
   (nm1, sg1)<-load_sg_def def_path "SG_Employee_Car.sg"
   (nm2, sg2)<-load_sg_def def_path "SG_Person_Vehicle_Ib.sg"
   (nm_m1, m1)<-load_morphism_def def_path "m_Employee_Car.gm"
   (nm_m2, m2)<-load_morphism_def def_path "m_Employee_Car_Inv.gm"
   (nm_m3, m3)<-load_morphism_def def_path "m_Employee_Carb.gm"
   check_report_wf nm1 (Just Total) sg1 True
   check_report_wf nm2 (Just Total) sg2 True
   check_morphism (nm_m1 ++ " (Weak)") (Just WeakM) sg1 m1 sg2 True
   check_morphism (nm_m1 ++ " (Partial)") (Just PartialM) sg1 m1 sg2 True
   check_morphism (nm_m1 ++ " (Total)") (Just TotalM) sg1 m1 sg2 True
   check_morphism (nm_m3 ++ " (Total)") (Just TotalM) sg1 m3 sg2 True
   check_morphism (nm_m2 ++ " (Weak)") (Just WeakM) sg2 m2 sg1 True
   check_morphism (nm_m2 ++ " (Total)") (Just TotalM) sg2 m2 sg1 True

do_test_6= do
   (nm1, sg1)<-load_sg_def def_path "SG_Employee_Car.sg"
   (nm2, sg2)<-load_sg_def def_path "SG_Person_Vehicle_Ic.sg"
   (nm_m1, m1)<-load_morphism_def def_path "m_Employee_Car.gm"
   (nm_m2, m2)<-load_morphism_def def_path "m_Employee_Carb.gm"
   (nm_m3, m3)<-load_morphism_def def_path "m_Employee_Car_Inv.gm"
   check_report_wf nm1 (Just Total) sg1 True
   check_report_wf nm2 (Just Total) sg2 True
   check_morphism (nm_m1 ++ " (Weak)") (Just WeakM) sg1 m1 sg2 True
   check_morphism (nm_m1 ++ " (Partial)") (Just PartialM) sg1 m1 sg2 True
   check_morphism (nm_m1 ++ " (Total)") (Just TotalM) sg1 m1 sg2 False
   check_morphism (nm_m3 ++ " (Total)") (Just TotalM) sg1 m2 sg2 True
   check_morphism (nm_m2 ++ " (Weak)") (Just WeakM) sg2 m2 sg1 False

do_test_7 = do
   (nm1, sg1)<-load_sg_def def_path "SG_Person_Vehicle.sg"
   (nm2, sg2)<-load_sg_def def_path "SG_Person_Vehicle_Ic.sg"
   (nm_m1, m1)<-load_morphism_def def_path "m_Person_Vehicle_I.gm"
   (nm_m2, m2)<-load_morphism_def def_path "m_Person_Vehicle_2_I.gm"
   (nm_m3, m3)<-load_morphism_def def_path "m_Person_Vehicle_2_Ib.gm"
   check_report_wf nm1 (Just Total) sg1 True
   check_report_wf nm2 (Just Total) sg2 True
   check_morphism (nm_m1 ++ " (Total)") (Just TotalM) sg2 m1 sg1 True
   check_morphism (nm_m2 ++ " (Total)") (Just TotalM) sg1 m2 sg2 True
   check_morphism (nm_m3 ++ " (Weak)") (Just WeakM) sg1 m3 sg2 True
   check_morphism (nm_m3 ++ " (Partial)") (Just PartialM) sg1 m3 sg2 True
   check_morphism (nm_m3 ++ " (Total)") (Just TotalM) sg1 m3 sg2 False


--The first morphism should not be a refinement morphism because the concrete model (in that case SG_1) looses things out.
do_main = do
   do_test_1
   do_test_2
   do_test_3
   do_test_4
   do_test_5
   do_test_6
   do_test_7

saveGraphs = do
   draw_def def_path img_path "SG_Person_Vehicle_Any.sg"
   draw_def def_path img_path "SG_Employee_Car.sg"
   draw_def def_path img_path "SG_Person_Vehicle_I.sg"
   draw_def def_path img_path "SG_Person_Vehicle_Ib.sg"
   draw_def def_path img_path "SG_Person_Vehicle_Ic.sg"
   draw_def def_path img_path "SG_Person_Vehicle.sg"
   draw_def def_path img_path "SG_PGC.sg"
   draw_def def_path img_path "SG_PVI.sg"

main = do
   option_main_save do_main saveGraphs

