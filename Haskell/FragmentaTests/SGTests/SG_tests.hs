-------------------------
-- Project: PCs/Fragmenta
-- Module: 'SG_tests'
-- Description: Test focused on SGs, morphisms and refinement following many examples given in the SGs section of the Fragmenta paper
-- Author: Nuno Amálio
-------------------------
import SGrs
import Grs
import CheckUtils
import LoadCheckDraw
import Control.Monad(when)
import MyMaybe
import SGElemTys
import Mult
import SimpleFuns
import Utils

def_path = "FragmentaTests/SGTests/"
img_path = "FragmentaTests/SGTests/img/"


-- Example used in PCs paper with morphisms m_1..m4 (Fig. 6a and 6b)
-- just checks that SGs and morphisms are valid
test1 :: IO ()
test1 = do
   (nm1, sg1)<-loadSG def_path "SG_PVO.sg" -- Fig 6a
   (nm2, sg2)<-loadSG def_path "SG_PV.sg" -- Fig 6b
   (nm3, sg3)<-loadSG def_path "SG_EC.sg" -- Fig 6b
   (nm_m1, m1)<-loadM def_path "m_PV_To_PVO.gm"
   (nm_m2, m2)<-loadM def_path "m_EC_To_PVO.gm"
   (nm_m3, m3)<-loadM def_path "m_EC_PV.gm"
   (nm_m4, m4)<-loadM def_path "m_PV_EC.gm"
   putStrLn "Test 1:"
   check_report_wf nm1 (Just Total) sg1 True
   check_report_wf nm2 (Just Total) sg2 True
   check_report_wf nm3 (Just Total) sg3 True
   check_morphism (nm_m1 ++ ": " ++ nm2 ++ "->" ++ nm1 ++ " (Weak, morphism)") (Just WeakM) sg2 m1 sg1 True
   check_morphism (nm_m2 ++ ": " ++ nm3 ++ "->" ++ nm1 ++ " (Weak, morphism)") (Just WeakM) sg3 m2 sg1 True
   check_morphism (nm_m3 ++ ": " ++ nm3 ++ "->" ++ nm2 ++ " (Weak, morphism)") (Just WeakM) sg3 m3 sg2 True
   check_morphism (nm_m4 ++ ": " ++ nm2 ++ "->" ++ nm3 ++ " (Weak, morphism)") (Just WeakM) sg2 m4 sg3 True
   check_morphism (nm_m1 ++ ": " ++ nm2 ++ "->" ++ nm1 ++ " (Total refinement)") (Just TotalM) sg2 m1 sg1 True
   check_morphism (nm_m2 ++ ": " ++ nm3 ++ "->" ++ nm1 ++ " (Total refinement)") (Just TotalM) sg3 m2 sg1 True
   check_morphism (nm_m3 ++ ": " ++ nm3 ++ "->" ++ nm2 ++ " (Partial refinement)") (Just PartialM) sg3 m3 sg2 True
   check_morphism (nm_m3 ++ ": " ++ nm3 ++ "->" ++ nm2 ++ " (Total refinement)") (Just TotalM) sg3 m3 sg2 False
   check_morphism (nm_m4 ++ ": " ++ nm2 ++ "->" ++ nm3 ++ " (Total refinement)") (Just TotalM) sg2 m4 sg3 True

-- Above the total refinement from 'SG_EC' to 'SG_PV' is not total as there are normal nodes out of the morphism
-- A variation of the previous example in which all refinements are total because PV includes abstract nodes
test1a :: IO ()
test1a = do 
   (nm1, sg1)<-loadSG def_path "SG_PVO.sg" -- Fig 6a
   (nm2, sg2)<-loadSG def_path "SG_PVb.sg" -- Fig 6b
   (nm3, sg3)<-loadSG def_path "SG_EC.sg" -- Fig 6b
   (nm_m1, m1)<-loadM def_path "m_PV_To_PVO.gm"
   (nm_m2, m2)<-loadM def_path "m_EC_To_PVO.gm"
   (nm_m3, m3)<-loadM def_path "m_EC_PV.gm"
   (nm_m4, m4)<-loadM def_path "m_PV_EC.gm"
   putStrLn "Test 1a:"
   check_report_wf nm1 (Just Total) sg1 True
   check_report_wf nm2 (Just Total) sg2 True
   check_report_wf nm3 (Just Total) sg3 True
   check_morphism (nm_m1 ++ ": " ++ nm2 ++ "->" ++ nm1 ++ " (Weak, morphism)") (Just WeakM) sg2 m1 sg1 True
   check_morphism (nm_m2 ++ ": " ++ nm3 ++ "->" ++ nm1 ++ " (Weak, morphism)") (Just WeakM) sg3 m2 sg1 True
   check_morphism (nm_m4 ++ ": " ++ nm2 ++ "->" ++ nm3 ++ " (Weak, morphism)") (Just WeakM) sg2 m4 sg3 True
   check_morphism (nm_m1 ++ ": " ++ nm2 ++ "->" ++ nm1 ++ " (Total, refinement)") (Just TotalM) sg2 m1 sg1 True
   check_morphism (nm_m3 ++ ": " ++ nm3 ++ "->" ++ nm2 ++ " (Total, refinement)") (Just TotalM) sg3 m3 sg2 True
   check_morphism (nm_m4 ++ ": " ++ nm2 ++ "->" ++ nm3 ++ " (Total, refinement)") (Just TotalM) sg2 m4 sg3 True



-- Example used in the PCs paper with morphisms m_1..m7, just checks that the SG morphisms are valid
--test_1c = do
--   (nm1, sg1)<-loadSG def_path "SG_Person_Vehicle_Other.sg"
--   (nm2, sg2)<-loadSG def_path "SG_Person_Vehicle_I.sg"
--   (nm3, sg3)<-loadSG def_path "SG_Employee_Car.sg"
--   (nm4, sg4)<-loadSG def_path "SG_PGC.sg"
--   (nm5, sg5)<-loadSG def_path "SG_PVI.sg"
--   (nm_m1, m1)<-loadM def_path "m_PVI_To_PV.gm"
--   (nm_m2, m2)<-loadM def_path "m_EC_To_PV.gm"
--   (nm_m3, m3)<-loadM def_path "m_Employee_Car.gm"
--   (nm_m4, m4)<-loadM def_path "m_Employee_Car_Inv.gm"
--   (nm_m5, m5)<-loadM def_path "m_PGC.gm"
--   (nm_m6, m6)<-loadM def_path "m_PVI.gm"
--   check_report_wf nm1 (Just Total) sg1 True
--   check_report_wf nm2 (Just Total) sg2 True
--   check_report_wf nm3 (Just Total) sg3 True
--   check_report_wf nm4 (Just Total) sg4 True
--   check_report_wf nm5 (Just Total) sg5 True
--   check_morphism (nm_m1 ++ ": " ++ nm2 ++ "->" ++ nm1 ++ " (Weak)") (Just WeakM) sg2 m1 sg1 True
--   check_morphism (nm_m2 ++ ": " ++ nm3 ++ "->" ++ nm1 ++ " (Weak)") (Just WeakM) sg3 m2 sg1 True
--   check_morphism (nm_m3 ++ ": " ++ nm3 ++ "->" ++ nm2 ++ " (Weak)") (Just WeakM) sg3 m3 sg2 True
--   check_morphism (nm_m4 ++ ": " ++ nm2 ++ "->" ++ nm3 ++ " (Weak)") (Just WeakM) sg2 m4 sg3 True
--   check_morphism (nm_m5 ++ ": " ++ nm4 ++ "->" ++ nm1 ++ " (Weak)") (Just WeakM) sg4 m5 sg1 True
--  check_morphism (nm_m6 ++ ": " ++ nm5 ++ "->" ++ nm1 ++ " (Weak)") (Just WeakM) sg5 m6 sg1 True
--   check_morphism ("Union of morphisms: " ++ nm4 ++ " U " ++ nm5 ++ "->" ++ nm1 ++ " (Weak)") (Just WeakM) (sg4 `union_sg` sg5) (m5 `union_gm` m6) sg1 True

--test_2 = do
--   (nm1, sg1)<-loadSG def_path "SG_Person_Vehicle_Other.sg"
--   (nm2, sg2)<-loadSG def_path "SG_Person_Vehicle_I.sg"
--   (nm3, sg3)<-loadSG def_path "SG_Employee_Car.sg"
--   (nm_m1, m1)<-loadM def_path "m_Employee_Car.gm"
--   (nm_m2, m2)<-loadM def_path "m_Employee_Car_Inv.gm"
--   (nm_m3, m3)<-loadM def_path "m_PVI_To_PV.gm"
--   (nm_m4, m4)<-loadM def_path "m_EC_To_PV.gm"
--   check_report_wf nm1 (Just Total) sg1 True
--   check_report_wf nm2 (Just Total) sg2 True
--   check_report_wf nm3 (Just Total) sg3 True
--   check_morphism (nm_m1 ++ " (Partial)") (Just PartialM) sg3 m1 sg2 True
--   check_morphism (nm_m1 ++ " (Total)") (Just TotalM) sg3 m1 sg2 False
--   check_morphism (nm_m2 ++ " (Total)") (Just TotalM) sg2 m2 sg3 True
--   check_morphism (nm_m3 ++ ": " ++ nm2 ++ "->" ++ nm1 ++ " (Total)") (Just TotalM) sg2 m3 sg1 True
--   check_morphism (nm_m4 ++ ": " ++ nm3 ++ "->" ++ nm1 ++ " (Total)") (Just TotalM) sg3 m4 sg1 True

-- Example used in PCs paper 
-- Morphisms from the two SGs of Fig. 6c into Fig. 6a
test2 :: IO ()
test2 = do
   (nm1, sg1)<-loadSG def_path "SG_PVO.sg"
   (nm2, sg2)<-loadSG def_path "SG_PGC.sg"
   (nm3, sg3)<-loadSG def_path "SG_PVI.sg"
   (nm_m1, m1)<-loadM def_path "m_PGC_PVO.gm"
   (nm_m2, m2)<-loadM def_path "m_PVI_PVO.gm"
   putStrLn "Test 2:"
   check_report_wf nm1 (Just Total) sg1 True
   check_report_wf nm2 (Just Partial) sg2 True
   check_report_wf nm3 (Just Partial) sg3 True
   check_morphism (nm_m1 ++ ": " ++ nm2 ++ "->" ++ nm1 ++ " (Weak, morphism)") (Just WeakM) sg2 m1 sg1 True
   check_morphism (nm_m2 ++ ": " ++ nm3 ++ "->" ++ nm1 ++ " (Weak, morphism)") (Just WeakM) sg3 m2 sg1 True
   check_morphism ("Union of morphisms: " ++ nm3 ++ " U " ++ nm2 ++ "->" ++ nm1 ++ " (Weak, morphism)") (Just WeakM) (sg2 `unionSG` sg3) (m1 `unionGM` m2) sg1 True
   check_morphism (nm_m1 ++ ": " ++ nm2 ++ "->" ++ nm1 ++ " (Partial, refinement)") (Just PartialM) sg2 m1 sg1 True
   check_morphism (nm_m2 ++ ": " ++ nm3 ++ "->" ++ nm1 ++ " (Partial, refinement)") (Just PartialM) sg3 m2 sg1 True
   check_morphism ("Union of morphisms: " ++ nm2 ++ " U " ++ nm3 ++ "->" ++ nm1 ++ " (Total, morphism)") (Just TotalM) (sg3 `unionSG` sg2) (m1 `unionGM` m2) sg1 True

--test_4 = do
--   (nm1, sg1)<-loadSG def_path "SG_Employee_Car.sg"
--   (nm2, sg2)<-loadSG def_path "SG_Person_Vehicle_I.sg"
--   (nm_m1, m1)<-loadM def_path "m_Employee_Car.gm"
--   (nm_m2, m2)<-loadM def_path "m_Employee_Car_Inv.gm"
--   check_report_wf nm1 (Just Total) sg1 True
--   check_report_wf nm2 (Just Total) sg2 True
--   check_morphism (nm_m1 ++ " (Partial)") (Just PartialM) sg1 m1 sg2 True
--   check_morphism (nm_m1 ++ " (Total)") (Just TotalM) sg1 m1 sg2 False
--   check_morphism (nm_m2 ++ " (Total)") (Just TotalM) sg2 m2 sg1 True

--test3 = do
--   (nm1, sg1)<-loadSG def_path "SG_Employee_Car.sg"
--   (nm2, sg2)<-loadSG def_path "SG_Person_Vehicle_Ib.sg"
--   (nm_m1, m1)<-loadM def_path "m_Employee_Car.gm"
--   (nm_m2, m2)<-loadM def_path "m_Employee_Car_Inv.gm"
--   (nm_m3, m3)<-loadM def_path "m_Employee_Carb.gm"
--   check_report_wf nm1 (Just Total) sg1 True
--   check_report_wf nm2 (Just Total) sg2 True
--   check_morphism (nm_m1 ++ " (Weak)") (Just WeakM) sg1 m1 sg2 True
--   check_morphism (nm_m1 ++ " (Partial)") (Just PartialM) sg1 m1 sg2 True
--   check_morphism (nm_m1 ++ " (Total)") (Just TotalM) sg1 m1 sg2 True
--   check_morphism (nm_m3 ++ " (Total)") (Just TotalM) sg1 m3 sg2 False
--   check_morphism (nm_m2 ++ " (Weak)") (Just WeakM) sg2 m2 sg1 True
--   check_morphism (nm_m2 ++ " (Total)") (Just TotalM) sg2 m2 sg1 True

--test_6 = do
--   (nm1, sg1)<-loadSG def_path "SG_Employee_Car.sg"
--   (nm2, sg2)<-loadSG def_path "SG_Person_Vehicle_Ic.sg"
--   (nm_m1, m1)<-loadM def_path "m_Employee_Car.gm"
--   (nm_m2, m2)<-loadM def_path "m_Employee_Carb.gm"
--   check_report_wf nm1 (Just Total) sg1 True
--   check_report_wf nm2 (Just Total) sg2 True
--   check_morphism (nm_m1 ++ ": " ++ nm1 ++ " -> " ++ nm2 ++ " (Weak)") (Just WeakM) sg1 m1 sg2 True
--   check_morphism (nm_m1 ++ ": " ++ nm1 ++ " -> " ++ nm2 ++ " (Partial)") (Just PartialM) sg1 m1 sg2 True
--   check_morphism (nm_m1 ++ ": " ++ nm1 ++ " -> " ++ nm2 ++ " (Total)") (Just TotalM) sg1 m1 sg2 False

test3 :: IO ()
test3 = do
   (nm1, sg1)<-loadSG def_path "SG_PVa.sg"
   (nm2, sg2)<-loadSG def_path "SG_PVIc.sg"
   (nm3, sg3)<-loadSG def_path "SG_EC.sg"
   (nm_m1, m1)<-loadM def_path "m_PVIc_PV.gm"
   (nm_m2, m2)<-loadM def_path "m_PVa_PVIc.gm"
   (nm_m3, m3)<-loadM def_path "m_PVa_EC.gm"
   putStrLn "Test 3:"
   check_report_wf nm1 (Just Total) sg1 True
   check_report_wf nm2 (Just Total) sg2 True
   check_morphism (nm_m1 ++ " (Total)") (Just TotalM) sg2 m1 sg1 True
   check_morphism (nm_m2 ++ " (Total)") (Just TotalM) sg1 m2 sg2 False
   check_morphism (nm_m3 ++ " (Weak)") (Just WeakM) sg1 m3 sg3 True
   check_morphism (nm_m3 ++ " (Partial)") (Just PartialM) sg1 m3 sg2 True
   check_morphism (nm_m3 ++ " (Total)") (Just TotalM) sg1 m3 sg3 True

do_main :: IO ()
do_main = do
   test1
   test1a
   test2
   test3
   --test_4
   --test_5
   --test_6
   --test_7

saveDrawings :: IO ()
saveDrawings = do
   draw_def def_path img_path "SG_PVO.sg"
   draw_def def_path img_path "SG_EC.sg"
   --draw_def def_path img_path "SG_PVIb.sg"
   --draw_def def_path img_path "SG_PVIc.sg"
   draw_def def_path img_path "SG_PVa.sg"
   draw_def def_path img_path "SG_PV.sg"
   draw_def def_path img_path "SG_PGC.sg"
   draw_def def_path img_path "SG_PVI.sg"
   draw_def def_path img_path "SG_PVIc.sg"

main :: IO ()
main = do
   option_main_save do_main saveDrawings
