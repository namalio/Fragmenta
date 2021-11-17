------------------
-- Project: PCs/Fragmenta
-- Module: 'Sg_ty_tests'
-- Description: Test which focus on SGs and SG refinement
-- Author: Nuno Amálio
-----------------
import SGrs
import Grs
import CheckUtils
import System.Environment
import Control.Monad(when)
import FrParsing
import MyMaybe
import LoadCheckDraw
import Utils

def_path = "Tests/SGTests/"
img_path = "Tests/SGTests/img/"

saveGraphs = do
   draw_def def_path img_path "Wander_exmp.sg"
   draw_def def_path img_path "Simple_Exmp.sg"


do_test1 = do
   (nmw, sgw)<-load_sg_def def_path "Wander_Exmp.sg"
   (nm1, sg_c1)<-load_sg_def def_path "SG_Employee_Car.sg"
   (nm_m1, m1)<-load_morphism_def def_path "m_Wander_Exmp1.gm"
   check_report_wf nmw (Just Total) sgw True
   check_report_wf nm1 (Just Total) sg_c1 True
   check_morphism nm_m1 (Just WeakM) sg_c1 m1 sgw True
   check_morphism nm_m1 (Just TotalM) sg_c1 m1 sgw True

do_test2 = do
   (nms, sg_s)<-load_sg_def def_path "Simple_Exmp.sg"
   (nm1, sg_c1)<-load_sg_def def_path "SG_Employee_Car.sg"
   (nm_m1, m1)<-load_morphism_def def_path "m_Wander_Exmp2.gm"
   check_report_wf nms (Just Total) sg_s True
   check_report_wf nm1 (Just Total) sg_c1 True
   check_morphism nm_m1 (Just WeakM) sg_s m1 sg_c1 True

do_main = do
   do_test1
   do_test2

main = do
   option_main_save do_main saveGraphs

--do_test3 = do
--   osg_w<-loadSG "Tests/Wander_Exmp.sg"
--   osg_c1<-loadSG "Tests/SG_Employee_Car.sg"
--   om1<-loadMorphism "Tests/m_Wander_Exmp2.gm"
--   when (all isSomething [osg_w, osg_c1] && isSomething om1) $ do
--      let (Just (nms, sg_w)) = osg_w
--      let (Just (nm1, sg_c1)) = osg_c1
--      let (Just (nm_m1, m1)) = om1
--      check_report_wf nms (Just Total) sg_w True
--      check_report_wf nm1 (Just Total) sg_c1 True
--      check_morphism nm_m1 (WeakM) m1 sg_w sg_c1 True
--      check_morphism nm_m1 (FullM Total) m1 sg_w sg_c1 True
      --saveSGDrawing nmw sgw

--do_test4 = do
--   osg_w<-loadSG "Tests/Wander_Exmp.sg"
--   osg_c1<-loadSG "Tests/SG_Employee_Car.sg"
--  om1<-loadMorphism "Tests/m_Wander_Exmp2.gm"
--   when (all isSomething [osg_w, osg_c1] && isSomething om1) $ do
--      let (Just (nms, sg_w)) = osg_w
--      let (Just (nm1, sg_c1)) = osg_c1
--      let (Just (nm_m1, m1)) = om1
      --check_report_wf nms (Just Total) sg_w True
      --check_morphism nm_m1 (WeakM) m1 sg_w sg_c1 True
--      let b = is_wf_gm_sgs (m1, sg_w, sg_c1)
--      if b 
--         then putStrLn "The morphism is valid"
--         else putStrLn "The morphism is invalid"




