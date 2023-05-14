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
import MyMaybe
import LoadCheckDraw
import Utils ( option_main_save )
import Gr_Cls

def_path = "FragmentaTests/SGTests/"
img_path = "FragmentaTests/SGTests/img/"


-- The wander example was modified because wander edges were taken out of the theory. 
-- Wander edges are expressed using the virtual node pattern
saveDrawings :: IO ()
saveDrawings = do
   draw_def def_path img_path "Wander_exmp.sg"
   draw_def def_path img_path "Simple_Exmp.sg"
   draw_def def_path img_path "Simple_Exmp2.sg"


test1 :: IO ()
test1 = do
   (nmw, sgw)<-loadSG def_path "Wander_Exmp.sg"
   (nm1, sg_c1)<-loadSG def_path "SG_EC.sg"
   (nm_m1, m1)<-loadM def_path "m_Wander_Exmp1.gm"
   check_report_wf nmw (Just Total) sgw True
   check_report_wf nm1 (Just Total) sg_c1 True
   check_morphism (nm_m1 ++ " WeakM") (Just WeakM) sg_c1 m1 sgw True
   check_morphism (nm_m1 ++ " TotalM") (Just TotalM) sg_c1 m1 sgw True

test2 :: IO ()
test2 = do
   (nms, sg_s)<-loadSG def_path "Simple_Exmp.sg"
   (nm1, sg_c1)<-loadSG def_path "SG_EC.sg"
   (nm_m1, m1)<-loadM def_path "m_Wander_Exmp2.gm"
   check_report_wf nms (Just Total) sg_s True
   check_report_wf nm1 (Just Total) sg_c1 True
   check_morphism nm_m1 (Just WeakM) sg_s m1 sg_c1 True

test3 :: IO ()
test3 = do
   (nmw, sgw)<-loadSG def_path "Wander_Exmp.sg"
   (nms, sgs)<-loadSG def_path "Simple_Exmp.sg"
   (nms2, sgs2)<-loadSG def_path "Simple_Exmp2.sg"
   (nm_m1, m1)<-loadM def_path "m_Wander_Exmp3.gm"
   (nm_m2, m2)<-loadM def_path "m_Wander_Exmp4.gm"
   check_report_wf nmw (Just Total) sgw True
   check_report_wf nms (Just Total) sgs True
   check_report_wf nms2 (Just Total) sgs2 True
   check_morphism (nm_m1 ++ " WeakM") (Just WeakM) sgs m1 sgw True
   check_morphism (nm_m1 ++ " TotalM") (Just TotalM) sgs m1 sgw True
   check_morphism (nm_m1 ++ " WeakM") (Just WeakM) sgs m1 sgw True
   check_morphism (nm_m1 ++ " TotalM") (Just TotalM) sgs m1 sgw True
   check_morphism (nm_m2 ++ " WeakM") (Just WeakM) sgs2 m2 sgw True
   check_morphism (nm_m2 ++ " TotalM") (Just TotalM) sgs2 m2 sgw True

do_main :: IO ()
do_main = do
   test1
   test2
   test3

main :: IO ()
main = do
   option_main_save do_main saveDrawings

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




