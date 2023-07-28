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
import Relations


def_path = "FragmentaTests/SGTests/"
img_path = "FragmentaTests/SGTests/img/"


-- The wander example was modified because wander edges were taken out of the theory. 
-- Wander edges are expressed using the virtual node pattern
saveDrawings :: IO ()
saveDrawings = do
   draw_def def_path img_path "Wander_exmp.sg"
   draw_def def_path img_path "Wander_exmp2.sg"
   draw_def def_path img_path "Wander_exmp3.sg"
   draw_def def_path img_path "Wander_exmp4.sg"
   draw_def def_path img_path "Simple_Exmp.sg"
   draw_def def_path img_path "Simple_Exmp2.sg"
   draw_def def_path img_path "Simple_Exmp3.sg"
   draw_def def_path img_path "Flex_Exmp.sg"
   draw_def def_path img_path "SEs.sg"
   draw_def def_path img_path "IEs.sg"


test1 :: IO ()
test1 = do
   putStrLn "Test 1"
   (nmw, sgw)<-loadSG def_path "Wander_Exmp.sg"
   (nm1, sg_c1)<-loadSG def_path "SG_EC.sg"
   (nm_m1, m1)<-loadM def_path "m_Wander_Exmp1.gm"
   check_report_wf nmw (Just Total) sgw True
   check_report_wf nm1 (Just Total) sg_c1 True
   check_morphism ("("++nm1 ++ ", " ++ nm_m1 ++ ") ⊒ " ++ nmw) (Just WeakM) sg_c1 m1 sgw True
   check_morphism ("("++nm1 ++ ", " ++ nm_m1 ++ ") ⊐ " ++ nmw) (Just TotalM) sg_c1 m1 sgw True
   

test2 :: IO ()
test2 = do
   putStrLn "Test 2"
   (nms, sg_s)<-loadSG def_path "Simple_Exmp.sg"
   (nm1, sg_c1)<-loadSG def_path "SG_EC.sg"
   (nm_m1, m1)<-loadM def_path "m_Wander_Exmp2.gm"
   check_report_wf nms (Just Total) sg_s True
   check_report_wf nm1 (Just Total) sg_c1 True
   check_morphism ("("++nms ++ ", " ++ nm_m1 ++ ") ⊒ " ++ nm1)  (Just WeakM) sg_s m1 sg_c1 True

test3 :: IO ()
test3 = do
   putStrLn "Test 3"
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
   check_morphism ("("++nms ++ ", " ++ nm_m1 ++ ") ⊒ " ++ nmw) (Just PartialM) sgs m1 sgw True
   check_morphism ("("++nms ++ ", " ++ nm_m1 ++ ") ⊐ " ++ nmw) (Just TotalM) sgs m1 sgw True
   check_morphism ("("++nms2 ++ ", " ++ nm_m2 ++ ") ⊒ " ++ nmw) (Just PartialM) sgs2 m2 sgw False
   --check_morphism ("("++nms2 ++ ", " ++ nm_m2 ++ ") ⊐ " ++ nmw)  (Just TotalM) sgs2 m2 sgw False
   --putStrLn $ show (appl ((srcma sgw) `bcomp` (fE m1)) "EOwns")
   --putStrLn $ show (appl (srcma sg_c1) "EOwns")
   --putStrLn $ "Constraint edges: " ++ (show (esCnt sgw))
   --putStrLn $ "Source multiplicity of 'ESRNAA': " ++ show (appl (srcma sgw) "ESRNAA")
   --putStrLn $ "Start edge of 'ESRNAA': " ++ show (startEdg (appl (pe sgw) "ESRNAA"))
   --putStrLn $ "Instances of Start edge of 'ESRNAA' in concrete model: " ++ show (img (inv . fE $ m2) [ePEA $ (startEdg (appl (pe sgw) "ESRNAA"))])
   --putStrLn $ "Instances of end edge of 'ESRNAA' in concrete model: " ++ show (img (inv . fE $ m2) [ePEA $ (endEdg (appl (pe sgw) "ESRNAA"))])
   --putStrLn $ show (appl (fV m2) (appl (src sgs2) "ESomeRel2"))
   --putStrLn $ show (appl (src sgw) "ESRNAA")
   --putStrLn $ show (appl (fV m2) (appl (tgt sgs2) "ESomeRel2"))
   --putStrLn $ show (appl (tgt sgw) "ESRNAA")
   --putStrLn $ show (appl (srcma sgw) "ESRNAA")
   --putStrLn $ show (ok_src_nodes sgs2 m2 sgw "ESRNAA" "ESomeRel2")
   --putStrLn $ show (ok_tgt_nodes sgs2 m2 sgw "ESRNAA" "ESomeRel2")
   --putStrLn $ show (ok_src_nodes sgs2 m2 sgw "ESRNAA" "ESomeRel")
   --putStrLn $ show (ok_tgt_nodes sgs2 m2 sgw "ESRNAA" "ESomeRel")
   --putStrLn $ show (src_m_ok sgs2 m2 sgw "ESRNAA" "ESomeRel2")
   --putStrLn $ show (tgt_m_ok sgs2 m2 sgw "ESRNAA" "ESomeRel2")

test4 :: IO ()
test4 = do
   putStrLn "Test 4"
   (nmw, sgw)<-loadSG def_path "Wander_Exmp2.sg"
   (nmw2, sgw2)<-loadSG def_path "Wander_Exmp3.sg"
   (nmw3, sgw3)<-loadSG def_path "Wander_Exmp4.sg"
   (nms, sgs)<-loadSG def_path "Simple_Exmp3.sg"
   (nm_m, m)<-loadM def_path "m_Wander_Exmp5.gm"
   check_report_wf nmw (Just Total) sgw True
   check_report_wf nmw2 (Just Total) sgw2 True
   check_report_wf nms (Just Total) sgs True
   check_morphism  ("("++nms ++ ", " ++ nm_m ++ ") ⇛ " ++ nmw2) (Just WeakM) sgs m sgw True
   check_morphism  ("("++nms ++ ", " ++ nm_m ++ ") ⊒ " ++ nmw2) (Just PartialM) sgs m sgw False
   --check_morphism ("("++nms ++ ", " ++ nm_m ++ ") ⊐ " ++ nmw) (Just TotalM) sgs m sgw False
   check_morphism ("("++nms ++ ", " ++ nm_m ++ ") ⊒ " ++ nmw2) (Just PartialM) sgs m sgw2 True
   check_morphism ("("++nms ++ ", " ++ nm_m ++ ") ⊐ " ++ nmw2) (Just TotalM) sgs m sgw2 True
   check_morphism ("("++nms ++ ", " ++ nm_m ++ ") ⇛ " ++ nmw3) (Just WeakM) sgs m sgw3 True
   check_morphism ("("++nms ++ ", " ++ nm_m ++ ") ⊒ " ++ nmw3) (Just PartialM) sgs m sgw3 False
   

test5 :: IO ()
test5 = do
   putStrLn "Test 5: Test used in paper"
   (nmf, sgf)<-loadSG def_path "Flex_Exmp.sg"
   (nm_ses, sg_ses)<-loadSG def_path "SEs.sg"
   (nm_ies, sg_ies)<-loadSG def_path "IEs.sg"
   (nm_m, m)<-loadM def_path "m_SEs.gm"
   (nm_mie, mie)<-loadM def_path "m_IEs.gm"
   check_report_wf nmf (Just Total) sgf True
   check_report_wf nm_ses (Just Total) sg_ses True
   check_report_wf nm_ies (Just Total) sg_ies True
   check_morphism  ("("++nm_ses ++ ", " ++ nm_m ++ ") ⊒ " ++ nmf) (Just PartialM) sg_ses m sgf True
   check_morphism  ("("++nm_ses ++ ", " ++ nm_m ++ ") ⊐ " ++ nmf) (Just TotalM) sg_ses m sgf True
   check_morphism  ("("++nm_ies ++ ", " ++ nm_mie ++ ") ⇛ " ++ nmf) (Just WeakM) sg_ies mie sgf True
   check_morphism  ("("++nm_ies ++ ", " ++ nm_mie ++ ") ⊒ " ++ nmf) (Just PartialM) sg_ies mie sgf False
   

do_main :: IO ()
do_main = do
   test1
   test2
   test3
   test4
   test5

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




