------------------
-- Project: PCs/Fragmenta
-- Module: 'SG_ref_tests'
-- Description: Tests which focus on SGs refinement
-- Author: Nuno Amálio
-----------------

{-# LANGUAGE UnicodeSyntax #-}

import SGrs
import Grs
import Utils
import CheckUtils
import Control.Monad(forM, forM_)
import LoadCheckDraw
import SimpleFuns

-- amm_1 = 
--    let ns' = ["A", "B", "B1", "B2"] in
--    let es' = ["IASelf", "IB1", "IB2", "EHasBs"] in
--    let s = [("IASelf", "A"), ("IB1", "B1"), ("IB2", "B2"), ("EHasBs", "A")] in
--    let t = [("IASelf", "A"), ("IB1", "B"), ("IB2", "B"), ("EHasBs", "B")] in
--    let nt = [("A", Nnrml), ("B", Nabst), ("B1", Nnrml), ("B2", Nnrml)] in
--    let et = [("IASelf", Einh), ("IB1", Einh), ("IB2", Einh), ("EHasBs", Erel Bi)] in
--    let sm = [("EHasBs", Sm Many)] in
--    let tm = [("EHasBs", Sm $ Val 1)] in
--    cons_sg (cons_g ns' es' s t) nt et sm tm

-- mm_1 = 
--    let ns' = ["A", "A1", "A2", "B", "B1", "B2"] in
--    let es' = ["IA1", "IA2",  "IB1", "IB2", "EHasBs1", "EHasBs2"] in
--    let s = [("IA1", "A1"), ("IA2", "A2"), ("IB1", "B1"), ("IB2", "B2"), ("EHasBs1", "A2"), ("EHasBs2", "A1")] in
--    let t = [("IA1", "A"), ("IA2", "A"), ("IB1", "B"), ("IB2", "B"), ("EHasBs1", "B1"), ("EHasBs2", "B2")] in
--    let nt =  [("A", Nabst), ("A1", Nnrml), ("A2", Nnrml), ("B", Nabst), ("B1", Nnrml), ("B2", Nnrml)] in
--    let et =  [("IA1", Einh), ("IA2", Einh),  ("IB1", Einh), ("IB2", Einh), ("EHasBs1", Erel Bi), ("EHasBs2", Erel Bi)] in
--    let sm = [("EHasBs1", Sm Many), ("EHasBs2", Sm Many)] in
--    let tm = [("EHasBs1", Sm $ Val 1), ("EHasBs2", Sm $ Val 1)] in
--    cons_sg (cons_g ns' es' s t) nt et sm tm

-- ty_morph_1 = 
--    let mv = [("A", "A"), ("A1", "A"), ("A2", "A"), ("B", "B"), ("B1", "B1"), ("B2", "B2")] in
--    let me = [("IA1", "IASelf"), ("IA2", "IASelf"), ("IB1", "IB1"), ("IB2", "IB2"), ("EHasBs1", "EHasBs"), ("EHasBs2", "EHasBs")] in
--    cons_gm mv me

-- mm_2 = 
--    let ns' = ["A", "A1", "A2", "B1", "B2"] in
--    let es' = ["IA1", "IA2",  "EHasBs1", "EHasBs2"] in
--    let s = [("IA1", "A1"), ("IA2", "A2"), ("EHasBs1", "A2"), ("EHasBs2", "A1")] in
--    let t = [("IA1", "A"), ("IA2", "A"), ("EHasBs1", "B1"), ("EHasBs2", "B2")] in
--    let nt =  [("A", Nabst), ("A1", Nnrml), ("A2", Nnrml), ("B1", Nnrml), ("B2", Nnrml)] in
--    let et = [("IA1", Einh), ("IA2", Einh),  ("EHasBs1", Erel Bi), ("EHasBs2", Erel Bi)] in
--    let sm = [("EHasBs1", Sm Many), ("EHasBs2", Sm Many)] in
--    let tm = [("EHasBs1", Sm $ Val 1), ("EHasBs2", Sm $ Val 1)] in
--    cons_sg (cons_g ns' es' s t) nt et sm tm

-- ty_morph_2 = 
--    let mv = [("A", "A"), ("A1", "A"), ("A2", "A"), ("B1", "B1"), ("B2", "B2")] in
--    let me = [("IA1", "IASelf"), ("IA2", "IASelf"), ("EHasBs1", "EHasBs"), ("EHasBs2", "EHasBs")] in
--    cons_gm mv me

-- mm_3 = 
--    let ns' = ["A", "A1", "A2", "A3", "B", "B1", "B2"] in
--    let es' = ["IA1", "IA2", "IA3", "IB1", "IB2", "EHasBs1", "EHasBs2"] in
--    let s = [("IA1", "A1"), ("IA2", "A2"), ("IA3", "A3"), ("IB1", "B1"), ("IB2", "B2"), ("EHasBs1", "A2"), ("EHasBs2", "A1")] in
--    let t = [("IA1", "A"), ("IA2", "A"), ("IA3", "A1"),  ("IB1", "B"), ("IB2", "B"), ("EHasBs1", "B1"), ("EHasBs2", "B2")] in
--    let nt =  [("A", Nabst), ("A1", Nnrml), ("A2", Nnrml), ("A3", Nnrml), ("B", Nabst), ("B1", Nnrml), ("B2", Nnrml)] in
--    let et =  [("IA1", Einh), ("IA2", Einh),  ("IA3", Einh),  ("IB1", Einh), ("IB2", Einh), ("EHasBs1", Erel Bi), ("EHasBs2", Erel Bi)] in
--    let sm = [("EHasBs1", Sm Many), ("EHasBs2", Sm Many)] in
--    let tm = [("EHasBs1", Sm $ Val 1), ("EHasBs2", Sm $ Val 1)] in
--    cons_sg (cons_g ns' es' s t) nt et sm tm

-- ty_morph_3 = 
--    let mv = [("A", "A"), ("A1", "A"), ("A2", "A"), ("A3", "A"), ("B", "B"), ("B1", "B1"), ("B2", "B2")]  in
--    let me = [("IA1", "IASelf"), ("IA2", "IASelf"), ("IA3", "IASelf"), ("IB1", "IB1"), ("IB2", "IB2"), ("EHasBs1", "EHasBs"), ("EHasBs2", "EHasBs")] in
--    cons_gm mv me

-- mm_4 = 
--    let ns' = ["A", "A1", "A2", "A3", "A4", "B", "B1", "B2"] in
--    let es' = ["IA1", "IA2", "IA3", "IA4", "IB1", "IB2", "EHasBs1", "EHasBs2"] in
--    let s = [("IA1", "A1"), ("IA2", "A2"), ("IA3", "A3"), ("IA4", "A4"), ("IB1", "B1"), ("IB2", "B2"), ("EHasBs1", "A2"), ("EHasBs2", "A1")] in
--    let t = [("IA1", "A"), ("IA2", "A"), ("IA3", "A1"),  ("IA4", "A"), ("IB1", "B"), ("IB2", "B"), ("EHasBs1", "B1"), ("EHasBs2", "B2")] in
--    let nt =  [("A", Nabst), ("A1", Nnrml), ("A2", Nnrml), ("A3", Nnrml), ("A4", Nnrml), ("B", Nabst), ("B1", Nnrml), ("B2", Nnrml)] in
--    let et =  [("IA1", Einh), ("IA2", Einh),  ("IA3", Einh), ("IA4", Einh), ("IB1", Einh), ("IB2", Einh), ("EHasBs1", Erel Bi), ("EHasBs2", Erel Bi)] in
--    let sm = [("EHasBs1", Sm Many), ("EHasBs2", Sm Many)] in
--    let tm = [("EHasBs1", Sm $ Val 1), ("EHasBs2", Sm $ Val 1)] in 
--    cons_sg (cons_g ns' es' s t) nt et sm tm

-- ty_morph_4 = 
--    let mv = [("A", "A"), ("A1", "A"), ("A2", "A"), ("A3", "A"), ("A4", "A"), ("B", "B"), ("B1", "B1"), ("B2", "B2")] in
--    let me = [("IA1", "IASelf"), ("IA2", "IASelf"), ("IA3", "IASelf"), ("IA4", "IASelf"), 
--              ("IB1", "IB1"), ("IB2", "IB2"), ("EHasBs1", "EHasBs"), ("EHasBs2", "EHasBs")] in
--    cons_gm mv me

-- amm_2 = 
--    let ns' = ["A", "B"] in
--    let es' = ["IASelf", "IBSelf", "EHasBs"] in
--    let s = [("IASelf", "A"), ("IBSelf", "B"), ("EHasBs", "A")] in
--    let t = [("IASelf", "A"), ("IBSelf", "B"), ("EHasBs", "B")] in
--    let nt =  [("A", Nnrml), ("B", Nnrml)] in
--    let et =  [("IASelf", Einh), ("IBSelf", Einh), ("EHasBs", Erel Bi)] in
--    let sm = [("EHasBs", Sm Many)] in 
--    let tm = [("EHasBs", Sm $ Val 1)] in
--    cons_sg (cons_g ns' es' s t) nt et sm tm

-- mm_5 = 
--    let ns' = ["A", "A1", "A2", "A3", "B1", "B2", "B1OrB2"] in
--    let es' = ["IA1", "IA2", "IA3", "EHasBs1", "EHasBs2", "EHasBs3", "IB1", "IB2"] in
--    let s = [("IA1", "A1"), ("IA2", "A2"), ("IA3", "A3"), ("IB1", "B1"), ("IB2", "B2"), ("EHasBs1", "A2"), ("EHasBs2", "A1"), ("EHasBs3", "A3")] in
--    let t = [("IA1", "A"), ("IA2", "A"), ("IA3", "A"), ("IB1", "B1OrB2"), ("IB2", "B1OrB2"), ("EHasBs1", "B1"), ("EHasBs2", "B2"), ("EHasBs3", "B1OrB2")] in
--    let nt =  [("A", Nabst), ("A1", Nnrml), ("A2", Nnrml), ("A3", Nnrml), ("B1", Nnrml), ("B2", Nnrml), ("B1OrB2", Nvirt)] in
--    let et =  [("IA1", Einh), ("IA2", Einh), ("IA3", Einh), ("IB1", Einh), ("IB2", Einh), ("EHasBs1", Erel Bi), ("EHasBs2", Erel Bi), ("EHasBs3", Erel Bi)] in
--    let sm = [("EHasBs1", Sm Many), ("EHasBs2", Sm Many), ("EHasBs3", Sm Many)] in
--    let tm = [("EHasBs1", Sm $ Val 1), ("EHasBs2", Sm $ Val 1), ("EHasBs3", Sm $ Val 1)] in
--    cons_sg (cons_g ns' es' s t) nt et sm tm

-- mm_6 = 
--    let ns' = ["A", "A1", "A2", "A3", "B1", "B2", "B1OrB2"] in
--    let es' = ["IA1", "IA2", "IA3", "EHasBs1", "EHasBs2", "EHasBs3", "IB1", "IB2"] in
--    let s = [("IA1", "A1"), ("IA2", "A2"), ("IA3", "A3"), ("IB1", "B1"), ("IB2", "B2"), ("EHasBs1", "A2"), ("EHasBs2", "A1"), ("EHasBs3", "A3")] in
--    let t = [("IA1", "A"), ("IA2", "A"), ("IA3", "A"), ("IB1", "B1OrB2"), ("IB2", "B1OrB2"), ("EHasBs1", "B1"), ("EHasBs2", "B2"), ("EHasBs3", "B1OrB2")] in
--    let nt = [("A", Nabst), ("A1", Nnrml), ("A2", Nnrml), ("A3", Nnrml), ("B1", Nnrml), ("B2", Nnrml), ("B1OrB2", Nvirt)] in
--    let et = [("IA1", Einh), ("IA2", Einh), ("IA3", Einh), ("IB1", Einh), ("IB2", Einh), ("EHasBs1", Erel Bi), ("EHasBs2", Erel Bi), ("EHasBs3", Erel Bi)] in
--    let sm = [("EHasBs1", Sm Many), ("EHasBs2", Sm $ Val 5), ("EHasBs3", Rm 0 $ Val 10)] in
--    let tm = [("EHasBs1", Sm $ Val 1), ("EHasBs2", Sm $ Val 1), ("EHasBs3", Sm $ Val 1)] in
--    cons_sg (cons_g ns' es' s t) nt et sm tm

-- ty_morph_5 = 
--    let mv = [("A", "A"), ("A1", "A"), ("A2", "A"), ("A3", "A"), ("B1", "B"), ("B2", "B"), ("B1OrB2", "B")] in
--    let me = [("IA1", "IASelf"), ("IA2", "IASelf"), ("IA3", "IASelf"),  ("IB1", "IBSelf"), ("IB2", "IBSelf"), ("EHasBs1", "EHasBs"), 
--             ("EHasBs2", "EHasBs"), ("EHasBs3", "EHasBs")] in
--    cons_gm mv me

-- amm_3 = 
--    let ns' = ["A", "B"] in
--    let es' = ["EHasBs"] in
--    let s = [("EHasBs", "A")] in
--    let t = [("EHasBs", "B")] in
--    let nt = [("A", Nnrml), ("B", Nnrml)] in
--    let et =  [("EHasBs", Erel Bi)] in
--    let sm = [("EHasBs", Sm Many)] in
--    let tm = [("EHasBs", Rm 0 $ Val 1)] in
--    cons_sg (cons_g ns' es' s t) nt et sm tm

-- mm_7 = 
--    let ns' = ["A", "B1", "B2"] in
--    let es' = ["EHasBs1"] in
--    let s = [("EHasBs1", "A")] in
--    let t = [("EHasBs1", "B1")] in
--    let nt =  [("A", Nnrml), ("B1", Nnrml), ("B2", Nnrml)] in
--    let et =  [("EHasBs1", Erel Bi)] in
--    let sm = [("EHasBs1", Sm Many)] in
--    let tm = [("EHasBs1", Sm $ Val 1)] in
--    cons_sg (cons_g ns' es' s t) nt et sm tm

-- ty_morph_6 = 
--    let mv = [("A", "A"), ("B1", "B"), ("B2", "B")] in
--    let me = [("EHasBs1", "EHasBs")] in
--    cons_gm mv me

-- amm_4 = 
--    let ns' = ["A", "B"] in
--    let es' = ["EHasBs"] in
--    let s = [("EHasBs", "A")] in
--    let t = [("EHasBs", "B")] in
--    let nt =  [("A", Nnrml), ("B", Nnrml)] in
--    let et =  [("EHasBs", Erel Bi)] in
--    let sm = [("EHasBs", Rm 1 Many)] in
--    let tm = [("EHasBs", Rm 0 $ Val 1)] in
--    cons_sg (cons_g ns' es' s t) nt et sm tm

-- amm_5 = 
--    let ns' = ["A", "B", "C", "BOrC"] in
--    let es' = ["IBIs", "ICIs", "EHasBsOrCs"] in
--    let s = [("IBIs", "B"), ("ICIs", "C"), ("EHasBsOrCs", "A")] in
--    let t = [("IBIs", "BOrC"), ("ICIs", "BOrC"), ("EHasBsOrCs", "BOrC")] in
--    let nt =  [("A", Nnrml), ("B", Nnrml), ("C", Nnrml), ("BOrC", Nvirt)] in
--    let et =  [("IBIs", Einh), ("ICIs", Einh), ("EHasBsOrCs", Erel Bi)] in
--    let sm = [("EHasBsOrCs", Sm $ Val 1)] in
--    let tm = [("EHasBsOrCs", Sm Many)] in
--    cons_sg (cons_g ns' es' s t) nt et sm tm

-- mm_8 = 
--    let ns' = ["A", "B", "C"] in
--    let es' = ["EHasBs", "EHasCs"] in
--    let s = [("EHasBs", "A"), ("EHasCs", "A")] in
--    let t = [("EHasBs", "B"), ("EHasCs", "C")] in
--    let nt =  [("A", Nnrml), ("B", Nnrml), ("C", Nnrml)] in
--    let et =  [("EHasBs", Erel Bi), ("EHasCs", Erel Bi)] in
--    let sm = [("EHasBs", Sm $ Val 1), ("EHasCs", Sm $ Val 1)] in
--    let tm = [("EHasBs", Sm Many), ("EHasCs", Sm Many)] in
--    cons_sg (cons_g ns' es' s t) nt et sm tm

-- ty_morph_7 = 
--    let mv = [("A", "A"), ("B", "B"), ("C", "C")] in
--    let me = [("EHasBs", "EHasBsOrCs"), ("EHasCs", "EHasBsOrCs")] in
--    cons_gm mv me

-- mm_9 = 
--    let ns' = ["A", "B", "C", "BOrC"] in
--    let es' = ["IBIs", "ICIs", "EHasBsOrCs"] in
--    let s = [("IBIs", "B"), ("ICIs", "C"), ("EHasBsOrCs", "A")] in
--    let t = [("IBIs", "BOrC"), ("ICIs", "BOrC"), ("EHasBsOrCs", "BOrC")] in
--    let nt =  [("A", Nnrml), ("B", Nnrml), ("C", Nnrml), ("BOrC", Nvirt)] in
--    let et =  [("IBIs", Einh), ("ICIs", Einh), ("EHasBsOrCs", Erel Bi)] in
--    let sm = [("EHasBsOrCs", Sm $ Val 1)] in
--    let tm = [("EHasBsOrCs", Rm 0 $ Val 1)] in
--    cons_sg (cons_g ns' es' s t) nt et sm tm

-- ty_morph_8 = 
--    let mv = [("A", "A"), ("B", "B"), ("C", "C"), ("BOrC", "BOrC")] in
--    let me = [("EHasBsOrCs", "EHasBsOrCs"), ("IBIs", "IBIs"), ("ICIs", "ICIs")] in
--    cons_gm mv me

-- mm_10 = 
--    let ns' = ["A", "B", "C", "BOrC"] in
--    let es' = ["IBIs", "ICIs", "EHasBsOrCs"] in
--    let s = [("IBIs", "B"), ("ICIs", "C"), ("EHasBsOrCs", "A")] in
--    let t = [("IBIs", "BOrC"), ("ICIs", "BOrC"), ("EHasBsOrCs", "BOrC")] in
--    let nt = [("A", Nnrml), ("B", Nnrml), ("C", Nnrml), ("BOrC", Nabst)] in
--    let et =  [("IBIs", Einh), ("ICIs", Einh), ("EHasBsOrCs", Erel Bi)] in
--    let sm = [("EHasBsOrCs", Sm $ Val 1)] in
--    let tm = [("EHasBsOrCs", Rm 0 $ Val 1)] in
--    cons_sg (cons_g ns' es' s t) nt et sm tm

def_path = "Tests/SGRefTests/"
img_path = "Tests/SGRefTests/img/"

saveDrawings = do
   forM_ [1..5] (\k->draw_def def_path img_path $ "amm_" ++ (show k) ++ ".sg")
   forM_ [1..10] (\k->draw_def def_path img_path $ "mm_" ++ (show k) ++ ".sg")

do_test1 = do
   (nm_amm_1, sg_amm_1)<-loadSG def_path "amm_1.sg"
   sgs<-forM [1..5] (\k->do 
         p<-load_sg_def def_path $ "mm_" ++ (show k) ++ ".sg"
         return p)
   ms<-forM [1..5] (\k->do 
         m<-load_morphism_def def_path $ "m_mm_" ++ (show k) ++ ".gm"
         return m)
   --(nm_mm_1, sg_mm_1)<-load_sg_def def_path "mm_1.sg"
   --(nm_mm_2, sg_mm_2)<-load_sg_def def_path "mm_2.sg"
   --(nm_mm_3, sg_mm_3)<-load_sg_def def_path "mm_3.sg"
   --(nm_mm_4, sg_mm_4)<-load_sg_def def_path "mm_4.sg"
   --(nm_mm_5, sg_mm_5)<-load_sg_def def_path "mm_5.sg"
   check_report_wf nm_amm_1 (Just Total) sg_amm_1 True
   forM_ sgs (\(nm, sg)->check_report_wf nm (Just Total) sg True)
   check_morphism (fst $ kth 0 ms) (Just TotalM) (snd $ kth 0 sgs) (snd $ kth 0 ms) sg_amm_1 True
   check_morphism (fst $ kth 1 ms) (Just PartialM) (snd $ kth 1 sgs) (snd $ kth 1 ms) sg_amm_1 True
   check_morphism (fst $ kth 1 ms) (Just TotalM) (snd $ kth 1 sgs) (snd $ kth 1 ms) sg_amm_1 False
   forM_ [2..4] (\k->check_morphism (fst $ kth k ms) (Just TotalM) (snd $ kth k sgs) (snd $ kth k ms) sg_amm_1 True)
   

do_test2 = do
   (nm_amm, sg_amm)<-load_sg_def def_path "amm_2.sg"
   (nm_mm_5, sg_mm_5)<-load_sg_def def_path "mm_5.sg"
   (nm_mm_6, sg_mm_6)<-load_sg_def def_path "mm_6.sg"
   (nm_m, m)<-load_morphism_def def_path $ "m_mm_5.gm"
   check_report_wf nm_amm (Just Total) sg_amm True
   check_report_wf nm_mm_5 (Just Total) sg_mm_5 True
   check_report_wf nm_mm_6 (Just Total) sg_mm_6 True
   check_morphism ("morphism " ++ nm_m ++ " with SG " ++ nm_mm_5) (Just TotalM) sg_mm_5 m sg_amm True
   check_morphism ("morphism " ++ nm_m ++ " with SG " ++ nm_mm_6) (Just TotalM) sg_mm_6 m sg_amm True

do_test3 = do
   (nm_amm1, sg_amm1)<-load_sg_def def_path "amm_3.sg"
   (nm_amm2, sg_amm2)<-load_sg_def def_path "amm_4.sg"
   (nm_mm_7, sg_mm_7)<-load_sg_def def_path "mm_7.sg"
   (nm_m, m)<-load_morphism_def def_path $ "m_mm_7.gm"
   check_report_wf nm_amm1 (Just Total) sg_amm1 True
   check_report_wf nm_amm2 (Just Total) sg_amm2 True
   check_report_wf nm_mm_7 (Just Total) sg_mm_7 True
   check_morphism ("morphism " ++ nm_m ++ " with SG " ++ nm_mm_7) (Just TotalM) sg_mm_7 m sg_amm1 True
   check_morphism ("morphism " ++ nm_m ++ " with SG " ++ nm_mm_7 ++ "(Weak)") (Just WeakM) sg_mm_7 m sg_amm2 True
   check_morphism ("morphism " ++ nm_m ++ " with SG " ++ nm_mm_7) (Just TotalM) sg_mm_7 m sg_amm2 False

do_test4 = do
   (nm_amm, sg_amm)<-load_sg_def def_path "amm_5.sg"
   (nm_mm_8, sg_mm_8)<-load_sg_def def_path "mm_8.sg"
   (nm_mm_9, sg_mm_9)<-load_sg_def def_path "mm_9.sg"
   (nm_mm_10, sg_mm_10)<-load_sg_def def_path "mm_10.sg"
   (nm_m8, m8)<-load_morphism_def def_path $ "m_mm_8.gm"
   (nm_m9, m9)<-load_morphism_def def_path $ "m_mm_9.gm"
   check_report_wf nm_amm (Just Total) sg_amm True
   check_report_wf nm_mm_8 (Just Total) sg_mm_8 True
   check_report_wf nm_mm_9 (Just Total) sg_mm_9 True
   check_report_wf nm_mm_10 (Just Total) sg_mm_10 True
   check_morphism ("morphism " ++ nm_m8 ++ " with SG " ++ nm_mm_8 ++ "(weak)") (Just WeakM) sg_mm_8 m8 sg_amm True
   check_morphism ("morphism " ++ nm_m8 ++ " with SG " ++ nm_mm_8 ++ "(total)") (Just TotalM) sg_mm_8 m8 sg_amm False
   check_morphism ("morphism " ++ nm_m9 ++ " with SG " ++ nm_mm_9) (Just TotalM) sg_mm_9 m9 sg_amm True
   check_morphism ("morphism " ++ nm_m9 ++ " with SG " ++ nm_mm_10) (Just TotalM) sg_mm_10 m9 sg_amm True

do_main = do
   do_test1
   do_test2
   do_test3
   do_test4

main = option_main_save do_main saveDrawings

-- main = do
--    check_report_wf "Abstract SG 1" (Just Total) amm_1 True
--    check_report_wf "Abstract SG 2" (Just Total) amm_2 True
--    check_report_wf "Abstract SG 3" (Just Total) amm_3 True
--    check_report_wf "Abstract SG 4" (Just Total) amm_4 True
--    check_report_wf "Abstract SG 5" (Just Total) amm_5 True
--    check_report_wf "Concrete SG 1" (Just Total) mm_1 True
--    check_report_wf "Concrete SG 2" (Just Total) mm_2 True
--    check_report_wf "Concrete SG 3" (Just Total) mm_3 True
--    check_report_wf "Concrete SG 4" (Just Total) mm_4 True
--    check_report_wf "Concrete SG 5" (Just Total) mm_5 True
--    check_report_wf "Concrete SG 6" (Just Total) mm_6 True
--    check_report_wf "Concrete SG 7" (Just Total) mm_7 True
--    check_report_wf "Concrete SG 8" (Just Total) mm_8 True
--    check_report_wf "Concrete SG 9" (Just Total) mm_9 True
--    check_report_wf "Concrete SG 10" (Just Total) mm_10 True
--    check_morphism "Morphism 1" WeakM ty_morph_1 mm_1 amm_1 True
--    check_morphism "Typing morphism 1" (FullM Total) ty_morph_1 mm_1 amm_1 True
--    check_morphism "Morphism 2" WeakM ty_morph_2 mm_2 amm_1 True
--    check_morphism "Typing morphism 2" (FullM Total) ty_morph_2 mm_2 amm_1 True
--    check_morphism "Morphism 3" WeakM ty_morph_3 mm_3 amm_1 True
--    check_morphism "Typing morphism 3" (FullM Total) ty_morph_3 mm_3 amm_1 True
--    check_morphism "Morphism 4" WeakM ty_morph_4 mm_4 amm_1 True
--    check_morphism "Typing morphism 4" (FullM Total) ty_morph_4 mm_4 amm_1 False
--    check_morphism "Morphism 5" WeakM ty_morph_5 mm_5 amm_2 True
--    check_morphism "Typing morphism 5" (FullM Total) ty_morph_5 mm_5 amm_2 True
--    check_morphism "Morphism 6" WeakM ty_morph_5 mm_6 amm_2 True
--    check_morphism "Typing morphism 6" (FullM Total) ty_morph_5 mm_6 amm_2 True
--    check_morphism "Morphism 7" WeakM ty_morph_6 mm_7 amm_3 True
--    check_morphism "Typing morphism 7" (FullM Total) ty_morph_6 mm_7 amm_3 True
--    check_morphism "Morphism 8" WeakM ty_morph_6 mm_7 amm_4 True
--    check_morphism "Typing morphism 8" (FullM Total) ty_morph_6 mm_7 amm_4 False
--    check_morphism "Morphism 9" WeakM ty_morph_7 mm_8 amm_5 True
--    check_morphism "Typing morphism 9" (FullM Total) ty_morph_7 mm_8 amm_5 True
--    check_morphism "Morphism 10" WeakM ty_morph_8 mm_9 amm_5 True
--    check_morphism "Typing morphism 10" (FullM Total) ty_morph_8 mm_9 amm_5 True
--    check_morphism "Morphism 11" WeakM ty_morph_8 mm_10 amm_5 True
--    check_morphism "Typing morphism 11" (FullM Total) ty_morph_8 mm_10 amm_5 False

-- saveGraphs = do
--    saveSGDrawing "AMM1_Test" amm_1 True
--    saveSGDrawing "AMM2_Test" amm_2 True
--    saveSGDrawing "AMM3_Test" amm_3 True
--    saveSGDrawing "MM1_Test" mm_1 True
--    saveSGDrawing "MM2_Test" mm_2 True
--    saveSGDrawing "MM3_Test" mm_3 True
--    saveSGDrawing "MM4_Test" mm_4 True
--    saveSGDrawing "MM5_Test" mm_5 True