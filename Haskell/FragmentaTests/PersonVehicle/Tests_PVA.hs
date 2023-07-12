-------------------------
-- Project: PCs/Fragmenta
-- Module: 'Tests_PVA'
-- Description: Tests focused on example of PCs paper (Fragmenta/Fragments section), nodes Person, Vehicle, Any
-- Author: Nuno Amálio
--------------------------
import Gr_Cls
import Grs
import Frs
import Mdls
import Utils
import CheckUtils
import LoadCheckDraw

def_path :: String
def_path = "FragmentaTests/PersonVehicle/"
img_path :: String
img_path = "FragmentaTests/PersonVehicle/img/"

saveDrawings :: IO ()
saveDrawings= do
    draw_mdl def_path img_path "m_person_vehicle_any"
    draw_mdl def_path img_path "m_person_vehicle_inh"
    --(nm_f1, f1)<-load_fr_def def_path "F_PV.fr"
    --(nm_f2, f2)<-load_fr_def def_path "F_PVA.fr"
    --(nm_f3, f3)<-load_fr_def def_path "F_PVI.fr"
    --(nm_f4, f4)<-load_fr_def def_path "F_PC.fr"
    --(nm_f5, f5)<-load_fr_def def_path "F_V.fr"
    --(nm_f6, f6)<-load_fr_def def_path "F_ECC.fr"
    --saveFrDrawing img_path nm_f1 f1 
    --saveFrDrawing img_path nm_f2 f2 
    --let ufs = f1 `union_f` f2
    --saveFrDrawing img_path "UFs_PVA" ufs 
    --let rf = reso_f ufs
    --saveFrDrawing img_path "Rf_UFs_PVA" rf 
    --saveFrDrawing img_path nm_f3 f3 
    --saveFrDrawing img_path nm_f4 f4 
    --saveFrDrawing img_path nm_f5 f5 
    --saveFrDrawing img_path nm_f6 f6 
    --let ufs2 = f3 `union_f` (f4 `union_f` f5)
    --saveFrDrawing img_path "UFs_PVI" ufs2
    --let rf2 = reso_f ufs2
    --saveFrDrawing img_path "Rf_UFs_PVI" rf2
    draw_def def_path img_path "F_ECC.fr"
    draw_def def_path img_path "carlos_joana.gwt"
    draw_def def_path img_path "carlos_joana2.gwt"
    

test1 :: IO ()
test1 = do
    putStrLn "Test 1"
    mdl<-load_mdl_def def_path "m_person_vehicle_any"
    check_report_wf "M_PVA" (Just Total) mdl True
    check_report_wf "M_PVA_UF " (Just Total) (mufs mdl) True
    check_report_wf "◉ M_PVA" (Just Total) (reso_m mdl) True

test2 :: IO ()
test2 = do
    putStrLn "Test 2"
    mdl<-load_mdl_def def_path "m_person_vehicle_inh"
    check_report_wf "M_PVI" (Just Total) mdl True
    check_report_wf "M_PVI_UF " (Just Total) (mufs mdl) True
    check_report_wf "◉ M_PVI" (Just Total) (reso_m mdl) True

-- Checks that 'm1, m2, m3 and m4' mentioned in the paper are valid refinements
test3 :: IO ()
test3 = do
    putStrLn "Test 3"
    (nm_f1, f1)<-loadF def_path "F_PV.fr" -- Fig. 11a
    (nm_f2, f2)<-loadF def_path "F_PVA.fr"  -- Fig. 11a
    (nm_f3, f3)<-loadF def_path "F_PVI.fr" -- Fig. 11b
    (nm_f4, f4)<-loadF def_path "F_PC.fr" -- Fig. 11b
    (nm_f5, f5)<-loadF def_path "F_V.fr" -- Fig. 11b
    (nm_f6, f6)<-loadF def_path "F_ECC.fr" -- Fig. 11c
    (nm_m1, m1)<-loadM def_path "m_PVI_PV.gm"
    (nm_m2, m2)<-loadM def_path "m_PC_PVA.gm"
    (nm_m3, m3)<-loadM def_path "m_V_PVA.gm"
    (nm_m5, m5)<-loadM def_path "m_ECC_PVA.gm"
    check_report_wf nm_f1 (Just Partial) f1 True
    check_report_wf nm_f2 (Just Partial) f2 True
    check_report_wf nm_f3 (Just Partial) f3 True
    check_report_wf nm_f4 (Just Partial) f4 True
    check_report_wf nm_f5 (Just Partial) f5 True
    check_report_wf nm_f6 (Just Total) f6 True
    let uft = f1 `union_f` f2
    let ufs = f3 `union_f` (f4 `union_f` f5)
    check_report_wf "F_PV UF F_PVA" (Just Total) uft True -- Fig. 11a
    check_report_wf "F_PVI UF F_C UF F_C" (Just Total) ufs True -- Fig. 11b
    check_morphism ("(" ++ nm_f3 ++ ", " ++ nm_m1 ++ ") ⊒ " ++ nm_f1) (Just PartialM) f3 m1 f1 True
    check_morphism ("(" ++ nm_f3 ++ ", " ++ nm_m1 ++ ") ⊐ " ++ nm_f1) (Just TotalM) f3 m1 f1 True
    check_morphism ("(" ++ nm_f4 ++ ", " ++ nm_m2 ++ ") ⊒ " ++ nm_f2) (Just PartialM) f4 m2 f2 True
    check_morphism ("(" ++ nm_f5 ++ ", " ++ nm_m3 ++ ") ⊒ " ++ nm_f2) (Just PartialM) f5 m3 f2 True
    let m4 = m1 `unionGM` (m2 `unionGM` m3)
    check_morphism ("(" ++ nm_f3 ++ " U " ++ nm_f4 ++ " U " ++ nm_f5 ++ ", " ++ nm_m1 ++ " U " ++ nm_m2 ++ " U " ++ nm_m3 ++ ") ⊐ " ++ nm_f1 ++ " U " ++ nm_f2) (Just TotalM) ufs m4 uft True
    check_morphism ("(" ++ nm_f6 ++ ", " ++ nm_m5 ++ ") ⊐ " ++ nm_f1 ++ " U " ++ nm_f2) (Just TotalM) f6 m5 uft True

test4 :: IO ()
test4 = do
    putStrLn "Test 4"
    amdl<-load_mdl_def def_path "m_person_vehicle_any"
    cmdl<-load_mdl_def def_path "m_person_vehicle_inh"
    (nm_m1, m1)<-loadM def_path "m_PVI_PV.gm"
    (nm_m2, m2)<-loadM def_path "m_PC_PVA.gm"
    (nm_m3, m3)<-loadM def_path "m_V_PVA.gm"
    let m4 = m1 `unionGM` (m2 `unionGM` m3)
    check_morphism ("(M_PVA, " ++ nm_m1 ++ " U " ++ nm_m2 ++ " U " ++ nm_m3 ++ ") ⊐ M_PVI") (Just TotalM) cmdl m4 amdl True

test5 :: IO ()
test5 = do
    putStrLn "Test 5"
    (nm_f3, f3)<-loadF def_path "F_PVI.fr"
    (nm_f4, f4)<-loadF def_path "F_PC.fr"
    (nm_f6, f6)<-loadF def_path "F_ECC.fr"
    (nm_gwt1, gwt1) <- loadGwT def_path "carlos_joana.gwt" -- Fig. 12b
    check_ty_morphism (nm_gwt1 ++ " ⋑ " ++ nm_f3 ++ " U " ++ nm_f4) (Just TotalM) gwt1 (f3 `union_f` f4) True
    check_ty_morphism (nm_gwt1 ++ " ⋑ " ++ nm_f6) (Just TotalM) gwt1 f6 True

test6 :: IO ()
test6 = do
    putStrLn "Test 6"
    mdl<-load_mdl_def def_path "m_person_vehicle_inh"
    (nm_gwt, gwt) <- loadGwT def_path "carlos_joana2.gwt"
    check_report_wf "Model M_PVI" (Just Total) mdl True
    check_ty_morphism (nm_gwt ++ " ⋑ " ++  "M_PVI") (Just TotalM) gwt mdl True

do_main :: IO ()
do_main = do
    test1
    test2
    test3
    test4
    test5
    test6

main :: IO ()
main = do
   option_main_save do_main saveDrawings
