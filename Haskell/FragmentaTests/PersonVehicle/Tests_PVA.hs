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

def_path = "FragmentaTests/PersonVehicle/"
img_path = "FragmentaTests/PersonVehicle/img/"

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
    draw_def def_path img_path "carlos_joana3.gwt"
    

do_test_1 = do
    mdl<-load_mdl_def def_path "m_person_vehicle_any"
    check_report_wf "M_PVA" (Just Total) mdl True
    check_report_wf "M_PVA_UF " (Just Total) (mufs mdl) True
    check_report_wf "◉ M_PVA" (Just Total) (reso_m mdl) True

do_test_2 = do
    mdl<-load_mdl_def def_path "m_person_vehicle_inh"
    check_report_wf "M_PVI" (Just Total) mdl True
    check_report_wf "M_PVI_UF " (Just Total) (mufs mdl) True
    check_report_wf "◉ M_PVI" (Just Total) (reso_m mdl) True

do_test_3 = do
    (nm_f6, f6)<-load_fr_def def_path "F_ECC.fr"
    check_report_wf nm_f6 (Just Total) f6 True

-- Checks that 'm1, m2, m3 and m4' mentioned in the paper are valid refinements
do_test_4 = do
    (nm_f1, f1)<-load_fr_def def_path "F_PV.fr"
    (nm_f2, f2)<-load_fr_def def_path "F_PVA.fr"
    (nm_f3, f3)<-load_fr_def def_path "F_PVI.fr"
    (nm_f4, f4)<-load_fr_def def_path "F_PC.fr"
    (nm_f5, f5)<-load_fr_def def_path "F_V.fr"
    (nm_f6, f6)<-load_fr_def def_path "F_ECC.fr"
    (nm_m1, m1)<-load_morphism_def def_path "m_PVI_PV.gm"
    (nm_m2, m2)<-load_morphism_def def_path "m_PC_PVA.gm"
    (nm_m3, m3)<-load_morphism_def def_path "m_V_PVA.gm"
    (nm_m5, m5)<-load_morphism_def def_path "m_ECC_PVA.gm"
    check_morphism (nm_m1 ++ " morphism (Partial)") (Just PartialM) f3 m1 f1 True
    check_morphism (nm_m2 ++ " morphism (Partial)") (Just PartialM) f4 m2 f2 True
    check_morphism (nm_m3 ++ " morphism (Partial)") (Just PartialM) f5 m3 f2 True
    let m4 = m1 `union_gm` (m2 `union_gm` m3)
    let uft = f1 `union_f` f2
    let ufs = f3 `union_f` (f4 `union_f` f5)
    check_morphism (nm_m1 ++ " U " ++ nm_m2 ++ " U " ++ nm_m3 ++ " morphism (Total)") (Just TotalM) ufs m4 uft True
    check_morphism (nm_m5 ++ " morphism (Total)") (Just TotalM) f6 m5 uft True

do_test_5 = do
    amdl<-load_mdl_def def_path "m_person_vehicle_any"
    cmdl<-load_mdl_def def_path "m_person_vehicle_inh"
    (nm_m1, m1)<-load_morphism_def def_path "m_PVI_PV.gm"
    (nm_m2, m2)<-load_morphism_def def_path "m_PC_PVA.gm"
    (nm_m3, m3)<-load_morphism_def def_path "m_V_PVA.gm"
    let m4 = m1 `union_gm` (m2 `union_gm` m3)
    check_morphism ("Refinement of M_PVA by M_PVI") (Just TotalM) cmdl m4 amdl True

do_test_6 = do
    (nm_f3, f3)<-load_fr_def def_path "F_PVI.fr"
    (nm_f4, f4)<-load_fr_def def_path "F_PC.fr"
    (nm_f6, f6)<-load_fr_def def_path "F_ECC.fr"
    (nm_gwt1, gwt1) <- load_gwt_def def_path "carlos_joana.gwt"
    (nm_gwt2, gwt2) <- load_gwt_def def_path "carlos_joana2.gwt"
    check_ty_morphism (nm_gwt1 ++ " typing morphism (Strong)") (Just TotalM) gwt1 (f3 `union_f` f4) True
    check_ty_morphism (nm_gwt2 ++ " typing morphism (Strong)") (Just TotalM) gwt2 f6 True

do_test_7 = do
    mdl<-load_mdl_def def_path "m_person_vehicle_inh"
    (nm_gwt, gwt) <- load_gwt_def def_path "carlos_joana3.gwt"
    check_report_wf "M_PVI" (Just Total) mdl True
    check_ty_morphism (nm_gwt ++ " typing morphism (Strong)") (Just TotalM) gwt mdl True

do_main = do
    do_test_1
    do_test_2
    do_test_3
    do_test_4
    do_test_5
    do_test_6
    do_test_7

main = do
   option_main_save do_main saveDrawings
