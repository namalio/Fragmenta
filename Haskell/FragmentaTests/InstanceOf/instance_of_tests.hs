-------------------------
-- Project: PCs/Fragmenta
-- Module: 'Intance_tests'
-- Description: Test focused on SGs and the instance of relation
-- Author: Nuno Amálio
-------------------------
import Gr_Cls
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
import GrswT
import Relations
import Sets

def_path = "FragmentaTests/InstanceOf/"
img_path = "FragmentaTests/InstanceOf/img/"

-- This example checks the commmuting through graph commuting.
do_test1 = do
   (nm1, sg1)<-load_sg_def def_path "SG_Block_Port.sg"
   (nm2, sg2)<-load_sg_def def_path "SG_Block_Conf.sg"
   (nm_g1, gwt1)<-load_gwt_def def_path "G_Blocks_I1.gwt"
   (nm_g2, gwt2)<-load_gwt_def def_path "G_Conf_I1.gwt"
   (nm_g3, gwt3)<-load_gwt_def def_path "G_Conf_I2.gwt"
   (nm_m1, m1)<-load_morphism_def def_path "m_Conf_Blocks_I1.gm"
   (nm_m2, m2)<-load_morphism_def def_path "m_Conf_Blocks_I2.gm"
   check_report_wf nm1 (Just Total) sg1 True
   check_report_wf nm2 (Just Total) sg2 True
   check_report_wf nm2 (Just Total) sg2 True
   check_report_wf nm_g1 (Just Total) gwt1 True
   check_report_wf nm_g2 (Just Total) gwt2 True
   check_report_wf nm_g3 (Just Total) gwt3 True
   check_ty_morphism (nm_g1 ++ " (Weak)") (Just WeakM) gwt1 sg1 True
   check_ty_morphism (nm_g1 ++ " (Total)") (Just TotalM) gwt1 sg1 True
   check_ty_morphism (nm_g2 ++ " (Weak)") (Just WeakM) gwt2 sg2 True
   check_ty_morphism (nm_g2 ++ " (Total)") (Just TotalM) gwt2 sg2 True
   check_ty_morphism (nm_g3 ++ " (Weak)") (Just WeakM) gwt3 sg2 True
   check_ty_morphism (nm_g3 ++ " (Total)") (Just TotalM) gwt3 sg2 True
   --putStrLn (show $ dom_of . fV $ m1)
   --putStrLn (show $ restrictNs (gOf gwt2) (dom_of . fV $ m1) )
   check_morphism (nm_m1 ++ ": " ++ nm_g2 ++ " -> " ++ nm_g1) Nothing (restrictNs (gOf gwt2) (dom_of . fV $ m1)) m1 (gOf gwt1) True
   check_morphism (nm_m2 ++ ": " ++ nm_g3 ++ " -> " ++ nm_g1) Nothing (restrictNs (gOf gwt3) (dom_of . fV $ m2)) m2 (gOf gwt1) False

consRelFrEdge gwt e = foldr (\e r->(appl (src gwt) e, appl (tgt gwt) e):r) [] (es_of_ety gwt e)

check_rel_commuting r1 r2 = r1 `seteq` r2 

resMsg b = if b then "Ok" else "Fail"

do_test2 = do
   (nm1, sg1)<-load_sg_def def_path "SG_Block_And_Conf.sg"
   (nm_g1, gwt1)<-load_gwt_def def_path "G_Blocks_Conf_I1.gwt"
   check_report_wf nm1 (Just Total) sg1 True
   check_report_wf nm_g1 (Just Total) gwt1 True
   check_ty_morphism (nm_g1 ++ " (Weak)") (Just WeakM) gwt1 sg1 True
   check_ty_morphism (nm_g1 ++ " (Total)") (Just TotalM) gwt1 sg1 True
   let r_bli_ports = consRelFrEdge gwt1 "EBlockI_ports"
   let r_pi_instOf = consRelFrEdge gwt1 "EPortI_instOf"
   let r_bli_instOf = consRelFrEdge gwt1 "EBlockI_instOf"
   let r_bl_ports = consRelFrEdge gwt1 "EBlock_ports"
   let b = check_rel_commuting (r_bli_ports  `rcomp` r_pi_instOf) (r_bli_instOf  `rcomp` r_bl_ports) 
   --putStrLn . show $ (r_bli_ports  `rcomp` r_pi_instOf)
   putStrLn $ "Commuting " ++ (evalExpectation b True)
   --putStrLn $ "The relation " ++ check_rel_commuting (r_bli_ports  `rcomp` r_pi_instOf) (r_bli_instOf  `rcomp` r_bl_ports) 

do_test3 = do
   (nm1, sg1)<-load_sg_def def_path "SG_Block_Conf_Ty.sg"
   (nm_g1, gwt1)<-load_gwt_def def_path "G_Blocks_Conf_Ty_I1.gwt"
   check_report_wf nm1 (Just Total) sg1 True
   check_report_wf nm_g1 (Just Total) gwt1 True
   check_ty_morphism (nm_g1 ++ " (Weak)") (Just WeakM) gwt1 sg1 True
   check_ty_morphism (nm_g1 ++ " (Total)") (Just TotalM) gwt1 sg1 True
   let r_c_ty = consRelFrEdge gwt1 "EConnector_type"
   let r_c_src = consRelFrEdge gwt1 "EConnector_src"
   let r_c_tgt = consRelFrEdge gwt1 "EConnector_tgt"
   let r_pi_inst = consRelFrEdge gwt1 "EPortI_instOf"
   let r_p_ty =consRelFrEdge gwt1 "EPort_type"
   let c1 = check_rel_commuting (r_c_src  `rcomp` (r_pi_inst `rcomp` r_p_ty)) (r_c_ty) 
   let c2 = check_rel_commuting (r_c_tgt  `rcomp` (r_pi_inst `rcomp` r_p_ty)) (r_c_ty) 
   putStrLn $ "Commuting " ++ (resMsg c1) ++ " " ++ (evalExpectation c1 True)
   putStrLn $ "Commuting " ++ (resMsg c2) ++ " " ++ (evalExpectation c2 True)

do_test4 = do -- continue here
   (nm1, sg1)<-load_sg_def def_path "SG_PetRoom.sg"
   (nm_g1, gwt1)<-load_gwt_def def_path "G_PetRoom_I1.gwt"
   (nm_g2, gwt2)<-load_gwt_def def_path "G_PetRoom_I2.gwt"
   check_report_wf nm1 (Just Total) sg1 True
   check_report_wf nm_g1 (Just Total) gwt1 True
   check_report_wf nm_g2 (Just Total) gwt2 True
   check_ty_morphism (nm_g1 ++ " (Weak)") (Just WeakM) gwt1 sg1 True
   check_ty_morphism (nm_g1 ++ " (Total)") (Just TotalM) gwt1 sg1 True
   check_ty_morphism (nm_g2 ++ " (Total)") (Just TotalM) gwt2 sg1 True
   let r_hosts gwt = consRelFrEdge gwt "EHosts"
   let r_tied_to gwt = consRelFrEdge gwt "ETiedTo"
   let r_pr_kind gwt = consRelFrEdge gwt "EPetRoom_kind"
   let c gwt = check_rel_commuting (r_hosts gwt  `rcomp` r_tied_to gwt) (r_pr_kind gwt) 
   putStrLn $ "Commuting of " ++ nm_g1 ++ " " ++ (resMsg . c $ gwt1) ++ " " ++ (evalExpectation (c gwt1) True)
   putStrLn $ "Commuting of " ++ nm_g2 ++ " " ++ (resMsg . c $ gwt2) ++ " " ++ (evalExpectation (c gwt2) False)

do_test4a = do -- continue here
   (nm1, sg1)<-load_sg_def def_path "SG_PetRoom.sg"
   (nm_g1, gwt1)<-load_gwt_def def_path "G_PetRoom_I3.gwt"
   check_report_wf nm1 (Just Total) sg1 True
   check_report_wf nm_g1 (Just Total) gwt1 True
   check_ty_morphism (nm_g1 ++ " (Weak)") (Just WeakM) gwt1 sg1 True
   check_ty_morphism (nm_g1 ++ " (Total)") (Just TotalM) gwt1 sg1 False



--The first morphism should not be a refinement morphism because the concrete model (in that case SG_1) looses things out.
do_main = do
   do_test1
   do_test2
   do_test3
   do_test4
   do_test4a
   --do_test_5
   --do_test_6
   --do_test_7

saveDrawings = do
   draw_def def_path img_path "SG_Block_Port.sg"
   draw_def def_path img_path "SG_Block_Conf.sg"
   draw_def def_path img_path "SG_Block_And_Conf.sg"
   draw_def def_path img_path "SG_Block_Conf_Ty.sg"
   draw_def def_path img_path "SG_PetRoom.sg"
   draw_def def_path img_path "G_Blocks_I1.gwt"
   draw_def def_path img_path "G_Conf_I1.gwt"
   draw_def def_path img_path "G_Conf_I2.gwt"
   draw_def def_path img_path "G_Blocks_Conf_I1.gwt"
   draw_def def_path img_path "G_PetRoom_I1.gwt"
   draw_def def_path img_path "G_PetRoom_I2.gwt"
   draw_def def_path img_path "G_PetRoom_I3.gwt"

main = do
   option_main_save do_main saveDrawings

