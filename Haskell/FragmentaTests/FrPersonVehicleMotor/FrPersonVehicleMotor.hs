--------------------------
-- Project: PCs/Fragmenta
-- Module: 'SGTest2'
-- Description: Batch of tests exercising features of SGs and SG refinement
-- Author: Nuno Amálio
---------------------------
import SGrs
import Grs
import CheckUtils
import System.Environment
import Control.Monad(when)
import FrParsing
import MyMaybe
import LoadCheckDraw
import Utils

def_path = "FragmentaTests/FrPersonVehicleMotor/"
img_path = "FragmentaTests/FrPersonVehicleMotor/img/"

saveDrawings = do
   draw_mdl def_path img_path "PersonVehicleAny"
   draw_mdl def_path img_path "PersonVehicleMotor"
   draw_def def_path img_path "Person_Vehicle_Motor.fr"

check_PVA = do
    amdl<-load_mdl_def def_path "PersonVehicleAny"
    check_report_wf "PersonVehicleAny" (Just Total) amdl True

check_PVM = do
    mdl<-load_mdl_def def_path "PersonVehicleMotor"
    check_report_wf "PersonVehicleMotor" (Just Total) mdl True

-- Checks the well-formedness of the abstract model
do_test1 = do
   (nmaf, af)<-load_fr_def def_path "Person_Vehicle_AnyM.fr"
   check_report_wf nmaf (Just Total) af True

-- Checks the well-formedness of the concrete fragment against the abstract one
do_test2 = do
   (nmaf, af)<-load_fr_def def_path "Person_Vehicle_AnyM.fr"
   (nmf, f)<-load_fr_def def_path "Person_Vehicle_Motor.fr"
   (nm_m1, m1)<-load_morphism_def def_path "m_PVI.gm"
   check_report_wf nmaf (Just Total) af True
   check_report_wf nmf (Just Total) f True
   check_morphism (nm_m1++ " refinement morphism (Weak)") (Just WeakM) f m1 af True
   check_morphism (nm_m1++ " refinement morphism (Partial)") (Just PartialM) f m1 af True
   check_morphism (nm_m1++ " refinement morphism (Total)") (Just TotalM) f m1 af True
 

-- Checks the well-formedness of refinement
do_test3 = do
    amdl<-load_mdl_def def_path "PersonVehicleAny"
    mdl<-load_mdl_def def_path "PersonVehicleMotor"
    rms<-load_rm_cmdl_def def_path "PersonVehicleMotor"
    check_report_wf "PersonVehicleAny" (Just Total) amdl True
    check_report_wf "PersonVehicleMotor" (Just Total) mdl True
    check_morphism "Refinement of 'PersonVehicleMotor' by 'PersonVehicleAny'" (Just TotalM) mdl rms amdl True

do_main = do
   do_test1
   check_PVA
   check_PVM
   do_test2
   do_test3

main = do
   option_main_save do_main saveDrawings




