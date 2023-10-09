--------------------------
-- Project: PCs/Fragmenta
-- Module: 'SGTest2'
-- Description: Batch of tests exercising features of SGs and SG refinement
-- Author: Nuno Amálio
---------------------------
import Grs
import CheckUtils ( check_morphism, check_report_wf )
import System.Environment
import Control.Monad(when)
import LoadCheckDraw
import Utils ( option_main_save )

def_path = "FragmentaTests/FrPersonVehicleMotor/"
img_path = "FragmentaTests/FrPersonVehicleMotor/img/"

saveDrawings :: IO ()
saveDrawings = do
   draw_mdl def_path img_path "PersonVehicleAny"
   draw_mdl def_path img_path "PersonVehicleMotor"
   draw_def def_path img_path "Person_Vehicle_Motor.fr"

check_PVA :: IO ()
check_PVA = do
    (nm_amdl, amdl)<-loadMdl def_path "PersonVehicleAny"
    check_report_wf nm_amdl (Just Total) amdl True

check_PVM :: IO ()
check_PVM = do
    (nm_mdl, mdl)<-loadMdl def_path "PersonVehicleMotor"
    check_report_wf nm_mdl (Just Total) mdl True

-- Checks the well-formedness of the abstract model
do_test1 :: IO ()
do_test1 = do
   putStrLn "Test 1"
   (nmaf, af)<-loadF def_path "Person_Vehicle_AnyM.fr"
   check_report_wf nmaf (Just Total) af True

-- Checks the well-formedness of the concrete fragment against the abstract one
do_test2 :: IO ()
do_test2 = do
   putStrLn "Test 2"
   (nmaf, af)<-loadF def_path "Person_Vehicle_AnyM.fr"
   (nmf, f)<-loadF def_path "Person_Vehicle_Motor.fr"
   (nm_m1, m1)<-loadM def_path "m_PVI.gm"
   check_report_wf nmaf (Just Total) af True
   check_report_wf nmf (Just Total) f True
   check_morphism (nm_m1++ " total morphism") Nothing f m1 af True
   check_morphism (nm_m1++ " refinement morphism (Partial)") (Just PartialM) f m1 af True
   check_morphism (nm_m1++ " refinement morphism (Total)") (Just TotalM) f m1 af True
 

-- Checks the well-formedness of refinement
do_test3 :: IO ()
do_test3 = do
   putStrLn "Test 3"
   (nm_amdl, amdl)<-loadMdl def_path "PersonVehicleAny"
   (nm_mdl, mdl)<-loadMdl def_path "PersonVehicleMotor"
   rms<-load_rm_cmdl_def def_path "PersonVehicleMotor"
   check_report_wf nm_amdl (Just Total) amdl True
   check_report_wf nm_mdl (Just Total) mdl True
   check_morphism ("Refinement of '" ++ nm_mdl ++ "' by '" ++ nm_amdl ++ "'") (Just TotalM) mdl rms amdl True

do_main :: IO ()
do_main = do
   do_test1
   check_PVA
   check_PVM
   do_test2
   do_test3

main :: IO ()
main = do
   option_main_save do_main saveDrawings





