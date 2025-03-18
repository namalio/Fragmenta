--------------------------
-- Project: PCs/Fragmenta
-- Module: 'vehicle_parts'
-- Description: Tests focused on example of vehicles, parts and wheels
-- Author: Nuno Amálio
---------------------------
import SGrs
import Grs
import Gr_Cls
import CheckUtils
    ( check_report_wf, check_morphism, check_ty_morphism )
import System.Environment
import Control.Monad(when)
import MyMaybe
import LoadCheckDraw
import GrswT
import Relations ( img )
import Utils (option_main_save)
import PathExpressions
import NumString
import Sets -- Remove later from here
import Relations

def_path :: FilePath
def_path = "FragmentaTests/VehicleParts/"

img_path :: FilePath
img_path = def_path ++ "img/"

saveDrawings :: IO ()
saveDrawings = do
   draw_def def_path img_path "SG_Vehicle_Parts.sg"
   draw_def def_path img_path "SG_Car_Wheels.sg"
   draw_def def_path img_path "SG_Vehicle_Wheels.sg"
   draw_def def_path img_path "SG_Pair_Bicycle.sg"
   draw_def def_path img_path "G_Car_Wheels_I1a.gwt"
   draw_def def_path img_path "G_Car_Wheels_I1b.gwt"
   draw_def def_path img_path "G_Car_Wheels_I2.gwt"
   draw_def def_path img_path "G_Vehicle_Wheels_I1.gwt"
   draw_def def_path img_path "G_Vehicle_Wheels_I2.gwt"
   draw_def def_path img_path "SG_Vehicle_Wheels.sg"
   draw_def def_path img_path "SG_Vehicle_Wheels.sg"
   draw_def def_path img_path "G_Bicycle_I1.gwt"
   draw_def def_path img_path "G_Bicycle_I2.gwt"
   draw_def def_path img_path "SG_Pair_Bicycle_Car.sg"
   draw_def def_path img_path "G_Bicycle_Car_I1.gwt"
   draw_def def_path img_path "G_Bicycle_Car_I2.gwt"
   draw_def def_path img_path "G_Bicycle_Car_I3.gwt"

test1 :: IO ()
test1 = do
   -- Checks the refinement
   (nm_asg, asg)<-loadSG def_path "SG_Vehicle_Parts.sg" -- SG_VP of Fig. 7d
   (nm_csg, csg)<-loadSG def_path "SG_Car_Wheels.sg" 
   (nm_m1, m1)<-loadM def_path "CW_VP.gm"
   putStrLn "Test 1: checks that an abstract model of a vehicle made up of parts\
            \ is refined by a model of a vehicle made up of 4 wheels"
   check_report_wf nm_asg (Just Total) asg True
   check_report_wf nm_csg (Just Total) csg True
   check_morphism (nm_m1 ++ ": " ++ nm_csg ++ "->" ++ nm_asg ++ " (Weak, morphism)") (Just WeakM) csg m1 asg True
   check_morphism (nm_m1 ++ ": " ++ nm_csg ++ "->" ++ nm_asg ++ " (Total, refinement)") (Just TotalM) csg m1 asg True

test2 :: IO ()
test2 = do
   (nm_asg, asg)<-loadSG def_path "SG_Vehicle_Parts.sg" -- SG_VP of Fig. 7d
   (nm_csg, csg)<-loadSG def_path "SG_Vehicle_Wheels.sg" -- SG_VWs of Fig. 7e
   (nm_m1, m1)<-loadM def_path "VW_VP.gm"
   putStrLn "Test 2: checks that an abstract model of a vehicle made up of parts\
            \ is refined by a model of an abstract vehicle which is either a three-wheeler or a car"
   check_report_wf nm_asg (Just Total) asg True
   check_report_wf nm_csg (Just Total) csg True
   check_morphism (nm_m1 ++ " morphism (Weak)") (Just WeakM) csg m1 asg True
   check_morphism (nm_m1 ++ " morphism (Partial)") (Just PartialM) csg m1 asg True
   check_morphism (nm_m1 ++ " morphism (Total)") (Just TotalM) csg m1 asg True

test3 :: IO ()
test3 = do
   (nm_asg, asg)<-loadSG def_path "SG_Vehicle_Parts.sg" -- SG_VP of Fig. 7d
   (nm_csg, csg)<-loadSG def_path "SG_Pair_Bicycle.sg"  -- SG_BI of Fig. 7f
   (nm_m1, m1)<-loadM def_path "PB_VP.gm"
   putStrLn "Test 3: checks that an abstract model of a vehicle made up of parts\
             \ is refined by a model of a bicycle with a pair of wheels (a sort of an instance of a pair pattern)."
   check_report_wf nm_asg (Just Total) asg True
   check_report_wf nm_csg (Just Total) csg True
   check_morphism (nm_m1 ++ " morphism (Weak)") (Just WeakM) csg m1 asg True
   check_morphism (nm_m1 ++ " morphism (Partial)") (Just PartialM) csg m1 asg True
   check_morphism (nm_m1 ++ " morphism (Total)") (Just TotalM) csg m1 asg True

test4 :: IO ()
test4 = do
   (nm_asg, asg)<-loadSG def_path "SG_Vehicle_Parts.sg" -- SG_VP of Fig. 7d
   (nm_csg, csg)<-loadSG def_path "SG_Pair_Bicycle_Car.sg" -- SG_BI of Fig. 7g
   (nm_m1, m1)<-loadM def_path "PBC_VP.gm"
   putStrLn "Test 4: checks that an abstract model of a vehicle made up of parts\
            \ is refined by a model of a bicycle with a pair of wheels, and a car made up of two side mirrors (both a sort instances of a pair pattern)."
   check_report_wf nm_asg (Just Total) asg True
   check_report_wf nm_csg (Just Total) csg True
   check_morphism (nm_m1 ++ " morphism (Weak)") (Just WeakM) csg m1 asg True
   check_morphism (nm_m1 ++ " morphism (Partial)") (Just PartialM) csg m1 asg True
   check_morphism (nm_m1 ++ " morphism (Total)") (Just TotalM) csg m1 asg True

test5 :: IO ()
test5 = do
   (nm_sg, sg)<-loadSG def_path "SG_Car_Wheels.sg"
   (nm_asg, asg)<-loadSG def_path "SG_Vehicle_Parts.sg" -- SG_VP of Fig. 7d
   (nm_ga, gwta)<-loadGwT def_path "G_Car_Wheels_I1a.gwt"
   (nm_gb, gwtb)<-loadGwT def_path "G_Car_Wheels_I1b.gwt"
   (nm_gc, gwtc)<-loadGwT def_path "G_Car_Wheels_I1c.gwt"
   putStrLn "Test 5: checks that an object model of an actual car with 4 wheels\ 
            \is an instance of: (i) a class model of a car made-up of 4 wheels\
            \and (ii) a model of a vehicle made-up of parts"
   check_report_wf nm_sg (Just Total) sg True
   check_report_wf nm_asg (Just Total) asg True
   check_report_wf nm_ga (Just Total) gwta True
   --check_report_wf nm_gb (Just Total) gwtb True
   --check_report_wf nm_gc (Just Total) gwtc True
   --check_ty_morphism (nm_ga ++ " (weak)") (Just WeakM) gwta sg True
   --check_ty_morphism (nm_ga ++ " (Total)") (Just TotalM) gwta sg True
   --check_ty_morphism (nm_gb ++ " (weak)") (Just WeakM) gwtb asg True
   --check_ty_morphism (nm_gb ++ " (Total)") (Just TotalM) gwtb asg True
   --check_ty_morphism (nm_gc ++ " (weak)") (Just WeakM) gwtc sg True
   --check_ty_morphism (nm_gc ++ " (Total)") (Just TotalM) gwtc sg False

test6 :: IO ()
test6 = do
   (nm_sg, sg)<-loadSG def_path "SG_Car_Wheels.sg"
   (nm_g, gwt)<-loadGwT def_path "G_Car_Wheels_I2.gwt"
   putStrLn "Test 6: checks that an object model of two cars, each with 3 wheels only, is not an instance of\
            \ a class model of a car made-up of 4 wheels"
   check_report_wf nm_sg (Just Total) sg True
   check_report_wf nm_g (Just Total) gwt True
   check_ty_morphism (nm_g ++ " (weak)") (Just WeakM) gwt sg True
   check_ty_morphism (nm_g ++ " (Total)") (Just TotalM) gwt sg False

test7 :: IO ()
test7 = do
   (nm_sg, sg)<-loadSG def_path "SG_Vehicle_Wheels.sg" -- SGVWs in Fig. 8g
   (nm_g1, gwt1)<-loadGwT def_path "G_Vehicle_Wheels_I1.gwt" -- Fig 8i
   (nm_g2, gwt2)<-loadGwT def_path "G_Vehicle_Wheels_I2.gwt" -- Fig 8j
   --print $ isVCEECnt sg "Etw_doors"
   --print $ isVCEECnt sg "Ecar_ndoors_neq2"
   --print $ img (inv . fV $ gwt1) (img (src sg) $ singles "Etw_doors")
   --print $ filterS (\e->appl (fV gwt2) (appl (src gwt2) e) == appl (src sg) "Ecar_ndoors_neq2") $ img (inv . fE $ gwt2) (maybeToSet . snd . appl (vcei sg) $ "Ecar_ndoors_neq2")
   --print $ satisfiesVCEECnt sg gwt1 "Etw_doors"
   --putStrLn $ show (ins gwt1 sg $ img (srcst sg) ["EHWs_1"])
   --putStrLn $ show (multOk_r sg "EHWs_1" gwt1)
   --let srcstr = multOk_srcstr sg "EHWs_1"
   --putStrLn $ show (ins gwt1 sg $ img srcstr [rsPE $ ape sg "EHWs_1"])
   --let tgtstr = multOk_tgtstr sg "EHWs_1"
   --putStrLn $ show (ins gwt1 sg $ img tgtstr [rsPE $ ape sg "EHWs_1"])
   putStrLn "Test 7 (Fig. 8): checks that the following object models comply to a class model of a car made-up of 4 wheels and a three-wheeler:\n\
            \(i) one car and one three-wheeler is a valid instance,\n\ 
            \and (ii) one three-wheeler and one car with three wheels is not a valid instance." 
   check_report_wf nm_sg (Just Total) sg True
   check_report_wf nm_g1 (Just Total) gwt1 True
   check_report_wf nm_g2 (Just Total) gwt2 True
   check_ty_morphism (nm_g1 ++ " (weak)") (Just WeakM) gwt1 sg True
   check_ty_morphism (nm_g1 ++ " (Total)") (Just TotalM) gwt1 sg True
   check_ty_morphism (nm_g2 ++ " (weak)") (Just WeakM) gwt2 sg True
   check_ty_morphism (nm_g2 ++ " (Total)") (Just TotalM) gwt2 sg False

test8 :: IO ()
test8 = do
   (nm_sg, sg)<-loadSG def_path "SG_Pair_Bicycle.sg"
   (nm_g1, gwt1)<-loadGwT def_path "G_Bicycle_I1.gwt"
   (nm_g2, gwt2)<-loadGwT def_path "G_Bicycle_I2.gwt"
   putStrLn "Test 8: checks compliance of the following object models against a \
            \class model of a bicycle with a pair of wheels (defined as generic):\n\
            \ (i) a bicyle with two wheels is a valid instance\
            \ and (ii) a bicycle with two wheels which are instances of virtuals X and Y is not a valid instance."
   check_report_wf nm_sg (Just Total) sg True
   check_ty_morphism (nm_g1 ++ " (weak)") (Just WeakM) gwt1 sg True
   check_ty_morphism (nm_g1 ++ " (Total)") (Just TotalM) gwt1 sg True
   check_ty_morphism (nm_g2 ++ " (weak)") (Just WeakM) gwt2 sg True
   check_ty_morphism (nm_g2 ++ " (Total)") (Just TotalM) gwt2 sg False

test9 :: IO ()
test9 = do
   (nm_sg, sg)<-loadSG def_path "SG_Pair_Bicycle_Car.sg"
   (nm_g1, gwt1)<-loadGwT def_path "G_Bicycle_Car_I1.gwt"
   (nm_g2, gwt2)<-loadGwT def_path "G_Bicycle_Car_I2.gwt"
   (nm_g3, gwt3)<-loadGwT def_path "G_Bicycle_Car_I3.gwt"
   putStrLn "Test 9: checks compliance of the following object models against a \
            \class model of a bicycle with a pair of wheels and a car as a pair of side mirrors (both defined as generics):\n\
            \ (i) a bicyle with two wheels and a car with two mirrors is a valid instance,\
            \ (ii) a bicycle with two wheels and a car with with wheels in the place of mirrors is not a valid instance,\
            \ and (iii) two bicycles that share one of the wheels and a car with two side mirrors is not a valid instance. "
   check_report_wf nm_sg (Just Total) sg True
   check_ty_morphism (nm_g1 ++ " (Weak)") (Just WeakM) gwt1 sg True
   check_ty_morphism (nm_g1 ++ " (Total)") (Just TotalM) gwt1 sg True
   check_ty_morphism (nm_g2 ++ " (Weak)") (Just WeakM) gwt2 sg True
   check_ty_morphism (nm_g2 ++ " (Total)") (Just TotalM) gwt2 sg False
   check_ty_morphism (nm_g3 ++ " (Weak)") (Just WeakM) gwt3 sg True
   check_ty_morphism (nm_g3 ++ " (Total)") (Just TotalM) gwt3 sg False

do_main :: IO ()
do_main = do
   test1
   test2
   test3
   test4
   test5
   test6
   test7
   test8
   test9

main :: IO ()
main = do
   option_main_save do_main saveDrawings




