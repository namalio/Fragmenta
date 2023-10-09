------------------------
-- Project: Fragmenta
-- Module: 'StCsUtils'
-- Description: Utilities module  of IntoSysML which checks well-formedness  and draws statecharts
-- Author: Nuno Amálio
------------------------

module IntoSysML.IntoSysML_Utils
where

import Gr_Cls
import Grs
import SGrs
import GrswT
import GrswET 
import IntoSysML.IntoSysMLASD
import IntoSysML.IntoSysMLCD
import IntoSysML.ParsingASD
import IntoSysML.ParsingCD
import CheckUtils
import Control.Monad(when, forM, unless)
import MyMaybe
import TheNil
import ErrorAnalysis
import LoadCheckDraw
import IntoSysML.DrawASD
import IntoSysML.DrawCD
import SimpleFuns
import MMI

mm_path   = "IntoSysML/MM/"
intosyml_path = "IntoSysML/Examples/"
mm_img_path = "IntoSysML/MM/img/"
intosyml_img_path = "IntoSysML/Examples/img/"

--saveMMDrawings = do
--   draw_mdl mm_path mm_img_path "StCs_AMM"
--   draw_mdl mm_path mm_img_path "StCs_MM"

check_ASD_MM :: IO ()
check_ASD_MM = do
    mmi<-load_asd_mmi mm_path
    check_report_wf "IntoSysML_AMM" (Just Total) (gAMM mmi) True
    check_report_wf "IntoSysML_MM" (Just Total) (gCMM mmi) True
    check_morphism "Refinement of 'IntoSysML_MM' by 'IntoSysML_AMM'" (Just TotalM) (gCMM mmi) (gRM mmi) (gAMM mmi) True

check_CD_MM :: IO ()
check_CD_MM = do
    mmi<-loadMMI mm_path
    check_report_wf "IntoSysML_AMM" (Just Total) (gAMM mmi) True
    check_report_wf "IntoSysML_MM" (Just Total) (gCMM mmi) True
    check_morphism "Refinement of 'IntoSysML_MM' by 'IntoSysML_AMM'" (Just TotalM) (gCMM mmi) (gRM mmi) (gAMM mmi) True

--checkWF::MMI String->ASD String->IO(Bool)
checkWF :: (GM_CHK' g g', Eq a, Eq b, Show a, Show b) =>String ->String ->g' a b -> g a b -> IO Bool
checkWF nm nmk csg d = do
    let errs = faultsGM' nm (Just TotalM) (d, csg)
    unless (is_nil errs) $ do
        show_wf_msg (nmk ++ " " ++ nm) errs
    return (is_nil errs)

checkWFASD :: MMI String String -> ASD String String -> IO Bool
checkWFASD mmi asd = checkWF (gASDName asd) "ASD" (gCMM mmi) asd

checkWFCD :: MMI String String -> CDG String String -> IO Bool
checkWFCD mmi cd = checkWF (gCDName cd) "CD" (gCMM mmi) (ggwt cd)

loadAndCheckASD::String->String->MMI String String->IO (Maybe (GrwT String String))
loadAndCheckASD asd_path fnm mmi = do
  asd <- loadASD (asd_path ++ fnm)
  b <- checkWFASD mmi asd 
  return (boolMaybe b asd)

loadAndCheckCD::String->String->MMI String String->IO (Maybe (GrwET String String))
loadAndCheckCD spath fnm mmi = do
  cd <- loadCD (spath ++ fnm)
  b <- checkWFCD mmi cd 
  return (boolMaybe b cd)

writeASDDrawingToFile ::String->MMI String String->ASD String String -> IO ()
writeASDDrawingToFile asd_img_path mmi asd = 
   let draw_src = wrASDAsGraphviz mmi asd in
   writeFile (asd_img_path ++ gASDName asd ++ ".gv") draw_src

writeCDDrawingToFile :: String->MMI String String->CDG String String-> IO ()
writeCDDrawingToFile img_path mmi cd = 
   let draw_src = drawCD mmi cd in
   writeFile (img_path ++ gCDName cd ++ ".gv") draw_src

drawASDToFile :: String -> MMI String String -> ASD String String -> IO ()
drawASDToFile asd_img_path mmi asd = do
   putStrLn "Writing the ASD drawing to the GraphViz file..." 
   writeASDDrawingToFile asd_img_path mmi asd

drawCDToFile::String->MMI String String->CDG String String -> IO ()
drawCDToFile img_path mmi cd = do
   putStrLn "Writing the CD drawing to the GraphViz file..." 
   writeCDDrawingToFile img_path mmi cd

check_draw_asd :: FilePath -> FilePath -> MMI String String -> FilePath -> IO ()
check_draw_asd spath img_path mmi fn = do
   putStrLn $ "Processing '" ++ fn ++ "'" 
   oasd <- loadAndCheckASD spath fn mmi 
   when (isSomething oasd) $ do
      drawASDToFile img_path mmi (the oasd)

cdCheckDraw :: FilePath -> FilePath -> MMI String String -> FilePath -> IO ()
cdCheckDraw path img_path mmi fn = do
   putStrLn $ "Processing '" ++ fn ++ "'" 
   ocd<-loadAndCheckCD path fn mmi 
   when (isSomething ocd) $ drawCDToFile img_path mmi (the ocd)

check_draw_3WTs :: IO ()
check_draw_3WTs = do
    mmi<-load_asd_mmi mm_path
    check_draw_asd intosyml_path intosyml_img_path mmi "three_water_tanks.asd"

check_draw_WTs :: IO ()
check_draw_WTs = do
    mmi<-load_asd_mmi mm_path
    check_draw_asd intosyml_path intosyml_img_path mmi "water_tanks.asd"

check_draw_CD_WTs :: IO ()
check_draw_CD_WTs = do
    mmi<-loadMMI mm_path
    cdCheckDraw intosyml_path intosyml_img_path mmi "water_tanks.cd"

check_thermostat :: IO ()
check_thermostat = do
    mmi<-load_asd_mmi mm_path
    check_draw_asd intosyml_path intosyml_img_path mmi "thermostat.asd"

check_cash_machine :: IO ()
check_cash_machine = do
    mmi<-load_asd_mmi mm_path
    check_draw_asd intosyml_path intosyml_img_path mmi "cash_machine.asd"


test :: IO ()
test = do
    mmi<-load_asd_mmi mm_path
    cd<-loadCD (intosyml_path ++ "water_tanks.cd") -- >>= print
    print cd
    --print $ foldr (\c cs->gName cd c:cs) [] (gASDComps asd)
    --print $ mkCDDrawing mmi cd
    -- Problem in 'gConnectors' (try out 'nsNty')
    --print (gConnectors (gCRSG mmi) cd)
    --putStrLn $ show $ gMainDescs stc 
    --putStrLn $ show $ gDescInfo (stc_sg_cmm mmi) stc (gMainDescNode stc)
    --putStrLn $ show $ gTransitionInfo stc "BuzzingToMuted"
    --putStrLn $ show $ gMutableStateDescs stc "ProcessingSt"
    --putStrLn $ getStCName stc
    --putStrLn $ show $ getMainDescInfo (stc_sg_cmm mmi) stc
