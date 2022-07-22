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
import IntoSysML.IntoSysML
import IntoSysML.ASDParsing
import CheckUtils
import Control.Monad(when, forM)
import MyMaybe
import The_Nil
import ErrorAnalysis
import LoadCheckDraw
import IntoSysML.ASDsDraw
import SimpleFuns
import MMI

mm_path   = "IntoSysML/MM/"
intosyml_path = "IntoSysML/Examples/"
mm_img_path = "IntoSysML/MM/img/"
intosyml_img_path = "IntoSysML/Examples/img/"

--saveMMDrawings = do
--   draw_mdl mm_path mm_img_path "StCs_AMM"
--   draw_mdl mm_path mm_img_path "StCs_MM"

check_ASD_MM = do
    mmi<-load_asd_mmi mm_path
    check_report_wf "IntoSysML_AMM" (Just Total) (mmi_amm mmi) True
    check_report_wf "IntoSysML_MM" (Just Total) (mmi_cmm mmi) True
    check_morphism "Refinement of 'IntoSysML_MM' by 'IntoSysML_AMM'" (Just TotalM) (mmi_cmm mmi) (mmi_rm mmi) (mmi_amm mmi) True

checkWF::MMI String->ASD String->IO(Bool)
checkWF mmi asd = do
    let asd_nm = gASDName asd
    let errs = check_wf_gm' asd_nm (Just TotalM) (asd, mmi_cmm mmi) 
    when (not . is_nil $ errs) $ do
        show_wf_msg ("ASD " ++ asd_nm) errs
    return (is_nil errs)

loadAndCheck asd_path fnm mmi = do
  asd <- loadASD (asd_path ++ fnm)
  b <- checkWF mmi asd 
  return (boolMaybe b asd)

writeASDDrawingToFile asd_img_path mmi asd = 
   let draw_src = wrASDAsGraphviz mmi asd in
   writeFile (asd_img_path ++ (gASDName asd) ++ ".gv") draw_src

drawASDToFile asd_img_path mmi asd = do
   putStrLn "Writing the ASD drawing to the GraphViz file..." 
   writeASDDrawingToFile asd_img_path mmi asd

check_draw_asd asd_path asd_img_path mmi fn = do
   putStrLn $ "Processing '" ++ fn ++ "'" 
   oasd <- loadAndCheck asd_path fn mmi
   when (isSomething oasd) $ do
      drawASDToFile asd_img_path mmi (the oasd)

check_draw_3WTs = do
    mmi<-load_asd_mmi mm_path
    check_draw_asd intosyml_path intosyml_img_path mmi "three_water_tanks.asd"

check_thermostat = do
    mmi<-load_asd_mmi mm_path
    check_draw_asd intosyml_path intosyml_img_path mmi "thermostat.asd"

check_cash_machine = do
    mmi<-load_asd_mmi mm_path
    check_draw_asd intosyml_path intosyml_img_path mmi "cash_machine.asd"

test = do
    mmi<-load_asd_mmi mm_path
    asd <- loadASD (intosyml_path ++ "cash_machine.asd") 
    putStrLn $ show asd
    putStrLn $ show $ drawASD mmi asd
--    putStrLn $ show $ gMainDescs stc 
    --putStrLn $ gStCName stc
    --putStrLn $ show $ gDescInfo (stc_sg_cmm mmi) stc (gMainDescNode stc)
    --putStrLn $ show $ gTransitionInfo stc "BuzzingToMuted"
    -- putStrLn $ show $ gMutableStateDescs stc "ProcessingSt"
    -- putStrLn $ getStCName stc
    -- putStrLn $ show $ getMainDescInfo (stc_sg_cmm mmi) stc
