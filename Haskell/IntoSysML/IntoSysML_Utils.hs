------------------------
-- Project: Fragmenta
-- Module: 'StCsUtils'
-- Description: Utilities module  of IntoSysML which checks well-formedness  and draws statecharts
-- Author: Nuno Amálio
------------------------

module IntoSysML.StCsUtils
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
--import Statecharts.StCsDraw
import SimpleFuns

mm_path   = "IntoSysML/MM/"
intosyml_path = "IntoSysML/Examples/"
mm_img_path = "IntoSysML/MM/img/"
intosyml_img_path = "IntoSysML/Examples/img/"

--saveMMDrawings = do
--   draw_mdl mm_path mm_img_path "StCs_AMM"
--   draw_mdl mm_path mm_img_path "StCs_MM"

check_asd_MM = do
    mmi<-load_asd_mmi mm_path
    check_report_wf "IntoSysML_AMM" (Just Total) (stc_amm mmi) True
    check_report_wf "IntoSysML_MM" (Just Total) (stc_cmm mmi) True
    check_morphism "Refinement of 'IntoSysML_MM' by 'IntoSysML_AMM'" (Just TotalM) (stc_cmm mmi) (stc_rm mmi) (stc_amm mmi) True

checkWF::MMI String->ASD String->IO(Bool)
checkWF mmi asd = do
    let asd_nm = gASDName asd
    let errs = check_wf_gm' asd_nm (Just TotalM) (asd, mmi_cmm mmi) 
    when (not . is_nil $ errs) $ do
        show_wf_msg ("ASD " ++ stc_nm) errs
    return (is_nil errs)

loadAndCheck asd_path fnm mmi = do
  asd <- loadASD (asd_path ++ fnm)
  b <- checkWF mmi asd 
  return (boolMaybe b asd)

--writeASDDrawingToFile asd_img_path mmi asd = do
--   let draw_src = wrASDAsGraphviz mmi asd
--   writeFile (asd_img_path ++ (gASDName asd) ++ ".gv") draw_src

--drawASDToFile asd_img_path mmi asd = do
--   putStrLn "Writing the ASD drawing to the GraphViz file..." 
--   writeStCDrawingToFile stc_img_path mmi stc

--check_draw_stc stcs_path stc_img_path mmi fn = do
--   putStrLn $ "Processing '" ++ fn ++ "'" 
--   ostc <- loadAndCheck stcs_path fn mmi
--   when (isSomething ostc) $ do
--      drawStCToFile stc_img_path mmi (the ostc)

check_draw_BoolSetter = do
    mmi<-load_stcs_mmi mm_path
    check_draw_stc stcs_path stc_img_path mmi "BoolSetter.stc"

check_draw_Buzzer = do
    mmi<-load_stcs_mmi mm_path
    check_draw_stc stcs_path stc_img_path mmi "Buzzer.stc"

check_draw_WBuzzer = do
    mmi<-load_stcs_mmi mm_path
    check_draw_stc stcs_path stc_img_path mmi "WBuzzer.stc"

check_draw_BuzzerWStatus = do
    mmi<-load_stcs_mmi mm_path
    check_draw_stc stcs_path stc_img_path mmi "BuzzerWStatus.stc"

check_draw_Lasbscs = do
    mmi<-load_stcs_mmi mm_path
    check_draw_stc stcs_path stc_img_path mmi "Lasbscs.stc"

check_draw_SimpleWatch = do
    mmi<-load_stcs_mmi mm_path
    check_draw_stc stcs_path stc_img_path mmi "SimpleWatch.stc"

check_draw_Gland = do
    mmi<-load_stcs_mmi mm_path
    check_draw_stc stcs_path stc_img_path mmi "Gland.stc"

check_draw_RGland = do
    mmi<-load_stcs_mmi mm_path
    check_draw_stc stcs_path stc_img_path mmi "RGland.stc"

check_draw_TVSet = do
    mmi<-load_stcs_mmi mm_path
    check_draw_stc stcs_path stc_img_path mmi "TVSet.stc"

draw_RGland = do
    mmi<-load_stcs_mmi mm_path
    stc <- loadStC (stcs_path ++ "RGland.stc") 
    writeStCDrawingToFile stc_img_path mmi stc

draw_WBuzzer = do
    mmi<-load_stcs_mmi mm_path
    stc <- loadStC (stcs_path ++ "WBuzzer.stc") 
    writeStCDrawingToFile stc_img_path mmi stc

test = do
    mmi<-load_stcs_mmi mm_path
    --check_draw_stc stcs_path stc_img_path mmi "BoolSetter.stc"
    stc <- loadStC (stcs_path ++ "SimpleWatch.stc") 
    putStrLn $ show stc
    putStrLn $ show $ gMainDescs stc 
    --putStrLn $ gStCName stc
    --putStrLn $ show $ gDescInfo (stc_sg_cmm mmi) stc (gMainDescNode stc)
    --putStrLn $ show $ gTransitionInfo stc "BuzzingToMuted"
    putStrLn $ show $ drawStC mmi stc
    -- putStrLn $ show $ gMutableStateDescs stc "ProcessingSt"
    -- putStrLn $ getStCName stc
    -- putStrLn $ show $ getMainDescInfo (stc_sg_cmm mmi) stc
