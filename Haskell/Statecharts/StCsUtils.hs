------------------------
-- Project: Fragmenta
-- Module: 'StCsUtils'
-- Description: Utilities module of statecharts
-- Author: Nuno Amálio
------------------------

module Statecharts.StCsUtils
where

import Gr_Cls
import Grs
import Statecharts.StCs
import Statecharts.StcsParsing
import CheckUtils
import Control.Monad(when, forM)
import MyMaybe
import The_Nil
import ErrorAnalysis
import LoadCheckDraw
import Statecharts.StCsDraw
import SimpleFuns

mm_path   = "Statecharts/MM/"
stcs_path = "Statecharts/Examples/"
mm_img_path = "Statecharts/MM/img/"
stc_img_path = "Statecharts/Examples/img/"

saveMMDrawings = do
   draw_mdl mm_path mm_img_path "StCs_AMM"
   draw_mdl mm_path mm_img_path "StCs_MM"

check_stcs_MM = do
    mmi<-load_stcs_mmi mm_path
    check_report_wf "StCs_AMM" (Just Total) (stc_amm mmi) True
    check_report_wf "StCs_MM" (Just Total) (stc_cmm mmi) True
    check_morphism "Refinement of 'StCs_MM' by 'StCs_AMM'" (Just TotalM) (stc_cmm mmi) (stc_rm mmi) (stc_amm mmi) True

checkWF::StC_MMI String->StC String->IO(Bool)
checkWF mmi stc = do
    let stc_nm = gStCName stc
    let errs = check_wf_gm' stc_nm (Just TotalM) (stc, stc_cmm mmi) 
    when (not . is_nil $ errs) $ do
        show_wf_msg ("StC " ++ stc_nm) errs
    return (is_nil errs)

loadAndCheck stcs_path fnm mmi = do
  stc <- loadStC (stcs_path ++ fnm)
  b <- checkWF mmi stc 
  return (boolMaybe b stc)

writeStCDrawingToFile stc_img_path mmi stc = do
   let draw_src = wrStCAsGraphviz mmi stc 
   writeFile (stc_img_path ++ (gStCName stc) ++ ".gv") draw_src

drawStCToFile stc_img_path mmi stc = do
   putStrLn "Writing the statechart drawing to the GraphViz file..." 
   writeStCDrawingToFile stc_img_path mmi stc

check_draw_stc stcs_path stc_img_path mmi fn = do
   putStrLn $ "Processing '" ++ fn ++ "'" 
   ostc <- loadAndCheck stcs_path fn mmi
   when (isSomething ostc) $ do
      drawStCToFile stc_img_path mmi (the ostc)

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
