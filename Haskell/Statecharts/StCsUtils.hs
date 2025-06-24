------------------------
-- Project: Fragmenta
-- Module: 'StCsUtils'
-- Description: Utilities for statecharts; 
--              checks well-formedness and draws statecharts
-- Author: Nuno Amálio
------------------------

module Statecharts.StCsUtils
where

import Gr_Cls
import Grs
import Statecharts.StCs
import Statecharts.StCsParsing
import CheckUtils
import Control.Monad(when, forM, unless)
import MyMaybe
import TheNil
import ErrorAnalysis
import LoadCheckDraw
import Statecharts.StCsDraw
import SimpleFuns
import MMI
import GrswT ( GrwT )
import NumString
import Utils ( option_main_save )

mm_path :: String
mm_path   = "Statecharts/MM/"
stcs_path :: String
stcs_path = "Statecharts/Examples/"
mm_img_path :: String
mm_img_path = "Statecharts/MM/img/"
stc_img_path :: String
stc_img_path = "Statecharts/Examples/img/"

saveMMDrawings :: IO ()
saveMMDrawings = do
   draw_mdl mm_path mm_img_path "StCs_AMM"
   draw_mdl mm_path mm_img_path "StCs_MM"

check_stcs_MM :: IO ()
check_stcs_MM = do
    mmi<-load_stcs_mmi mm_path
    check_report_wf "StCs_AMM" (Just Total) (gAMM mmi) True
    check_report_wf "StCs_MM" (Just Total) (gCMM mmi) True
    check_morphism "Refinement of 'StCs_MM' by 'StCs_AMM'" (Just TotalM) (gCMM mmi) (gRM mmi) (gAMM mmi) True

checkWF::MMI String String->StC String String->IO Bool
checkWF mmi stc = do
    let stc_nm = gStCName stc
    let errs = faultsGM' stc_nm (Just TotalM) (stc, gCMM mmi) 
    unless (is_nil  errs) $ do
        show_wf_msg ("StC " ++ stc_nm) errs
    return (is_nil errs)

loadAndCheck :: FilePath->FilePath-> MMI String String-> IO (Maybe (GrwT String String))
loadAndCheck stcs_path fnm mmi = do
  stc <- loadStC (stcs_path ++ fnm)
  b <- checkWF mmi stc 
  return (boolMaybe b stc)

writeStCDrawingToFile :: (GRM gm, GR gm) =>String-> MMI String String -> gm String String -> IO ()
writeStCDrawingToFile stc_img_path mmi stc = do
   let draw_src = wrStCAsGraphviz mmi stc 
   writeFile (stc_img_path ++ (gStCName stc) ++ ".gv") draw_src

drawStCToFile :: (GRM gm, GR gm) =>String -> MMI String String -> gm String String -> IO ()
drawStCToFile stc_img_path mmi stc = do
   putStrLn "Writing the statechart drawing to the GraphViz file..." 
   writeStCDrawingToFile stc_img_path mmi stc

check_draw_stc :: FilePath -> FilePath -> MMI String String -> FilePath -> IO ()
check_draw_stc stcs_path stc_img_path mmi fn = do
   putStrLn $ "Processing '" ++ fn ++ "'" 
   ostc <- loadAndCheck stcs_path fn mmi
   when (isSomething ostc) $ do
      drawStCToFile stc_img_path mmi (the ostc)

check_draw_BoolSetter :: IO ()
check_draw_BoolSetter = do
    mmi<-load_stcs_mmi mm_path
    check_draw_stc stcs_path stc_img_path mmi "BoolSetter.stc"

check_draw_Buzzer :: IO ()
check_draw_Buzzer = do
    print "The Simple Buzzer (Valid)"
    mmi<-load_stcs_mmi mm_path
    check_draw_stc stcs_path stc_img_path mmi "Buzzer.stc"

check_draw_WBuzzer :: IO ()
check_draw_WBuzzer = do
    print "The Simple Buzzer with two initial states (Invalid)"
    mmi<-load_stcs_mmi mm_path
    check_draw_stc stcs_path stc_img_path mmi "WBuzzer.stc"

check_draw_BuzzerWStatus :: IO ()
check_draw_BuzzerWStatus = do
    print "A Buzzer with status of Fig. 12.c (Valid)"
    mmi<-load_stcs_mmi mm_path
    check_draw_stc stcs_path stc_img_path mmi "BuzzerWStatus.stc"

check_draw_WBuzzerWStatus :: IO ()
check_draw_WBuzzerWStatus = do
    print "The Buzzer with status of Fig. 12.d with a missing initial state(Invalid)"
    mmi<-load_stcs_mmi mm_path
    check_draw_stc stcs_path stc_img_path mmi "WBuzzerWStatus.stc"

check_draw_WBuzzerWStatus2 :: IO ()
check_draw_WBuzzerWStatus2 = do
    mmi<-load_stcs_mmi mm_path
    check_draw_stc stcs_path stc_img_path mmi "WBuzzerWStatus2.stc"

check_draw_Lasbscs :: IO ()
check_draw_Lasbscs = do
    mmi<-load_stcs_mmi mm_path
    check_draw_stc stcs_path stc_img_path mmi "Lasbscs.stc"

check_draw_SimpleWatch :: IO ()
check_draw_SimpleWatch = do
    mmi<-load_stcs_mmi mm_path
    check_draw_stc stcs_path stc_img_path mmi "SimpleWatch.stc"

check_draw_Gland :: IO ()
check_draw_Gland = do
    print "The Gland example of Fig. 22a in paper (Valid)"
    mmi<-load_stcs_mmi mm_path
    check_draw_stc stcs_path stc_img_path mmi "Gland.stc"

check_draw_RGland :: IO ()
check_draw_RGland = do
    print "The Ressuscitating Gland example of Fig. 22b in paper (Invalid)"
    mmi<-load_stcs_mmi mm_path
    check_draw_stc stcs_path stc_img_path mmi "RGland.stc"

check_draw_TVSet :: IO ()
check_draw_TVSet = do
    mmi<-load_stcs_mmi mm_path
    check_draw_stc stcs_path stc_img_path mmi "TVSet.stc"

draw_RGland :: IO ()
draw_RGland = do
    mmi<-load_stcs_mmi mm_path
    stc <- loadStC (stcs_path ++ "RGland.stc") 
    writeStCDrawingToFile stc_img_path mmi stc

draw_WBuzzer :: IO ()
draw_WBuzzer = do
    mmi<-load_stcs_mmi mm_path
    stc <- loadStC (stcs_path ++ "WBuzzer.stc") 
    writeStCDrawingToFile stc_img_path mmi stc

draw_WBuzzerWStatus :: IO ()
draw_WBuzzerWStatus = do
    mmi<-load_stcs_mmi mm_path
    stc <- loadStC (stcs_path ++ "WBuzzerWStatus.stc") 
    writeStCDrawingToFile stc_img_path mmi stc

draw_WBuzzerWStatus2 :: IO ()
draw_WBuzzerWStatus2 = do
    mmi<-load_stcs_mmi mm_path
    stc <- loadStC (stcs_path ++ "WBuzzerWStatus2.stc") 
    writeStCDrawingToFile stc_img_path mmi stc

test :: IO ()
test = do
    mmi<-load_stcs_mmi mm_path
    --check_draw_stc stcs_path stc_img_path mmi "BoolSetter.stc"
    stc <- loadStC (stcs_path ++ "WBuzzerWStatus2.stc") 
    drawStCToFile stc_img_path mmi stc
    putStrLn . show $ stc
    putStrLn . show $ gMainDescs stc
    --putStrLn $ gStCName stc
    --putStrLn $ show $ gDescInfo (stc_sg_cmm mmi) stc (gMainDescNode stc)
    --putStrLn $ show $ gTransitionInfo stc "BuzzingToMuted"
    putStrLn $ show (drawStC mmi stc)
    -- putStrLn $ show $ gMutableStateDescs stc "ProcessingSt"
    -- putStrLn $ getStCName stc
    -- putStrLn $ show $ getMainDescInfo (stc_sg_cmm mmi) stc

do_main :: IO ()
do_main = do
    print "Checking the Statecharts metamodel"
    check_stcs_MM

main :: IO ()
main = do
    option_main_save do_main saveMMDrawings
    check_draw_BoolSetter
    check_draw_Buzzer
    check_draw_WBuzzer
    draw_WBuzzer
    check_draw_BuzzerWStatus 
    check_draw_WBuzzerWStatus 
    draw_WBuzzerWStatus
    check_draw_WBuzzerWStatus2
    draw_WBuzzerWStatus2
    check_draw_Lasbscs 
    check_draw_SimpleWatch
    check_draw_Gland
    check_draw_RGland
    draw_RGland
    check_draw_TVSet