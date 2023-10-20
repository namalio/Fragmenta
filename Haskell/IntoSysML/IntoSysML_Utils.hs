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
import IntoSysML.CheckCD

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
    mmi<-loadCDMMI mm_path
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

checkET::(GWET g, GWT g', Eq a, Eq b, Show a, Show b, ET_GM_CHK g g' gt)
    =>String ->String ->g a b -> g' a b ->gt a b->gt a b-> IO Bool
checkET nm nmk d dt mdl mdlt = do
    let errs = faultsETGM nm (d, mdl) (dt, mdlt)
    unless (is_nil errs) $ do
        show_wf_msg (nmk ++ " " ++ nm) errs
    return (is_nil errs)

checkWFASD :: MMI String String -> ASD String String -> IO Bool
checkWFASD mmi asd = checkWF (gASDName asd) "ASD" (gCMM mmi) asd

checkWFCD :: MMI String String ->MMI String String -> CDG String String -> ASD String String -> IO Bool
checkWFCD mmi mmit cd asd = do
    b<-checkWF (gCDName cd) "CD" (gCMM mmi) (ggwt cd)
    b1<-if b then checkET (gCDName cd) "CD" cd asd (gCMM mmi) (gCMM mmit) else return False
    if b1 
        then if checkPDG (gCRSG mmi) asd cd
             then return True
             else do
                putStrLn "The ports dependency graph has a cycle"
                return False
        else return False



loadAndCheckASD::String->String->MMI String String->IO (Maybe (GrwT String String))
loadAndCheckASD asd_path fnm mmi = do
  asd <- loadASD (asd_path ++ fnm)
  b <- checkWFASD mmi asd 
  return (boolMaybe b asd)

loadAndCheckCD::FilePath->FilePath->FilePath->MMI String String->MMI String String->IO (Maybe (GrwET String String))
loadAndCheckCD spath fnm fnmt mmi mmit = do
  cd <- loadCD (spath ++ fnm)
  asd <- loadASD (spath ++ fnmt)
  b <- checkWFCD mmi mmit cd asd 
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
   when (isSomething oasd) $ drawASDToFile img_path mmi (the oasd)

cdCheckDraw::FilePath->FilePath->MMI String String 
    -> MMI String String->FilePath->FilePath-> IO ()
cdCheckDraw path img_path mmi mmit fn1 fnt = do
   putStrLn $ "Processing '" ++ fn1 ++ "'" 
   ocd<-loadAndCheckCD path fn1 fnt  mmi mmit
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
    mmi<-loadCDMMI mm_path
    mmit<-load_asd_mmi mm_path
    cdCheckDraw intosyml_path intosyml_img_path mmi mmit "water_tanks.cd" "water_tanks.asd"
    

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
    mmi<-loadCDMMI mm_path
    cd<-loadCD (intosyml_path ++ "water_tanks.cd") -- >>= print
    asd<-loadASD (intosyml_path ++ "water_tanks.asd")
    savePDGDrawing intosyml_img_path (gCRSG mmi) asd cd
    --print (gCDPorts (gCRSG mmi) cd)
    --print (etm cd)
    --let m = fet . mufs . gCMM $ mmi
    --print (etm cd)
    --print (m `ogm` ty cd)
    --print (domg $ etm cd)
    --print (domg $ m `ogm` ty cd)
    --mmi<-load_asd_mmi mm_path
    --asd<-loadASD (intosyml_path ++ "test_asd.asd") -- >>= print
    --print asd
    --print (gDTypePTy asd "Area_Type")
    --print $ foldr (\c cs->gName cd c:cs) [] (gASDComps asd)
    --print $ drawASD mmi asd
    -- Problem in 'gConnectors' (try out 'nsNty')
    --print (gConnectors (gCRSG mmi) cd)
    --print (gSrcP cd "T_wo_D_wi_Connector")
    --print (gTgtP cd "T_wo_D_wi_Connector")
    --print (appl (consRelOfEdge cd CD_MM_EConnector_src) "T_wo_D_wi_Connector")
    --print (nsNTy (gCRSG mmi) cd CD_MM_Connector)
    --print (ns_of_ntys cd (gCRSG mmi) [show_cd_mm_n CD_MM_Connector])
    --print (img (inv . fV $ ty cd) [show_cd_mm_n CD_MM_Connector])
    --print (img (inv . inhst $ gCRSG mmi) [show_cd_mm_n CD_MM_Connector])
    --print (nsNTy (gCRSG mmi) cd CD_MM_Name)
    --print (nsNTy (gCRSG mmi) cd CD_MM_PortI)
    --print (nsNTy (gCRSG mmi) cd CD_MM_ATypeRef)
    --print (nsNTy (gCRSG mmi) cd CD_MM_Named)
    --print (nsNTy (gCRSG mmi) cd CD_MM_ConfigurationDiagram)
   
