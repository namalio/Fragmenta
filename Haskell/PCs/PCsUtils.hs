
---------------------
-- Project: PCs/Utils
-- Module: 'PCsUtils'
-- Description: Utilities module of PCs
-- Author: Nuno Amálio
--------------------
module PCs.PCsUtils(
   writeCSPToFile
   , checkWFAndGeneratePCTree
   , checkWF
   , outputDrawing
   , outputCSP) where

import Gr_Cls
import PCs.PCs
import SGrs
import GrswT
import PCs.ToCSP ( toCSP )
import PCs.PCTrees
import CSP.CSPPrint
import System.IO
import Control.Monad(when, forM, unless, forM_, foldM)
import PCs.PCsDraw
import PCs.ParsingPCs
import Relations
import Sets
import SimpleFuns
import ErrorAnalysis
import CheckUtils
import TheNil
import MyMaybe
import System.Environment
import NumString
import PCs.PCs_MM_Names
import MMI
import ParseUtils
import PCs.PCTrees_TC
import PCs.PCTrees_TypeErrors
import PCs.PCTrees_Types
--import ShowUtils -- remove later
--import PCs.ParsingPCTxtExp -- remove later
import Control.Monad.Except
import Control.Monad.State

mm_path :: String
mm_path = "PCs/MM/"
pcs_path :: String
pcs_path = "PCs/Examples/"
csp_path :: String
csp_path = "PCs/Examples/CSP/"
img_path :: String
img_path = "PCs/Examples/img/"

getImportedAtoms::FilePath->SGr String String->PC String String->IO (Set String)
getImportedAtoms pcs_path sg_mm pc = do
   let is = importsOf sg_mm pc
   as <- forM is (\n-> do 
      opc<-loadPC sg_mm (pcs_path ++ n ++".pc") 
      (if isSomething opc then do
         as <- getImportedAtoms pcs_path sg_mm (the opc)
         return (as `union` set (getAtoms sg_mm $ the opc))
      else do
        return nil))
   return (gunion as)


getImports::FilePath->SGr String String->PC String String->IO (Set String)
getImports pcs_path sg_mm pc = do
   let is = importsOf sg_mm pc
   is <- forM is (\n-> do 
      opc<-loadPC sg_mm (pcs_path ++ n ++".pc") 
      (if isSomething opc then do
         is' <- getImports pcs_path sg_mm (the opc)
         let is_ = importsOf sg_mm (the opc)
         return (is `union` (is' `union` is_))
      else do
         return nil))
   return (gunion is)

writeDrawingToFile :: String -> MMI String String -> PC String String -> IO ()
writeDrawingToFile img_path mmi pc = do
   let draw_src = wrPCAsGraphviz mmi pc  
   writeFile (img_path ++ (getPCDef pc) ++ ".gv") draw_src

--writePCDef pc m = 
--   let pc_txt = wrPC $ frPCtoPCNot pc m in
--   writeFile ("pcs/"++ (getPCDef m) ++ ".pc") pc_txt

checkWFAndGeneratePCTree :: MMI String String -> PC String String -> IO ()
checkWFAndGeneratePCTree mmi pc = do 
   b <- checkWF mmi pc 
   when b $ do 
     putStrLn "The PC treee is as follows:" 
     putStrLn $ show_pctd $ consPCTD mmi pc []

check_MM :: (Eq a, Eq b, Show a, Show b, GNumSets a, GNodesNumConv a)=>MMI a b -> IO Bool
check_MM mmi = do
    let errs1 = faultsG "PCs_AMM" (Just Total) (gAMM mmi)
    unless (is_nil errs1) $ do 
        show_wf_msg "PCs abstract metamodel" errs1
    let errs2 = faultsG "PCs_MM" (Just Total) (gCMM mmi)
    unless (is_nil errs2) $ do 
        show_wf_msg "PCs concrete metamodel" errs2
    let errs3 = faultsGM "Refinement of PCs_MM by PCs_AMM " (Just TotalM) (gCMM mmi, gRM mmi, gAMM mmi)
    unless (not . is_nil $ errs3) $ do 
        show_wf_msg "PCs abstract metamodel" errs3
    return (all is_nil [errs1, errs2, errs3])

checkWF::MMI String String->PC String String->IO Bool
checkWF mmi pc = do
    let pc_nm = getPCDef pc
    let errs = faultsGM' pc_nm (Just TotalM) (pc, gCRSG mmi) 
    unless (is_nil errs) $ do
        show_wf_msg ("PC " ++ pc_nm) errs
    return (is_nil errs)


--wrCSPToFile :: FilePath -> String -> MMI String String -> PC String String -> IO ()
--wrCSPToFile pcs_path csp_path mmi pc = do
--   putStrLn "Writing the CSP file..." 
--   ias <- getImportedAtoms pcs_path (gCRSG mmi) pc 
--   is <-getImports pcs_path (gCRSG mmi) pc 
--   let (cspb, cspp, cspm) = mapT wrCSP (toCSP mmi pc ias is)
--   writeFile (csp_path ++ (getPCDef pc) ++ "_base.csp") cspb
--   writeFile (csp_path ++ (getPCDef pc) ++ "P.csp") cspp
--   writeFile (csp_path ++ (getPCDef pc) ++ ".csp") cspm

wrCSPToFile :: FilePath -> String -> MMI String String -> PC String String -> Env->IO ()
wrCSPToFile pcs_path csp_path mmi pc env = do
   putStrLn "Writing the CSP file..." 
   --ias <- getImportedAtoms pcs_path (gCRSG mmi) pc 
   let sg_mm = gCRSG mmi
   is <-getImports pcs_path sg_mm pc 
   forM is (\n-> do
      opc<-loadPC sg_mm (pcs_path ++ n ++".pc") 
      (if isSomething opc then
         wrCSPToFile pcs_path csp_path mmi (the opc) env
      else 
         return ()))
   let (cspb, cspp) = toCSP mmi pc is env
   writeFile (csp_path ++ (getPCDef pc) ++ "P.csp") (wrCSP cspp)
   writeFile (csp_path ++ (getPCDef pc) ++ ".csp") (wrCSP cspb)
   return ()


wrPCDrawingToFile ::String->MMI String String -> PC String String -> IO ()
wrPCDrawingToFile img_path mmi pc = do
    putStrLn "Writing the GraphViz file..." 
    let sg_mm = gCRSG mmi
    is <-getImports pcs_path sg_mm pc 
    forM_ is (\n-> do
      opc<-loadPC sg_mm (pcs_path ++ n ++".pc") 
      when (isSomething opc) $ do
          wrPCDrawingToFile img_path mmi (the opc))    
    writeDrawingToFile img_path mmi pc

--checkWFAndHealth pc m = do
--  b <- checkWF pc m 
--  if (not b) then
--    return b
--    else do
--      b'<- checkHealth pc m
--      return b'

showPCAsGwT _ _ _ _ pc = do
   putStrLn $ show pc

showAfterERel _ _ _ mmi pc = do 
  putStrLn $ show $ afterCRel mmi pc

showPCTree _ _ _ mmi pc = do
   putStrLn $ show_pctd $ consPCTD mmi pc []

showWithinRel _ _ _ mmi pc= do
   putStrLn $ show $ withinRel mmi pc

drawPCToFile _ img_path _ mmi pc = do
    wrPCDrawingToFile img_path mmi pc

writeCSPToFile :: FilePath -> p -> FilePath -> MMI String String -> PC String String -> Env->IO ()
writeCSPToFile pcs_path _ csp_path mmi pc env = 
   wrCSPToFile pcs_path csp_path mmi pc env >> putStrLn ""

--writeCSPToFile :: FilePath -> FilePath -> MMI String String -> PC String String -> IO ()
--writeCSPToFile pcs_path csp_path mmi pc = 
--   wrCSPToFile pcs_path csp_path mmi pc >> putStrLn ""


menuStr = "1 - show graph and morphism\n"
   ++ "2 - show after relation\n"
   ++ "3 - show PC Tree\n"
   ++ "4 - show PC's within relation\n"
   ++ "5 - draw PC's Graphviz code\n"
   ++ "6 - generate CSP\n"
   ++ "0 - quit\n"

--dispatch =  [ (1, showPCAsGwT) 
--            , (2, showAfterERel)  
--            , (3, showPCTree)
--            , (4, showWithinRel)
--            , (5, drawPCToFile)  
--            , (6, writeCSPToFile)  
--            ]  

--optionsPCs pcs_path img_path csp_path mmi pc = do
--    putStrLn menuStr
--    putStr "Which option? "  
--    optStr <- getLine 
--    let opt = (read optStr)
--    when (opt > 0 && opt <= 6) $ do
--       let (Just action) = lookup opt dispatch   
--       action pcs_path img_path csp_path mmi pc
--       optionsPCs pcs_path img_path csp_path mmi pc

loadAndCheck::String->String->MMI String String->IO (Maybe (PC String String))
loadAndCheck pcs_path fnm mmi = do
  opc <- loadPC (gCRSG mmi) (pcs_path ++ fnm)
  (if (isSomething opc) then do 
     b <- checkWF mmi (the opc)
     let is = importsOf (gCRSG mmi) (the opc)
     chs <- forM is (\n-> do 
       opc <- loadAndCheck pcs_path (n++".pc") mmi
       return $ isSomething opc)
     return (boolMaybe (all (== True) (b `intoSet` chs)) (the opc))
   else do
      return opc) >>= return

--askLoadAndOpsPCs :: MMI String String -> IO ()
--askLoadAndOpsPCs mmi = do
--  putStrLn "Name of directory with PC definitions? [enter for current directory]"
--  d <- getLine 
--  putStrLn "Name of PC file?"
--  fn <- getLine 
--  opc <- loadAndCheck d fn mmi
--  when (isSomething opc) $ do optionsPCs d (d++"img/") (d++"CSP/") mmi (the opc)

--startPCOps :: IO ()
--startPCOps = do
--    mmi<-load_mm_info mm_path
--    b <- check_MM mmi
--    if b
--        then askLoadAndOpsPCs mmi
--        else putStrLn "Errors in the metamodel definition."

outputDrawing :: String -> String -> p -> String -> MMI String String -> IO ()
outputDrawing pcs_path img_path csp_path fn mmi = do
   opc <- loadAndCheck pcs_path fn mmi
   when (isSomething opc) $ do drawPCToFile pcs_path img_path csp_path mmi (the opc) 

outputCSP :: FilePath -> FilePath -> FilePath -> String -> MMI String String -> Env-> IO ()
outputCSP pcs_path img_path csp_path fn mmi env = do
   opc <- loadAndCheck pcs_path fn mmi
   when (isSomething opc) $ writeCSPToFile pcs_path img_path csp_path mmi (the opc) env

check :: String -> MMI String String -> String -> IO ()
check pcs_path mmi fn = do
  loadAndCheck pcs_path fn mmi
  return ()

--main = startPCOps

loadPCs::Foldable t=>String -> MMI String String->t String->IO [PC String String]
loadPCs pcs_path mmi pcns = 
   foldM (\pcs pcn->do
           opc <-loadPC (gCRSG mmi) (pcs_path ++ pcn ++".pc") 
           return $ if isSomething opc then ((the opc):pcs) else pcs) [] pcns

typeCheckPC::MMI String String->PC String String->IO (Maybe Env)
typeCheckPC mmi pc = do 
   let is = importsOf (gCRSG mmi) pc
   pcs <-loadPCs pcs_path mmi is
   let pctd  = consPCTD mmi pc pcs
   putStrLn $ show_pctd pctd
   let (r, _) = runState (runExceptT $ typecheck_pctd pctd) 0
   if (isError r) then do 
      showResult r
      return Nothing
   else do
     return $ Just (gEnv r)
   where
      isError (Left _) = True
      isError _ = False
      gEnv (Right env) = env
      showResult (Left err) = putStrLn $ errorMsg err
   
   
check_generate :: String -> String -> String -> MMI String String -> String -> IO ()
check_generate pcs_path img_path csp_path mmi fn = do
   putStrLn $ "Processing '" ++ fn ++ "'" 
   opc <- loadAndCheck pcs_path fn mmi
   when (isSomething opc) $ do
      drawPCToFile pcs_path img_path csp_path mmi (the opc)
      oenv<-typeCheckPC mmi (the opc)
      if isNil (oenv) then do
         putStrLn $ "The PC is not type correct!"
      else do
         writeCSPToFile pcs_path img_path csp_path mmi (the opc) (the oenv)

generate_Clock :: MMI String String -> IO ()
generate_Clock mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_Clock.pc"

generate_Clock_ref :: MMI String String -> IO ()
generate_Clock_ref mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_Clock_ref.pc"

generate_GreetChat :: MMI String String -> IO ()
generate_GreetChat mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_GreetChat.pc"

generate_VM :: MMI String String -> IO ()
generate_VM mmi = do
  check_generate pcs_path img_path csp_path mmi "PC_VM.pc"

generate_VM2 :: MMI String String -> IO ()
generate_VM2 mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_VM2.pc"

generate_CCVM :: MMI String String -> IO ()
generate_CCVM mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_CCVM.pc"

generate_BreakStealHouse1 :: MMI String String -> IO ()
generate_BreakStealHouse1 mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_BreakStealHouse1.pc"

generate_BreakStealHouse2 :: MMI String String -> IO ()
generate_BreakStealHouse2 mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_BreakStealHouse2.pc"

generate_BreakStealHouse3 :: MMI String String -> IO ()
generate_BreakStealHouse3 mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_BreakStealHouse3.pc"

generate_BreakStealHouse4 :: MMI String String -> IO ()
generate_BreakStealHouse4 mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_BreakStealHouse4.pc"

generate_StealHouseTreasure :: MMI String String -> IO ()
generate_StealHouseTreasure mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_StealHouseTreasure.pc"

generate_HouseAlarm :: MMI String String -> IO ()
generate_HouseAlarm mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_HouseAlarm.pc"
  
generate_HouseLiving :: MMI String String -> IO ()
generate_HouseLiving mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_HouseLiving.pc"

generate_HouseUnderAttack :: MMI String String -> IO ()
generate_HouseUnderAttack mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_HouseUnderAttack_Snatch.pc"
   check_generate pcs_path img_path csp_path mmi "PC_HouseUnderAttack_Ransack.pc"
   check_generate pcs_path img_path csp_path mmi "PC_HouseUnderAttack.pc"

generate_SuccessfulHouseAttack :: MMI String String -> IO ()
generate_SuccessfulHouseAttack mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_SuccessfulHouseAttack.pc"

generate_UnnoticedAttack :: MMI String String -> IO ()
generate_UnnoticedAttack mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_UnnoticedAttack.pc"

generate_ProtectedHouse :: MMI String String -> IO ()
generate_ProtectedHouse mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_ProtectedHouse_HouseAlarm.pc"
    check_generate pcs_path img_path csp_path mmi "PC_ProtectedHouse.pc"

generate_SecureHouse :: MMI String String -> IO ()
generate_SecureHouse mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_SecureHouse.pc"

generate_HouseAttacker :: MMI String String -> IO ()
generate_HouseAttacker mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_HouseAttacker.pc"

generate_SecuredHouse :: MMI String String -> IO ()
generate_SecuredHouse mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_SecuredHouse.pc"


checkMMGenerateAll :: IO ()
checkMMGenerateAll = do
    mmi<-load_mm_info mm_path
    b <- check_MM mmi
    when b $ do
        generate "PC_Clock"
        generate "PC_Clock_ref"
        generate "PC_FaultyClock"
        generate "PC_GreetChat"
        generate "PC_VM"
        generate "PC_VM2"
        generate "PC_Bool"
        generate "PC_Bool2"
        generate "PC_BusRider" 
        generate "PC_ABusRide"
        generate "PC_CCVM"
        generate "PC_Timer"
        generate "PC_BiscuitJar"
        generate "PC_Buzzer"
        generate "PC_POS" -- From Hoare's book, p.156
        generate "PC_Panda1"
        generate "PC_Panda2"
        generate "PC_TicketMachine"
        generate "PC_SimpleLife"
        generate "PC_BreakStealHouse1"
        generate "PC_BreakStealHouse2"
        generate "PC_BreakStealHouse3"
        generate "PC_BreakStealHouse4"
        generate "PC_StealHouseTreasure"
        generate "PC_HouseUnderAttack"
        generate "PC_Lasbscs"
        generate "PC_HouseAttacker"
        generate "PC_HouseAlarm"
        generate "PC_CashMachine"
        generate "PC_ProtectedHouse"
        generate "PC_StopTimer"
        generate "PC_StopPauseTimer"
        generate "PC_SecuredHouse"
        generate "PC_BoolSetter"
        generate "PC_Authentication"
        generate "PC_MadTicker"
        generate "PC_OrderGoods"

load_check_show_tree :: MMI String String -> String -> IO ()
load_check_show_tree mmi fnm = do
    opc <- loadPC (gCRSG mmi) (pcs_path ++ fnm)
    when (isSomething opc) $ do
       b<-checkWF mmi (the opc)
       when b $ do
           let td = consPCTD mmi (the opc) [] -- Could change here
           putStrLn $ show_pctd td

generate :: String -> IO ()
generate fnm = do
  mmi<-load_mm_info mm_path
  check_generate pcs_path img_path csp_path mmi (fnm ++ ".pc")

showPCT :: String -> IO ()
showPCT fnm = do
  mmi<-load_mm_info mm_path
  opc <- loadPC (gCRSG mmi) (pcs_path ++ fnm ++ ".pc") 
  when (isSomething opc) $ do
     let is = importsOf (gCRSG mmi) (the opc)
     pcs <-loadPCs pcs_path mmi is
     putStrLn $ show_pctd $ consPCTD mmi (the opc) pcs

showTypePCT :: String -> IO ()
showTypePCT fnm = do
   mmi<-load_mm_info mm_path
   opc <- loadPC (gCRSG mmi) (pcs_path ++ fnm ++ ".pc") 
   when (isSomething opc) $ do
      typeCheckPC mmi (the opc) >>= putStrLn . show
      --when (isSomething oenv) $ putStrLn $ show (the oenv)
      return ()
      --is<-getImports pcs_path (gCRSG mmi) (the opc)
      --let pctd  = consPCTD mmi (the opc)
      --putStrLn $ show_pctd pctd
      --putStrLn $ show $ runState (runExceptT $ typecheck_pctd pctd) 0
   --where
   --   showResult (Left err, _) = putStrLn $ errorMsg err

main :: IO ()
main = do
  args <- getArgs
  generate (head args ++ ".pc")

test :: IO ()
test = do 
   --showTypePCT "PC_TCellActivation"
   --showTypePCT "PC_Authentication"
   --showTypePCT "PC_Timer"
   --showTypePC "PC_CCVM"
   --showTypePCT "PC_Buzzer"
   --showTypePCT "PC_HouseLiving"
   mmi<-load_mm_info mm_path
   opc<-loadPC (gCRSG mmi) (pcs_path ++ "PC_HouseLiving_err.pc")
   putStrLn $ "Start K: " ++ show (startCompound mmi (the opc))
   let pctd = consPCTD mmi (the opc) []
   putStrLn $ show_pctd  pctd
   --opc<-loadPC (gCRSG mmi) (pcs_path ++ "PC_HouseLiving.pc")
   --putStrLn $ show $ nmOfRefF mmi (the opc) "RefEnterHall"
   --putStrLn $ show pds
   --putStrLn $ show_pctd  pctd
   --putStrLn $ show $ innerRefKs mmi (the opc) "PositiveSignallingOn"
   --putStrLn $ show $ innerKs mmi (the opc) "PositiveSignallingOn"
   --atLeaf (the opc) "freeLigandTCR2"
   --putStrLn $ "Expression of atom: " ++ show (expOfAtom (the opc) "showBal")
   --print $ expsOf (the opc) "OpPosSigOff"
   --print $ nextNode mmi (the opc) "OpPosSigOff" 
   --putStrLn $ "Expression of atom: " ++ show (expOfAtom (the opc) "ShowBal")
   --putStrLn $ "Inner referenced compunds: " ++ (show $ innerRefKs mmi (the opc) "BiscuitJar")
   --putStrLn $ "Referenced compunds: " ++ (show $ refKs mmi (the opc) "BiscuitJar")
   --load_check_show_tree mmi "PC_Buzzer.pc"
   --generate_BiscuitJar mmi
   --generate_TicketMachine mmi
   --generate_BusRider mmi
   -- opc <- loadPC (gCRSG mmi) (pcs_path ++ "PC_BiscuitJar.pc")
   -- let pc = the opc
   --let pctd  = consPCTD mmi pc 
   -- print pctd
   -- print $ runState (runExceptT $ typecheck_pctd pctd) 0
    --print $ paramsOf pc "Timer"
    --print $ img (tgt pc) $ img (inv $ src pc) ["Timer"] `intersec` es_of_ety pc (show_cmm_e CMM_Eparams)
    --print $ tyOfParam pc "Timer_param_1_t"
    --print $ img (inv . src $ pc) ["Timer_param_1_t"] `intersec`  es_of_ety pc (show_cmm_e CMM_Etype)
    --print pc
    --print $ fmap (the . parsePCExp) (strOfTxtExps (expsOf pc "OpTimer"))
    --print $ expsOf pc "OpIfChoice"
    --print $ (parsePCExp . str_of_ostr) (guardOfOp mmi pc "OpTimer")
    --print $ branchesOfOp mmi pc "OpIfChoice"
    --print $ fmap (the . parsePCExp) (strOfTxtExps $ expsOf pc "OpIfChoice")
    --print $ opValOfOp (gCRSG mmi) pc "OpIfChoice"
    --print $ nextNode mmi pc "COpIfChoice_timeout"
    --print $ guardOf pc "timeout"
    --print $ img (tgt pc) $ img (inv $ src pc) ["steal"] `intersec` es_of_ety pc (show_cmm_e CMM_Eexps)
    --print $ nextNode mmi pc "COpIfChoice_timeout"
    --print env
    --print $ atomsPCTD pctd
    --putStrLn $ show $ nextKsOf mmi (the opc)  "Buzzing"
    --putStrLn $ nextNodes mmi pc n
    --putStrLn $ show_pctd $ consPCTD mmi (the opc)
    --print $ isNodeOfTys "Bool" [CMM_Compound] (gCRSG mmi) (the opc)
    --putStrLn $ show $ compoundStart mmi (the opc)  "Bool"
    --putStrLn $ show $ nextNodesAfter mmi (the opc)  "Bool"
    --putStrLn $ "Next nodes of " ++ "OpBreakAndStealHouse" ++ ":" ++ (show $ nextNodes mmi (the opc) "OpBreakAndStealHouse")
    --putStrLn $ "Inner Ks of "  ++ "BreakAndStealHouse" ++ ":" ++ (show $ innerKs mmi (the opc) "BreakAndStealHouse")
    --putStrLn $ "Inner Ref Ks of "  ++ "BreakAndStealHouse" ++ ":" ++ (show $ innerRefKs mmi (the opc) "BreakAndStealHouse")
    --putStrLn $ "Start K: " ++ show (startCompound mmi (the opc))
    --putStrLn $ "Common Inner ks: " ++ show (commonInnerKs mmi (the opc) "BreakAndStealHouse")
    --putStrLn $ show $ compoundAB mmi (the opc) "BreakAndStealHouse" nil
    --putStrLn $ "Withrel: " ++ show (withinRel mmi (the opc))
    --putStrLn $ "Next nodes of 'BreakAndStealHouse':" ++ show (nextNodes mmi (the opc) "BreakAndStealHouse")
    --putStrLn $ "Next nodes of 'OpBreakAndStealHouse':" ++ show (nextNodes mmi (the opc) "OpBreakAndStealHouse")
    --putStrLn $ "Next nodes of 'OpBurglary':" ++ show (nextNodes mmi (the opc) "OpBurglary")
    --putStrLn $ "Next nodes after 'BreakAndStealHouse':" ++ show (nextNodesAfter mmi (the opc) "BreakAndStealHouse")
    --putStrLn $ "NextKsOf 'BreakAndStealHouse':" ++ show (nextKsOf mmi (the opc) "BreakAndStealHouse")
    --putStrLn $ "NextKsOf 'Alarm':" ++ show (nextKsOf mmi (the opc) "Alarm")
    --putStrLn $ "NextKsOf 'DoBurglary':" ++ show (nextKsOf mmi (the opc) "DoBurglary")
    --putStrLn $ "NextKsOf 'RunAway':" ++ show (nextKsOf mmi (the opc) "RunAway")
    --putStrLn $ "NextKsOf 'GetInside':" ++ show (nextKsOf mmi (the opc) "GetInside")
    --putStrLn $ "NextKsOf 'Steal':" ++ show (nextKsOf mmi (the opc) "Steal")
    --putStrLn $ "RelKs: " ++ show (relKs mmi (the opc))
    --putStrLn $ "Inner Ks of "  ++ "BreakAndStealHouse" ++ ":" ++ (show $ innerKs mmi (the opc) "BreakAndStealHouse")
    --checkWFAndGeneratePCTree mmi (the opc)
    --print $ toPCDrawing mmi (the opc) 
    --print $ paramsOf (the opc) "BiscuitJar"
    --let pc = the opc
    --print pc
    --print $ img (tgt pc) $ img (inv $ src pc) ["CRefSnatchControl"] `intersec` es_of_ety pc (show_cmm_e CMM_Ebindings)
    --print $ img (tgt pc) $ img (inv $ src pc) ["CRefSnatchControl_binding_1"] `intersec` es_of_ety pc (show_cmm_e CMM_Evals) 
    --print $ img (inv $ src pc) ["seize"] `intersec` es_of_ety pc (show_cmm_e CMM_Ebindings)
    --print $ img (tgt pc) $ img (inv $ src pc) ["RefHouseAlarm"] `intersec` es_of_ety pc (show_cmm_e CMM_Ebindings)
    --print $ pbindings pc $ img (tgt pc) $ img (inv $ src pc) ["RefHouseAlarm"] `intersec` es_of_ety pc (show_cmm_e CMM_Ebindings)
    --print $ img (tgt (the opc)) $ img (inv $ src (the opc)) ["CRefJarOpenedDrop"] `intersec` es_of_ety (the opc) (show_cmm_e CMM_Ebindings)
    --print $ img (tgt (the opc)) $ img (inv $ src (the opc)) ["BiscuitJar"] `intersec`  es_of_ety (the opc)  (show_cmm_e CMM_EHasParams)
    --is<-getImports pcs_path (gCRSG mmi) pc
    --putStrLn $ show is
    --generate_Timer mmi
    --generate_CashMachineOps mmi
    --generate_HouseUnderAttack mmi
    --generate_HouseAttacker mmi
    --generate_SecuredHouse mmi
    --generate_HouseAlarm mmi
    --generate_ProtectedHouse mmi
    --generate_SuccessfulHouseAttack mmi
    --generate_SecureHouse mmi
    --let pc = the opc
    --let sg = gCRSG mmi
    --print $ rMultOk sg (show_cmm_e CMM_ERenamings) pc
    --print $ img (inv . fE $ pc) [show_cmm_e CMM_ERenamings]
    --print $ img (srcst sg) [show_cmm_e CMM_ERenamings]
    --pc <- loadPC (gCRSG mmi) (pcs_path ++ "PC_GreetChat.pc")
    --putStrLn $ tyOfN "OpChat" pc
    --putStrLn $ tyOfN "OpChoice_Val" pc
    --print $ isNodeOfTys "OpChoice_Val" [CMM_Operator] (gCRSG mmi) pc
    --putStrLn $ show $ appl (fV pc) $ appl (tgt pc) (first $ img (inv $ src pc) ["OpChat"] `intersec` es_of_ety pc (show_cmm_e CMM_ECombination_op))
    --putStrLn $ show $ opValOfOp (gCRSG mmi) pc "OpChat"
    --putStrLn $ show $ inner_Ref pc "RefGive"
    --putStrLn $ show $ nmOfRefF mmi pc "RefGive"
    --putStrLn $ "Inner ks: " ++ (show $ innerKs mmi pc "SecuredHouse")
    --putStrLn $ "Common Inner ks: " ++ (show $ commonInnerKs mmi pc "GetandGive")
    --putStrLn $ "Inner ps: " ++ (show $ innerRefKs mmi pc "SecuredHouse")
    --pc <- loadPC (gCRSG mmi) (pcs_path ++ "PC_HouseAttacker.pc")
    --putStrLn $ show $ commonInnerKs mmi pc (startCompound mmi pc)
    --putStrLn $ show $ nextNodes mmi pc "OpChat"
    --generate_PC_SimpleLife mmi
    --generate_PC_Bool mmi
   
    --putStrLn $ show $ paramsOfRef mmi pc "RefLive"
    --putStrLn $ show $ (successorsOf mmi pc "RefTimer") `intersec` (pc_ns_of_nty (gCRSG mmi) pc CMM_ReferenceC)
    --putStrLn $ show $ successorsOf mmi pc "CRefTimer"
    --putStrLn $ show $ nextNodeAfter mmi pc "RefTimer"
    --putStrLn $ show $ isNodeOfTy "Timer" CMM_Compound (gCRSG mmi) pc
    --generate_PC_Lasbscs mmi 
    --generate_PC_GreetChat mmi
    --generate_PC_CashMachine mmi
    --pc <- loadPC (gCRSG mmi) (pcs_path ++ "PC_Clock.pc")
    --b<-checkWF mmi pc 