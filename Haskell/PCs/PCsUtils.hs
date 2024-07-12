
---------------------
-- Project: PCs/Utils
-- Module: 'PCsUtils'
-- Description: Utilities module of PCs
-- Author: Nuno Amálio
--------------------
module PCs.PCsUtils(writeCSPToFile, checkWFAndGeneratePCTree, checkWF, optionsPCs, startPCOps, 
   outputDrawing, outputCSP) where

import Gr_Cls
import PCs.PCs
import SGrs
import GrswT
import PCs.ToCSP
import PCs.PCTrees
import CSPPrint
import System.IO
import Control.Monad(when, forM, unless)
import PCs.PCsDraw
import PCs.PCsParsing
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
      (if (isSomething opc) then do
         as <- getImportedAtoms pcs_path sg_mm (the opc)
         return (as `union` set (getAtoms sg_mm (the opc)))
      else do
        return nil) >>= return)
   return (gunion as)


getImports::FilePath->SGr String String->PC String String->IO (Set String)
getImports pcs_path sg_mm pc = do
   let is = importsOf sg_mm pc
   is <- forM is (\n-> do 
      opc<-loadPC sg_mm (pcs_path ++ n ++".pc") 
      (if (isSomething opc) then do
         is' <- getImports pcs_path sg_mm (the opc)
         let is_ = importsOf sg_mm (the opc)
         return (is `union` (is' `union` is_))
      else do
         return nil) >>= return)
   return (gunion is)

writeDrawingToFile img_path mmi pc = do
   let draw_src = wrPCAsGraphviz mmi pc  
   writeFile (img_path ++ (getPCDef pc) ++ ".gv") draw_src

--writePCDef pc m = 
--   let pc_txt = wrPC $ frPCtoPCNot pc m in
--   writeFile ("pcs/"++ (getPCDef m) ++ ".pc") pc_txt

checkWFAndGeneratePCTree :: MMInfo String String -> PC String String -> IO ()
checkWFAndGeneratePCTree mmi pc = do 
   b <- checkWF mmi pc 
   when b $ do 
     putStrLn "The PC treee is as follows:" 
     putStrLn $ show_pctd $ consPCTD mmi pc

check_MM :: (Eq a, Eq b, Show a, Show b, GNumSets a, GNodesNumConv a)=>MMInfo a b -> IO Bool
check_MM mmi = do
    let errs1 = faultsG "PCs_AMM" (Just Total) (pc_amm mmi)
    unless (is_nil errs1) $ do 
        show_wf_msg "PCs abstract metamodel" errs1
    let errs2 = faultsG "PCs_MM" (Just Total) (pc_cmm mmi)
    unless (is_nil errs2) $ do 
        show_wf_msg "PCs concrete metamodel" errs2
    let errs3 = faultsGM "Refinement of PCs_MM by PCs_AMM " (Just TotalM) (pc_cmm mmi, pc_rm mmi, pc_amm mmi)
    unless (not . is_nil $ errs3) $ do 
        show_wf_msg "PCs abstract metamodel" errs3
    return (all is_nil [errs1, errs2, errs3])

checkWF::MMInfo String String->PC String String->IO(Bool)
checkWF mmi pc = do
    let pc_nm = getPCDef pc
    let errs = faultsGM' pc_nm (Just TotalM) (pc, pc_cmm mmi) 
    unless (is_nil errs) $ do
        show_wf_msg ("PC " ++ pc_nm) errs
    return (is_nil errs)


wrCSPToFile :: FilePath -> String -> MMInfo String String -> PC String String -> IO ()
wrCSPToFile pcs_path csp_path mmi pc = do
   putStrLn "Writing the CSP file..." 
   ias <- getImportedAtoms pcs_path (pc_sg_cmm mmi) pc 
   is <-getImports pcs_path (pc_sg_cmm mmi) pc 
   let (cspb, cspp, cspm) = mapT wrCSP (toCSP mmi pc ias is)
   writeFile (csp_path ++ (getPCDef pc) ++ "_base.csp") cspb
   writeFile (csp_path ++ (getPCDef pc) ++ "P.csp") cspp
   writeFile (csp_path ++ (getPCDef pc) ++ ".csp") cspm


wrPCDrawingToFile ::String->MMInfo String String -> GrwT String String -> IO ()
wrPCDrawingToFile img_path mmi pc = do
    putStrLn "Writing the GraphViz file..." 
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
   putStrLn $ show_pctd $ consPCTD mmi pc

showWithinRel _ _ _ mmi pc= do
   putStrLn $ show $ withinRel mmi pc

drawPCToFile _ img_path _ mmi pc = do
    wrPCDrawingToFile img_path mmi pc

writeCSPToFile pcs_path _ csp_path mmi pc = do
   wrCSPToFile pcs_path csp_path mmi pc


menuStr = "1 - show graph and morphism\n"
   ++ "2 - show after relation\n"
   ++ "3 - show PC Tree\n"
   ++ "4 - show PC's within relation\n"
   ++ "5 - draw PC's Graphviz code\n"
   ++ "6 - generate CSP\n"
   ++ "0 - quit\n"

dispatch =  [ (1, showPCAsGwT) 
            , (2, showAfterERel)  
            , (3, showPCTree)
            , (4, showWithinRel)
            , (5, drawPCToFile)  
            , (6, writeCSPToFile)  
            ]  

optionsPCs pcs_path img_path csp_path mmi pc = do
    putStrLn menuStr
    putStr "Which option? "  
    optStr <- getLine 
    let opt = (read optStr)
    when (opt > 0 && opt <= 6) $ do
       let (Just action) = lookup opt dispatch   
       action pcs_path img_path csp_path mmi pc
       optionsPCs pcs_path img_path csp_path mmi pc

loadAndCheck::String->String->MMInfo String String->IO (Maybe (PC String String))
loadAndCheck pcs_path fnm mmi = do
  opc <- loadPC (pc_sg_cmm mmi) (pcs_path ++ fnm)
  (if (isSomething opc) then do 
     b <- checkWF mmi (the opc)
     let is = importsOf (pc_sg_cmm mmi) (the opc)
     chs <- forM is (\n-> do 
       opc <- loadAndCheck pcs_path (n++".pc") mmi
       return $ isSomething opc)
     return (boolMaybe (all (== True) (b `intoSet` chs)) (the opc))
   else do
      return opc) >>= return

askLoadAndOpsPCs mmi = do
  putStrLn "Name of directory with PC definitions? [enter for current directory]"
  d <- getLine 
  putStrLn "Name of PC file?"
  fn <- getLine 
  opc <- loadAndCheck d fn mmi
  when (isSomething opc) $ do optionsPCs d (d++"img/") (d++"CSP/") mmi (the opc)

startPCOps = do
    mmi<-load_mm_info mm_path
    b <- check_MM mmi
    if b
        then askLoadAndOpsPCs mmi
        else putStrLn "Errors in the metamodel definition."

outputDrawing pcs_path img_path csp_path fn mmi = do
   opc <- loadAndCheck pcs_path fn mmi
   when (isSomething opc) $ do drawPCToFile pcs_path img_path csp_path mmi (the opc) 

outputCSP pcs_path img_path csp_path fn mmi = do
   opc <- loadAndCheck pcs_path fn mmi
   when (isSomething opc) $ do writeCSPToFile pcs_path img_path csp_path mmi (the opc) 

check :: String -> MMInfo String String -> String -> IO ()
check pcs_path mmi fn = do
  loadAndCheck pcs_path fn mmi
  return ()

--main = startPCOps

check_generate :: String -> String -> String -> MMInfo String String -> String -> IO ()
check_generate pcs_path img_path csp_path mmi fn = do
   putStrLn $ "Processing '" ++ fn ++ "'" 
   opc <- loadAndCheck pcs_path fn mmi
   when (isSomething opc) $ do
      drawPCToFile pcs_path img_path csp_path mmi (the opc)
      wrCSPToFile pcs_path csp_path mmi (the opc)

generate_Clock :: MMInfo String String -> IO ()
generate_Clock mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_Clock.pc"

generate_Clock_ref :: MMInfo String String -> IO ()
generate_Clock_ref mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_Clock_ref.pc"

generate_GreetChat :: MMInfo String String -> IO ()
generate_GreetChat mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_GreetChat.pc"

generate_VM :: MMInfo String String -> IO ()
generate_VM mmi = do
  check_generate pcs_path img_path csp_path mmi "PC_VM.pc"

generate_VM2 :: MMInfo String String -> IO ()
generate_VM2 mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_VM2.pc"

generate_CCVM :: MMInfo String String -> IO ()
generate_CCVM mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_CCVM.pc"

generate_BreakStealHouse1 :: MMInfo String String -> IO ()
generate_BreakStealHouse1 mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_BreakStealHouse1.pc"

generate_BreakStealHouse2 :: MMInfo String String -> IO ()
generate_BreakStealHouse2 mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_BreakStealHouse2.pc"

generate_BreakStealHouse3 :: MMInfo String String -> IO ()
generate_BreakStealHouse3 mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_BreakStealHouse3.pc"

generate_BreakStealHouse4 :: MMInfo String String -> IO ()
generate_BreakStealHouse4 mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_BreakStealHouse4.pc"

generate_StealHouseTreasure :: MMInfo String String -> IO ()
generate_StealHouseTreasure mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_StealHouseTreasure.pc"

generate_HouseAlarm :: MMInfo String String -> IO ()
generate_HouseAlarm mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_HouseAlarm.pc"
  
generate_HouseLiving :: MMInfo String String -> IO ()
generate_HouseLiving mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_HouseLiving.pc"

generate_HouseUnderAttack :: MMInfo String String -> IO ()
generate_HouseUnderAttack mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_HouseUnderAttack_Snatch.pc"
   check_generate pcs_path img_path csp_path mmi "PC_HouseUnderAttack_Ransack.pc"
   check_generate pcs_path img_path csp_path mmi "PC_HouseUnderAttack.pc"

generate_SuccessfulHouseAttack :: MMInfo String String -> IO ()
generate_SuccessfulHouseAttack mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_SuccessfulHouseAttack.pc"

generate_UnnoticedAttack :: MMInfo String String -> IO ()
generate_UnnoticedAttack mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_UnnoticedAttack.pc"

generate_ProtectedHouse :: MMInfo String String -> IO ()
generate_ProtectedHouse mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_ProtectedHouse_HouseAlarm.pc"
    check_generate pcs_path img_path csp_path mmi "PC_ProtectedHouse.pc"

generate_SecureHouse :: MMInfo String String -> IO ()
generate_SecureHouse mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_SecureHouse.pc"

generate_HouseAttacker :: MMInfo String String -> IO ()
generate_HouseAttacker mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_HouseAttacker.pc"

generate_SecuredHouse :: MMInfo String String -> IO ()
generate_SecuredHouse mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_SecuredHouse.pc"

-- generate_HouseMovement mmi = do
--   check_generate pcs_path img_path csp_path mmi "PC_HouseMovement.pc"

generate_Bool :: MMInfo String String -> IO ()
generate_Bool mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_Bool.pc"

generate_Bool2 :: MMInfo String String -> IO ()
generate_Bool2 mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_Bool2.pc"

generate_BoolSetter :: MMInfo String String -> IO ()
generate_BoolSetter mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_BoolSetter.pc"

generate_Lasbscs :: MMInfo String String -> IO ()
generate_Lasbscs mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_Lasbscs.pc"

generate_Timer :: MMInfo String String -> IO ()
generate_Timer mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_Timer.pc"

generate_SimpleLife :: MMInfo String String -> IO ()
generate_SimpleLife mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_SimpleLife.pc"

generate_BiscuitJar :: MMInfo String String -> IO ()
generate_BiscuitJar mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_BiscuitJar.pc"

generate_CardReader :: MMInfo String String -> IO ()
generate_CardReader mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_CardReader.pc"

generate_Authentication :: MMInfo String String -> IO ()
generate_Authentication mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_Authentication.pc"

generate_CashMachine :: MMInfo String String -> IO ()
generate_CashMachine mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_CashMachine.pc"

generate_BusRider :: MMInfo String String -> IO ()
generate_BusRider mmi = do
   check_generate pcs_path img_path csp_path mmi "PC_BusRider.pc"

generate_ABusRide :: MMInfo String String -> IO ()
generate_ABusRide mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_ABusRide.pc"

generate_Withdraw :: MMInfo String String -> IO ()
generate_Withdraw mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_Withdraw.pc"

generate_ShowBalance :: MMInfo String String -> IO ()
generate_ShowBalance mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_ShowBalance.pc"

generate_DoCancel :: MMInfo String String -> IO ()
generate_DoCancel mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_DoCancel.pc"

generate_CashMachineOps :: MMInfo String String -> IO ()
generate_CashMachineOps mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_CashMachineOps.pc"

generate_MadTicker :: MMInfo String String -> IO ()
generate_MadTicker mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_MadTicker.pc"

generate_TicketMachine :: MMInfo String String -> IO ()
generate_TicketMachine mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_TicketMachine.pc"

generate_OrderGoods :: MMInfo String String -> IO ()
generate_OrderGoods mmi = do
    check_generate pcs_path img_path csp_path mmi "PC_OrderGoods.pc"

generate_POS :: MMInfo String String -> IO ()
generate_POS mmi = do -- From Hoare's book, p.156
    check_generate pcs_path img_path csp_path mmi "PC_POS.pc"

generate_Buzzer :: MMInfo String String -> IO ()
generate_Buzzer mmi = 
    check_generate pcs_path img_path csp_path mmi "PC_Buzzer.pc"

generateAll :: IO ()
generateAll = do
    mmi<-load_mm_info mm_path
    b <- check_MM mmi
    when b $ do
        generate_Clock mmi
        generate_Clock_ref mmi
        generate_GreetChat mmi
        generate_VM mmi
        generate_VM2 mmi
        generate_Bool mmi
        generate_Bool2 mmi
        generate_BusRider mmi 
        generate_ABusRide mmi
        generate_CCVM mmi
        generate_Timer mmi
        generate_BiscuitJar mmi
        generate_Buzzer mmi
        generate_BreakStealHouse1 mmi
        generate_BreakStealHouse2 mmi
        generate_BreakStealHouse3 mmi
        generate_BreakStealHouse4 mmi
        generate_StealHouseTreasure mmi
        generate_HouseUnderAttack mmi
        generate_HouseAttacker mmi
        generate_HouseAlarm mmi
        generate_ProtectedHouse mmi
        generate_SecuredHouse mmi
        generate_BoolSetter mmi
        generate_Lasbscs mmi 
        generate_SimpleLife mmi
        generate_CardReader mmi
        generate_Authentication mmi
        generate_ShowBalance mmi
        generate_Withdraw mmi
        generate_DoCancel mmi
        generate_CashMachine mmi
        generate_CashMachineOps mmi
        generate_MadTicker mmi 
        generate_POS mmi
        generate_TicketMachine mmi
        generate_OrderGoods mmi

load_check_show_tree :: MMInfo String String -> String -> IO ()
load_check_show_tree mmi fnm = do
    opc <- loadPC (pc_sg_cmm mmi) (pcs_path ++ fnm)
    when (isSomething opc) $ do
       b<-checkWF mmi (the opc)
       when b $ do
           let td = consPCTD mmi (the opc) 
           putStrLn $ show_pctd td

generate :: String -> IO ()
generate fnm = do
  mmi<-load_mm_info mm_path
  check_generate pcs_path img_path csp_path mmi (fnm ++ ".pc")

main :: IO ()
main = do
  args <- getArgs
  generate (head args ++ ".pc")

test :: IO ()
test = do 
    mmi<-load_mm_info mm_path
    --load_check_show_tree mmi "PC_Buzzer.pc"
    generate_Timer mmi
    generate_Buzzer mmi
    --generate_BusRider mmi
    -- opc <- loadPC (pc_sg_cmm mmi) (pcs_path ++ "PC_Buzzer.pc")
    --print $ isNodeOfTys "Bool" [CMM_Compound] (pc_sg_cmm mmi) (the opc)
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
    --print (the opc) 
    --print $ paramsOf (the opc) "BiscuitJar"
    --print $ img (tgt (the opc)) $ img (inv $ src (the opc)) ["BiscuitJar"] `intersec`  es_of_ety (the opc)  (show_cmm_e CMM_EHasParams)
    --is<-getImports pcs_path (pc_sg_cmm mmi) pc
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
    --let sg = pc_sg_cmm mmi
    --print $ rMultOk sg (show_cmm_e CMM_ERenamings) pc
    --print $ img (inv . fE $ pc) [show_cmm_e CMM_ERenamings]
    --print $ img (srcst sg) [show_cmm_e CMM_ERenamings]
    --pc <- loadPC (pc_sg_cmm mmi) (pcs_path ++ "PC_GreetChat.pc")
    --putStrLn $ tyOfN "OpChat" pc
    --putStrLn $ tyOfN "OpChoice_Val" pc
    --print $ isNodeOfTys "OpChoice_Val" [CMM_Operator] (pc_sg_cmm mmi) pc
    --putStrLn $ show $ appl (fV pc) $ appl (tgt pc) (first $ img (inv $ src pc) ["OpChat"] `intersec` es_of_ety pc (show_cmm_e CMM_ECombination_op))
    --putStrLn $ show $ opValOfOp (pc_sg_cmm mmi) pc "OpChat"
    --putStrLn $ show $ inner_Ref pc "RefGive"
    --putStrLn $ show $ nmOfRefF mmi pc "RefGive"
    --putStrLn $ "Inner ks: " ++ (show $ innerKs mmi pc "SecuredHouse")
    --putStrLn $ "Common Inner ks: " ++ (show $ commonInnerKs mmi pc "GetandGive")
    --putStrLn $ "Inner ps: " ++ (show $ innerRefKs mmi pc "SecuredHouse")
    --pc <- loadPC (pc_sg_cmm mmi) (pcs_path ++ "PC_HouseAttacker.pc")
    --putStrLn $ show $ commonInnerKs mmi pc (startCompound mmi pc)
    --putStrLn $ show $ nextNodes mmi pc "OpChat"
    --generate_PC_SimpleLife mmi
    --generate_PC_Bool mmi
    --pc <- loadPC (pc_sg_cmm mmi) (pcs_path ++ "PC_SimpleLife.pc")
    --putStrLn $ show $ nmOfRefF mmi pc "RefLive"
    --putStrLn $ show $ paramsOfRef mmi pc "RefLive"
    --putStrLn $ show $ (successorsOf mmi pc "RefTimer") `intersec` (pc_ns_of_nty (pc_sg_cmm mmi) pc CMM_ReferenceC)
    --putStrLn $ show $ successorsOf mmi pc "CRefTimer"
    --putStrLn $ show $ nextNodeAfter mmi pc "RefTimer"
    --putStrLn $ show $ isNodeOfTy "Timer" CMM_Compound (pc_sg_cmm mmi) pc
    --generate_PC_Lasbscs mmi 
    --generate_PC_GreetChat mmi
    --generate_PC_CashMachine mmi
    --pc <- loadPC (pc_sg_cmm mmi) (pcs_path ++ "PC_Clock.pc")
    --b<-checkWF mmi pc 
    --when b $ do
    --    let n = startCompound mmi pc 
    --    putStrLn $ show $ nextNodeAfter mmi pc n
    --    let (t, _, _) = consPCTNode mmi pc n nil_guard []
    --    putStrLn $ show t
    --load_check_show_tree mmi "PC_Clock.pc"
    --load_check_show_tree mmi "PC_BreakStealHouse1.pc"
    --load_check_show_tree mmi "GreetChat.pc"
    --load_check_show_tree mmi "PC_BreakStealHouse2.pc"
    --load_check_show_tree mmi "PC_Bool.pc"
--  when b $ do
--    let t = consPCTree mmi pc 
--    putStrLn $ show t
  --let csp = genCSPDecl t
  --putStrLn $ show csp
  --putStrLn $ show $ generatePCTree pc tm 
  --putStrLn $ show $ generateForOperator pc tm "OpProcessAuthenticate" ["ATM", "ProcessAuthenticate"]
  --putStrLn $ show $ nextNodesInPC pc tm "ProcessAuthenticate"
  --putStrLn $ show $ withinRelWith' pc tm "ATM" []
  --putStrLn $ show $ withinRelOfPC pc tm
  --putStrLn $ show $ drawPC pc tm 
  --putStrLn $ show $ withinRelOfPC pc tm
  --putStrLn $ show $ withinRelWith' pc tm "Bool" []
  --putStrLn $ show $ nextNodesInPC pc tm "BoolT"
  --putStrLn $ show $ nextNodesInPC pc tm "OpBoolT"
  --putStrLn $ show $ withinRelWith' pc tm "BoolT" ["Bool"]
  --putStrLn $ show $ withinRelWithAux pc tm "BoolT" "getT" ["Bool"]
  --putStrLn $ show $ withinRelWithAux pc tm "BoolT" "RefBool" ["Bool"]
  --putStrLn $ show $ typeOfN "OpChooseGive" tm 
  --putStrLn $ show $ getOpVal pc tm "OpChoiceVal"
  --putStrLn $ show $ getOperatorOp pc tm "OpChooseGive"
  --putStrLn $ show $ getOperatorOp pc tm "OpChooseGive"
  --putStrLn $ show pc
  --b<-checkWF pc tm
  --putStrLn $ show $ getPCStartCompound pc tm 