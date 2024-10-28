
import Gr_Cls
import PCs.PCsParsing
import PCs.PCs
import CheckUtils
import PCs.PCs_MM_Names
import MyMaybe
import NumString
import TheNil
import MMI

pcs_path :: String
pcs_path = "PCs/PCs/"
def_path :: String
def_path = "PCs/MM/"

tst_1 :: IO ()
tst_1 = do
    mmi<-load_mm_info def_path
    opc<-loadPC (gCRSG mmi) (pcs_path ++ "PC_Clock.pc") 
    -- Checks whether the PC is well formed
    check_ty_morphism (getPCDef $ the opc) (Just TotalM) (the opc) (gCRSG mmi) True
    --putStrLn $ show $ startCompound mmi pc 
    --putStrLn $ show $ getPCStart (pc_sg_cmm mmi) pc 
    --putStrLn $ show $ afterCRel mmi pc 
    --putStrLn $ show $ nmOfNamed pc $ startCompound mmi pc 
    --putStrLn $ show $ pc_ns_of_nty (pc_sg_cmm mmi) pc CMM_AfterC
    --putStrLn $ show $ withinRel mmi pc