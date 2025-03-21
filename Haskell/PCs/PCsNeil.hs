module PCs.PCsNeil where
import PCs.PCs ( load_mm_info )
import PCs.PCsParsing (loadPC)
import TheNil
import PCs.PCTrees
import Control.Monad(when)
import MMI (gCRSG)

mm_path :: String
mm_path = "PCs/MM/"
pcs_path :: String
pcs_path = "PCs/Examples/"

-- Interesting PCs in general: PC_Clock, PC_Clock_ref, PC_VM, PC_VM2, PC_Bool, PC_Bool2, PC_POS
-- Interesting PCs for type-checking: 'PC_Timer.pc', 'PC_BiscuitJar.pc', 'PC_CCVM.pc', 'PC_Buzzer.pc'

main :: IO ()
main = do
    mmi<-load_mm_info mm_path
    opc <- loadPC (gCRSG mmi) (pcs_path ++ "PC_Timer.pc")
    when (isSomething opc) $ do
        let pc = the opc
        let pctd = consPCTD mmi pc
        putStrLn $ show_pctd pctd