module PCs.PCsNeil where
import PCs.PCs ( load_mm_info, pc_sg_cmm )
import PCs.PCsParsing (loadPC)
import TheNil
import PCs.PCTrees
import Control.Monad(when)

mm_path :: String
mm_path = "PCs/MM/"
pcs_path :: String
pcs_path = "PCs/Examples/"

-- Interesting PCs for type-checking: 'PC_Timer.pc', 'PC_BiscuitJar.pc', 'PC_CCVM.pc', 'PC_Buzzer.pc'

main :: IO ()
main = do
    mmi<-load_mm_info mm_path
    opc <- loadPC (pc_sg_cmm mmi) (pcs_path ++ "PC_Timer.pc")
    when (isSomething opc) $ do
        let pc = the opc
        let pctd = consPCTD mmi pc
        putStrLn $ show_pctd pctd