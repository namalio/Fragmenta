------------------
-- Project: PCs/Fragmenta
-- Description: Generates haskell files with names used in metamodel, useful for typing
-- Author: Nuno Amálio
-----------------
import Gr_Cls
import Mdls 
import LoadCheckDraw
import CheckUtils
import Utils
import Grs
import SGrs
import Frs
import ShowUtils
import Sets

def_path = "IntoSysML/MM/"
wr_path = "IntoSysML/"

code_preamble_amm = "module IntoSysML.AMM_Names (IntoSysML_AMM_Ns(..), IntoSysML_AMM_Es(..), show_amm_n, show_amm_e)\n"
    ++ "where\n\n"

code_concl_amm = "show_amm_n nt = drop 4 (show nt)\n"
    ++ "show_amm_e et = drop 4 (show et)\n"

code_preamble_asd_mm = "module IntoSysML.ASD_MM_Names (IntoSysML_ASD_MM_Ns(..), IntoSysML_ASD_MM_Es(..), show_asd_mm_n, show_asd_mm_e, read_asd_mm)\n"
    ++ "where\n\n"

code_concl_asd_mm = "show_asd_mm_n nt = drop 7 (show nt)\n"
    ++ "show_asd_mm_e et = drop 7 (show et)\n"
    ++ "read_asd_mm x = read (\"ASD_MM_\" ++ x)"

code_preamble_cd_mm = "module IntoSysML.CD_MM_Names (IntoSysML_CD_MM_Ns(..), IntoSysML_CD_MM_Es(..), show_cd_mm_n, show_cd_mm_e, read_cd_mm)\n"
    ++ "where\n\n"

code_concl_cd_mm = "show_cd_mm_n nt = drop 6 (show nt)\n"
    ++ "show_cd_mm_e et = drop 6 (show et)\n"
    ++ "read_cd_mm x = read (\"CD_MM_\" ++ x)"

cons_data_type :: Foldable t => String -> t String -> String
cons_data_type nm elems = "data " ++ nm ++ " = " ++ (showStrs elems " | ") ++ "\n    deriving (Read, Show, Eq)"

cons_AMM_datatypes :: IO ()
cons_AMM_datatypes = do
    (_, amdl)<-loadMdl def_path "IntoSysML_AAD_MM"
    let usg = fsg . mufs $ amdl
    let n_ids = cons_data_type "IntoSysML_AMM_Ns" (fmap ("AMM_" ++ ) $ (ns usg) `sminus` (nsP usg))
    let e_ids = cons_data_type "IntoSysML_AMM_Es" (fmap ("AMM_" ++ ) $ es usg `sminus` esI usg)
    let code = code_preamble_amm ++ n_ids ++ "\n\n" ++ e_ids ++ "\n\n" ++ code_concl_amm ++ "\n"
    writeFile (wr_path ++ "IntoSysML_AMM_Names.hs") code

cons_MM_ASD_datatypes :: IO ()
cons_MM_ASD_datatypes = do
    (nm_mdl, mdl)<-loadMdl def_path "IntoSysML_ASD_MM"
    let usg = fsg . mufs $ mdl
    let n_ids = cons_data_type "IntoSysML_ASD_MM_Ns" (fmap ("ASD_MM_" ++ ) $ (ns usg) `sminus` (nsP usg))
    let e_ids = cons_data_type "IntoSysML_ASD_MM_Es" (fmap ("ASD_MM_" ++ ) $ es usg `sminus` esI usg)
    let code = code_preamble_asd_mm ++ n_ids ++ "\n\n" ++ e_ids ++ "\n\n" ++ code_concl_asd_mm ++ "\n"
    writeFile (wr_path ++ "IntoSysML_ASD_MM_Names.hs") code


cons_MM_CD_datatypes :: IO ()
cons_MM_CD_datatypes = do
    (_, mdl)<-loadMdl def_path "IntoSysML_CD_MM"
    let usg = fsg . mufs $ mdl
    let n_ids = cons_data_type "IntoSysML_CD_MM_Ns" (fmap ("CD_MM_" ++ ) $ (ns usg) `sminus` (nsP usg))
    let e_ids = cons_data_type "IntoSysML_CD_MM_Es" (fmap ("CD_MM_" ++ ) $ es usg `sminus` esI usg)
    let code = code_preamble_cd_mm ++ n_ids ++ "\n\n" ++ e_ids ++ "\n\n" ++ code_concl_cd_mm ++ "\n"
    writeFile (wr_path ++ "IntoSysML_CD_MM_Names.hs") code

main :: IO ()
main = do
    cons_AMM_datatypes
    cons_MM_ASD_datatypes
    cons_MM_CD_datatypes