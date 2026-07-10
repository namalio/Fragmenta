
------------------------
-- Project: Fragmenta/PCs
-- Module: 'MM'
-- Description: Module that deals with the checks anf generation of haskell model with names subjacent to the metamodel of PCs 
-- Author: Nuno Amálio
------------------------

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
import NumString

def_path :: String
def_path = "PCs/MM/"
img_path :: String
img_path = "PCs/MM/img/"
wr_path :: String
wr_path = "./"

-- Saves the PCs drawings as graphviz files
saveDrawings :: IO ()
saveDrawings = do
   draw_mdl def_path img_path "PCs_AMM"
   draw_mdl def_path img_path "PCs_MM"

checkAMM :: IO ()
checkAMM = do
    (nm_mdl, mdl)<-loadMdl def_path "PCs_AMM"
    check_report_wf nm_mdl (Just Total) mdl True

code_preamble :: String
code_preamble = "module PCs.MM_Names\n"
    ++ "    ( PCs_AMM_Ns(..)\n"
    ++ "    , PCs_AMM_Es(..)\n"
    ++ "    , PCs_CMM_Ns(..)\n" 
    ++ "    ,  PCs_CMM_Es(..)\n"
    ++ "    , show_amm_n\n"
    ++ "    , show_amm_e\n"
    ++ "    , show_cmm_n\n"
    ++ "    , show_cmm_e\n"
    ++ "    , read_cmm\n"
    ++ "    )\n"
    ++ "where\n\n"
--code_concl = "data PCS_MM_Ns = AMMN PCs_AMM_Ns | CMMN PCs_CMM_Ns\n"
--    ++ "data PCS_MM_Es = AMME PCs_AMM_Es | CMME PCs_CMM_Es\n"
code_concl :: String
code_concl = "show_mm_n :: Show a => a -> String\n"
    ++ "show_mm_n nt = drop 4 (show nt)\n"
    ++ "show_amm_n :: PCs_AMM_Ns -> String\n"
    ++ "show_amm_n nt = show_mm_n nt\n"
    ++ "show_mm_e :: Show a => a -> String\n"
    ++ "show_mm_e et = drop 4 (show et)\n"
    ++ "show_amm_e :: PCs_AMM_Es -> String\n"
    ++ "show_amm_e et = show_mm_e et\n"
    ++ "show_cmm_n :: PCs_CMM_Ns -> String\n"
    ++ "show_cmm_n nt = show_mm_n nt\n"
    ++ "show_cmm_e :: PCs_CMM_Es -> String\n"
    ++ "show_cmm_e et = show_mm_e et\n"
    ++ "read_cmm :: Read a => String -> a\n"
    ++ "read_cmm x = read (\"CMM_\" ++ x)\n"

cons_data_type :: String -> Set String -> String
cons_data_type nm elems = "data " ++ nm ++ "\n    = " 
    ++ (first elems) ++ " " ++ (showStrs (fmap ("\n    | " ++) $ rest elems) "") ++ "\n    deriving (Read, Show, Eq)"

consMMDatatypes :: IO ()
consMMDatatypes = do
    (nm_mdla, mdla)<-loadMdl def_path "PCs_AMM"
    (nm_mdlc, mdlc)<-loadMdl def_path "PCs_MM"
    let ausg = fsg . mufs $ mdla
    let data_amm_ns = cons_data_type "PCs_AMM_Ns" (fmap ("AMM_" ++ ) $ ns ausg)
    let data_amm_es = cons_data_type "PCs_AMM_Es" (fmap ("AMM_" ++ ) $ es ausg `sminus` esI ausg)
    let cusg = fsg . mufs $ mdlc
    let data_cmm_ns = cons_data_type "PCs_CMM_Ns" (fmap ("CMM_" ++ ) $ ns cusg)
    let data_cmm_es = cons_data_type "PCs_CMM_Es" (fmap ("CMM_" ++ ) $ es cusg `sminus` esI cusg)
    let code = code_preamble ++ data_amm_ns ++ "\n\n" ++ data_amm_es ++ "\n\n" ++ data_cmm_ns ++ "\n\n" ++ data_cmm_es ++ "\n\n" ++ code_concl ++ "\n"
    writeFile (wr_path ++ "MM_Names.hs") code

checkMMs ::IO ()
checkMMs = do
    (nm_amdl, amdl)<-loadMdl def_path "PCs_AMM"
    check_report_wf nm_amdl (Just Total) amdl True
    (nm_mdl, mdl)<-loadMdl def_path "PCs_MM"
    check_report_wf nm_mdl (Just Total) mdl True

check_morphisms ::IO ()
check_morphisms = do
    (nm_af, af)<-loadF def_path "F_AMM.fr"
    (nm_f1, f1)<-loadF def_path "F_MM_1.fr"
    (nm_f2, f2)<-loadF def_path "F_MM_2.fr"
    (nm_f3, f3)<-loadF def_path "F_MM_3.fr"
    (nm_f4, f4)<-loadF def_path "F_MM_4.fr"
    (nm_f5, f5)<-loadF def_path "F_MM_5.fr"
    (nm_f6, f6)<-loadF def_path "F_MM_6.fr"
    (nm_f7, f7)<-loadF def_path "F_MM_7.fr"
    (nm_f8, f8)<-loadF def_path "F_MM_8.fr"
    (nm_f9, f9)<-loadF def_path "F_MM_9.fr"
    (nm_f10, f10)<-loadF def_path "F_MM_10.fr"
    (nm_f11, f11)<-loadF def_path "F_MM_11.fr"
    (nm_f12, f12)<-loadF def_path "F_MM_12.fr"
    (nm_f13, f13)<-loadF def_path "F_MM_13.fr"
    (nm_f14, f14)<-loadF def_path "F_MM_14.fr"
    (nm_f15, f15)<-loadF def_path "F_MM_15.fr"
    (nm_m1, m1)<-loadM def_path "F_MM_1.gm"
    (nm_m2, m2)<-loadM def_path "F_MM_2.gm"
    (nm_m3, m3)<-loadM def_path "F_MM_3.gm"
    (nm_m4, m4)<-loadM def_path "F_MM_4.gm"
    (nm_m5, m5)<-loadM def_path "F_MM_5.gm"
    (nm_m6, m6)<-loadM def_path "F_MM_6.gm"
    (nm_m7, m7)<-loadM def_path "F_MM_7.gm"
    (nm_m8, m8)<-loadM def_path "F_MM_8.gm"
    (nm_m9, m9)<-loadM def_path "F_MM_9.gm"
    (nm_m10, m10)<-loadM def_path "F_MM_10.gm"
    (nm_m11, m11)<-loadM def_path "F_MM_11.gm"
    (nm_m12, m12)<-loadM def_path "F_MM_12.gm"
    (nm_m13, m13)<-loadM def_path "F_MM_13.gm"
    (nm_m14, m14)<-loadM def_path "F_MM_14.gm"
    (nm_m15, m15)<-loadM def_path "F_MM_15.gm"
    check_report_wf nm_af (Just Total) af True
    check_report_wf nm_f1 (Just Partial) f1 True
    check_report_wf nm_f2 (Just Partial) f2 True
    check_report_wf nm_f3 (Just Partial) f3 True
    check_report_wf nm_f4 (Just Partial) f4 True
    check_report_wf nm_f5 (Just Partial) f5 True
    check_report_wf nm_f6 (Just Partial) f6 True
    check_report_wf nm_f7 (Just Partial) f7 True
    check_report_wf nm_f8 (Just Partial) f8 True
    check_report_wf nm_f9 (Just Partial) f9 True
    check_report_wf nm_f10 (Just Partial) f10 True
    check_report_wf nm_f11 (Just Partial) f11 True
    check_report_wf nm_f12 (Just Partial) f12 True
    check_report_wf nm_f13 (Just Partial) f13 True
    check_report_wf nm_f14 (Just Partial) f14 True
    check_report_wf nm_f15 (Just Partial) f15 True
    check_morphism (nm_m1 ++ " (Partial)") (Just PartialM) f1 m1 af True
    check_morphism (nm_m2 ++ " (Partial)") (Just PartialM) f2 m2 af True
    check_morphism (nm_m3 ++ " (Partial)") (Just PartialM) f3 m3 af True
    check_morphism (nm_m4 ++ " (Partial)") (Just PartialM) f4 m4 af True
    check_morphism (nm_m5 ++ " (Partial)") (Just PartialM) f5 m5 af True
    check_morphism (nm_m6 ++ " (Partial)") (Just PartialM) f6 m6 af True
    check_morphism (nm_m7 ++ " (Partial)") (Just PartialM) f7 m7 af True
    check_morphism (nm_m8 ++ " (Partial)") (Just PartialM) f8 m8 af True
    check_morphism (nm_m9 ++ " (Partial)") (Just PartialM) f9 m9 af True
    check_morphism (nm_m10 ++ " (Partial)") (Just PartialM) f10 m10 af True
    check_morphism (nm_m11 ++ " (Partial)") (Just PartialM) f11 m11 af True
    check_morphism (nm_m12 ++ " (Partial)") (Just PartialM) f12 m12 af True
    check_morphism (nm_m13 ++ " (Partial)") (Just PartialM) f13 m13 af True
    check_morphism (nm_m14 ++ " (Partial)") (Just PartialM) f14 m14 af True
    check_morphism (nm_m15 ++ " (Partial)") (Just PartialM) f15 m15 af True

check_models_ref::IO ()
check_models_ref = do
    (nm_amdl, amdl)<-loadMdl def_path "PCs_AMM"
    (nm_cmdl, cmdl)<-loadMdl def_path "PCs_MM"
    rms<-load_rm_cmdl_def def_path "PCs_MM"
    check_report_wf "PCs_AMM" (Just Total) amdl True
    check_report_wf "PCs_MM" (Just Total) cmdl True
    check_morphism "Refinement of PCs_MM by PCs_AMM " (Just TotalM) cmdl rms amdl True


do_main :: IO ()
do_main = do
    check_models_ref

main :: IO ()
main = do
    option_main_save do_main saveDrawings
    other_option consMMDatatypes "-dt"
    other_option check_morphisms "-c"

test::IO()
test = do
    (nm_f6, f6)<-loadF def_path "F_MM_6.fr"
    let sg=fsg f6
    print sg
    print (inh sg)
