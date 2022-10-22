module CheckUtils(check_report_wf, check_morphism, check_ty_morphism, show_typing_msg, show_wf_msg) where

import Gr_Cls
import Grs
import SGrs
import Utils
import Frs
import ShowUtils
import ErrorAnalysis

show_wf_msg g_id errs = do
   if is_nil errs 
      then putStrLn $ g_id ++ " is well formed" 
      else putStrLn $ g_id ++ " is mal-formed\n" ++  (show_err errs) 

report_errs id errs b = do
   if is_nil errs
      then putStrLn $ id ++ " is well formed (" ++ (evalExpectation b True) ++ ")"
      else putStrLn $ "(" ++ (evalExpectation b False) ++ ") " ++ id ++ " is mal-formed\n" ++ (show_err errs) 

check_report_wf id otk g b = do
   let errs = check_wf id otk g 
   report_errs id errs b

check_morphism::(Eq a, Eq b, Show a, Show b, GM_CHK g g')=>String->Maybe MK->g a b->GrM a b->g' a b->Bool->IO()
check_morphism id omk gs m gt b = do 
   let errs = check_wf_gm id omk (gs, m, gt) 
   report_errs id errs b

check_ty_morphism id omk gwt sg b = do 
   let errs = check_wf_gm' id omk (gwt, sg) 
   report_errs id errs b

show_typing_msg errs = 
   if is_nil errs
      then putStrLn "The PC is well-typed."
      else putStrLn $ "The PC is ill-typed:\n" ++ (show_err errs) 

