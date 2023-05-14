module CheckUtils(check_report_wf, check_morphism, check_ty_morphism, show_typing_msg, show_wf_msg) where

import Gr_Cls
import Grs
import SGrs
import Utils
import Frs
import ShowUtils
import ErrorAnalysis ( is_nil, showErr, ErrorTree )

show_wf_msg :: String -> ErrorTree -> IO ()
show_wf_msg g_id errs = do
   if is_nil errs 
      then putStrLn $ g_id ++ " is well formed" 
      else putStrLn $ g_id ++ " is mal-formed\n" ++  (showErr errs) 

reportErrs :: [Char] -> ErrorTree -> Bool -> IO ()
reportErrs id errs b = do
   if is_nil errs
      then putStrLn $ id ++ " is well formed (" ++ (evalExpectation b True) ++ ")"
      else putStrLn $ "(" ++ (evalExpectation b False) ++ ") " ++ id ++ " is mal-formed\n" ++ (showErr errs) 

check_report_wf :: (G_WF_CHK g, Eq a, Eq b, Show a, Show b) =>String -> Maybe TK -> g a b -> Bool -> IO ()
check_report_wf id otk g b = do
   let errs = faultsG id otk g 
   reportErrs id errs b

check_morphism::(Eq a, Eq b, Show a, Show b, GM_CHK g g')=>String->Maybe MK->g a b->GrM a b->g' a b->Bool->IO()
check_morphism id omk gs m gt b = do 
   let errs = faultsGM id omk (gs, m, gt) 
   reportErrs id errs b

check_ty_morphism id omk gwt sg b = do 
   let errs = faultsGM' id omk (gwt, sg) 
   reportErrs id errs b

show_typing_msg errs = 
   if is_nil errs
      then putStrLn "The PC is well-typed."
      else putStrLn $ "The PC is ill-typed:\n" ++ (showErr errs) 

