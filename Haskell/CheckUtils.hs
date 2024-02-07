module CheckUtils(
   check_report_wf
   , check_morphism
   , check_ty_morphism
   , show_typing_msg
   , show_wf_msg
   , checkOkETCFs
   , checkETCompliance) where

import Gr_Cls
import Utils ( evalExpectation )
import Frs ( rEtCompliesF, Fr )
import GrswT ( GrwT )
import GrswET ( GrwET )
import ErrorAnalysis ( is_nil, showErr, ErrorTree )

show_wf_msg :: String -> ErrorTree -> IO ()
show_wf_msg g_id errs = do
   if is_nil errs 
      then putStrLn $ g_id ++ " is well formed" 
      else putStrLn $ g_id ++ " is mal-formed\n" ++  (showErr errs) 

reportErrs :: String -> ErrorTree -> Bool -> IO ()
reportErrs id errs b = do
   if is_nil errs
      then putStrLn $ id ++ " is well formed (" ++ (evalExpectation b True) ++ ")"
      else putStrLn $ "(" ++ (evalExpectation b False) ++ ") " ++ id ++ " is mal-formed\n" ++ (showErr errs) 

check_report_wf :: (G_WF_CHK g, Eq a, Eq b, Show a, Show b, GNumSets a) =>String -> Maybe TK -> g a b -> Bool -> IO ()
check_report_wf id otk g b = do
   let errs = faultsG id otk g 
   reportErrs id errs b

check_morphism::(Eq a, Eq b, Show a, Show b, GM_CHK g g', GNodesNumConv a, GNumSets a)
   =>String->Maybe MK->g a b->GrM a b->g' a b->Bool->IO()
check_morphism id omk gs m gt b = do 
   let errs = faultsGM id omk (gs, m, gt) 
   reportErrs id errs b

check_ty_morphism :: (GM_CHK' g g', Eq a, Eq b, Read a, Show a, Show b, GNodesNumConv a, GNumSets a) 
   =>String -> Maybe MK -> g a b -> g' a b -> Bool -> IO ()
check_ty_morphism id omk gwt sg b = do 
   let errs = faultsGM' id omk (gwt, sg) 
   reportErrs id errs b

-- Checks the extra typing
checkETCompliance::(Eq a, Eq b, Read a, Show a, Show b, GWET gi, GWT gi', ET_GM_CHK gi gi' gt, GNodesNumConv a, GNumSets a)
   =>String->gi a b->gt a b->gi' a b->gt a b->Bool->IO ()
checkETCompliance id gwet f1 gwt f2 b = do
   let errs = faultsETGM id (gwet, f1) (gwt, f2)  
   reportErrs id errs b

show_typing_msg :: ErrorTree -> IO ()
show_typing_msg errs = 
   if is_nil errs
      then putStrLn "The PC is well-typed."
      else putStrLn $ "The PC is ill-typed:\n" ++ (showErr errs) 

checkOkETCFs::(Eq a, Eq b, Show a, Show b, GET g, Ok_ETC_CHK g)=>(String, g a b)->(String,g a b)->Bool->IO() 
checkOkETCFs (nm_fs, fs) (nm_ft, ft) b1 = do
   let id = "Extra typing compatibility of " ++ nm_fs ++ " with respect to " ++ nm_ft
   let errs = faultsETC id fs ft
   let msgStart =  nm_fs 
   let msgEndOk = " is ET compatible with " ++ nm_ft 
   let msgEndFail = " is not ET compatible with " ++ nm_ft ++ "\n"
   let b2 = is_nil errs
   if b2
      then putStrLn $ (evalExpectation b1 b2) ++ msgStart ++ msgEndOk
      else putStrLn $ (evalExpectation b1 b2) ++ msgStart ++ msgEndFail ++ (showErr errs) 
   where evalExpectation b1 b2 = if b1 == b2 then "(Ok)" else "(Fail)"