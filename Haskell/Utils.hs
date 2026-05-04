module Utils(
   transToStr
   , reportWF 
   , evalExpectation
   , print_g_wf_msg 
   , option_main_save
   , other_option) where

import ErrorAnalysis ( nile, consET, ErrorTree )
import System.Environment ( getArgs )
import Control.Monad(when)

transToStr :: (Foldable t, Show a) => t a -> String -> String
transToStr ss sep = foldl (\ss s->if null ss then show s else (show s)++sep++ss) "" ss

reportWF :: t -> [Char] -> (t -> Bool) -> (t -> [ErrorTree]) -> ErrorTree
reportWF s nm wf_f errs_f = 
    if wf_f s then nile else consET (nm++" is malformed. ") (errs_f s)

evalExpectation :: Eq a => a -> a -> String
evalExpectation e r = if e == r then "Ok" else "Fail"

print_g_wf_msg :: String -> [String] -> IO ()
print_g_wf_msg g_id errs = 
   if null errs 
      then putStrLn $ g_id ++ " is well formed" 
      else putStrLn $ show (unlines errs) 

option_main_save :: IO a -> IO () -> IO ()
option_main_save mainp sdsp = do
   args <- getArgs
   mainp
   when ("-g" `elem` args ) $ sdsp

other_option :: IO () -> String-> IO ()
other_option other opt = do
   args <- getArgs
   when (opt `elem` args ) $ other
