
------------------
-- Project: PCs/Fragmenta
-- Module: 'CSPPrint'
-- Description: Converts CSP specifications to strings 
-- Author: Nuno Amálio
-----------------
module CSPPrint(wrCSP) where

import CSP_AST
import ShowUtils
import Sets

--wrWaitFor = "Wait_({})= SKIP\nWait_(evs) = [] e :evs @ e->Wait_(diff(evs, {e}))"

--wrBindings::[[String]]->[String]
--wrBindings bss = foldr (\bs bs'->conv bs:bs') [] bss 
--   where conv bs 
--          | length bs == 0 = "{}" 
--         | length bs == 1 = head bs 
--          | otherwise = "{" ++ foldr (\b s-> b ++ if null s then "" else ",") "" bs ++ "}"

wrDecl :: Int -> Decl -> String
wrDecl ind (Channel ids) = "channel " ++ (wrSepElems ids "," True False ind)
wrDecl ind (EqDecl e1 e2) = (do_indent ind) ++ (wrExp ind e1) ++ " = " ++ wrExp (ind +1) e2
wrDecl ind (Include ms) = wrSepElems (map (\m->"include \"" ++ m ++ ".csp\"") (toList ms)) "\n" False False ind

wrExp :: Int -> Exp -> String
wrExp _ (ExpId id) = id 
wrExp ind (ExpPar e) = "(" ++ (wrExp ind e) ++ ")" 
wrExp ind (ExpApp id bs) = id ++ "(" ++ (wrSepElems bs ", " False False 0) ++ ")" 
wrExp ind (GExp e1 e2) = (wrExp ind e1) ++ " & " ++ (wrExp ind e2)
wrExp ind (IfExp e1 e2 e3) = 
   "if " ++ (wrExp 0 e1) ++ "\n" ++ (do_indent ind) ++ "then\n" ++ (do_indent $ ind +1) ++ (wrExp ind e2) 
   ++ "\n" ++ (do_indent ind) ++ "else\n" ++ (do_indent $ ind +1) ++ (wrExp ind e3)
wrExp ind (Prfx e1 e2) = (wrExp ind e1) ++ " -> " ++ (wrExp ind e2)
wrExp ind (ExtChoice e1 e2) = (wrExp ind e1) ++ "\n" ++ (do_indent (ind +1)) ++ "[] " ++ (wrExp ind e2)
wrExp ind (IntChoice e1 e2) = (wrExp ind e1) ++ "\n" ++ (do_indent (ind +1)) ++ " |~| " ++ (wrExp ind e2)
wrExp ind (RExtChoice idv ids e) =  "[] " ++ idv ++ " : " ++ ids ++ " @ " ++ (wrExp ind e)
wrExp ind (SeqComp e1 e2) = (wrExp ind e1) ++ "; " ++ (wrExp ind e2)
wrExp ind (Parallel evs e1 e2) = (wrExp ind e1) ++ "[|{" ++ (wrSepElems evs "," False False 0) ++ "}|]" ++ (wrExp ind e2)
wrExp ind (Throw evs e1 e2) = (wrExp ind e1) ++ "[|{" ++ (wrSepElems evs "," False False 0) ++ "}|>" ++ (wrExp ind e2)
--wrExp ind (SyncInterrupt evs e1 e2) = (wrExp ind e1) ++ "/+{" ++ (wrSepElems evs "," False False 0) ++ "}+\\" ++ (wrExp ind e2)
wrExp ind (Interleave e1 e2) = (wrExp ind e1) ++ " ||| " ++ (wrExp ind e2)
--wrExp ind (WaitFor ids) = "Wait_({" ++ (wrSepElems ids "," True False ind) ++ "})"
wrExp ind STOP = "STOP"
wrExp ind SKIP = "SKIP"
wrExp ind (LetW ds e) = "\n" ++ (do_indent ind) ++ "let \n" ++ (wrSepElems (map (wrDecl $ ind + 1) ds) "\n" False False (ind +2)) 
   ++ "\n" ++ (do_indent ind) ++ "within\n" ++ (do_indent (ind+1)) ++ (wrExp (ind + 1) e)
wrExp ind (ExpRen e rs) = (wrExp ind e) ++ (wrRenamings rs)
wrRenamings :: Foldable t => t (String, String) ->String
wrRenamings rs = "[[" ++ (foldr (\(fr, to) rstr->fr ++ " <- " ++ to ++ (if null rstr then "" else ",") ++ rstr) "" rs) ++ "]]"
--hasWait (WaitFor _) = True

hasWait :: Exp -> Bool
hasWait (LetW ds e) = (hasWaitDs ds) || hasWait e
hasWait _ = False

hasWaitD :: Decl -> Bool
hasWaitD (Channel _) = False
hasWaitD (Include _) = False
hasWaitD (EqDecl _ e) = hasWait e

hasWaitDs :: Foldable t => t Decl -> Bool
hasWaitDs ds = foldr (\d d'->(hasWaitD d) || d') False ds

wrCSP :: CSPSpec -> String
wrCSP (CSP ds) = 
   let cspTxt = wrSepElems (map (wrDecl 0) ds) "\n\n" False False 0 in
   cspTxt
  -- if (hasWaitDs ds) then wrWaitFor ++ "\n\n" ++ cspTxt else cspTxt


