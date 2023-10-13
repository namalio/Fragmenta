module ErrorAnalysis(
  ErrorTree
  , nile
  , is_nil
  , consET
  , consSET
  , err_prepend
  , concat_ets
  , add_to_err
  , reportS
  , reportI
  , reportF'
  , reportF
  , reportFI
  , reportRT
  , reportFB
  , reportFT
  , report_fun_total_seq
  , reportFT'
  , reportPF
  , reportFPI
  , showErr
  , reportSSEq
  , reportSEq
  , reportR
  , reportSPEq) where

import Relations
import Sets ( sminus, gunion, Set ) 
import ShowUtils

data ErrorTree = NilE | Error String [ErrorTree]
    deriving (Eq, Show)

-- The 'null' error
nile :: ErrorTree
nile = NilE

is_nil :: ErrorTree -> Bool
is_nil et = et == NilE 

-- Builds an error with nesting
consET :: String -> [ErrorTree] -> ErrorTree
consET = Error

-- Builds an error without nesting
consSET :: String -> ErrorTree
consSET s = consET s []

-- concatenates two ets with a string giving precedence to nil
concat_ets :: String -> ErrorTree -> ErrorTree -> ErrorTree
concat_ets s NilE NilE = nile
concat_ets _ et NilE   = et
concat_ets _ NilE et   = et
concat_ets s et1 et2   = consET s [et1, et2]

-- Prepends a string to the error string
err_prepend :: String -> ErrorTree -> ErrorTree
err_prepend _ NilE = NilE
err_prepend s (Error s' ets) = Error (s++s') ets

add_to_err::ErrorTree ->[ErrorTree]->ErrorTree
add_to_err NilE [] = NilE
add_to_err NilE (e:es) = add_to_err e es
add_to_err (Error s es) es' = (Error s $ es++es')

-- shows the error message
showErrs :: [ErrorTree] -> String
showErrs [] =  ""
showErrs (e:errs) = wr_err (showErr e) ++ (showErrs errs)
    where wr_err es = if null es then "" else "\n\t" ++ es

showErr :: ErrorTree -> String
showErr NilE = ""
showErr (Error s errs) = s ++ showErrs errs

-- Reports possible surjection errors 
reportS :: (Eq b, Show b) => Rel a b -> Set b -> ErrorTree
reportS f ys = 
    let emsg = "Errors in surjection. The following elements are not mapped to: " in
    if surjective f ys then nile else consSET $ emsg ++ (showElems' (ys `sminus` (ran_of f)))

-- Finds error with a function
reportF'::(Eq a,Eq b, Show a, Show b)=>String->Rel a b->ErrorTree
reportF' msg f =
    let emsg = msg ++ " More than one mapping for the elements: " in
    let emsg2 = ". Function is: " in
    let xs_monce = find_monces f in
    if functional f then nile else consSET $ emsg ++ (showElems' xs_monce) ++ emsg2 ++ (showElems' f)

reportF::(Eq a,Eq b, Show a, Show b)=>Rel a b->ErrorTree
reportF f = reportF' "Errors in function." f

-- Finds error with an injection
reportI::(Eq a,Eq b,Show a, Show b)=>Rel a b->ErrorTree
reportI f = reportF' "Errors in injection." (inv f) 

-- Finds error with an bijection
reportFB::(Eq a,Eq b,Show a, Show b)=>Rel a b->Set a->Set b->ErrorTree
reportFB f xs ys = 
  if fun_bij f xs ys then nile else consET "Errors in bijection." les
  where les = [reportFT f xs ys, reportI f, reportS f ys]

-- Reports on a total injection
reportFI::(Eq a,Eq b,Show a, Show b)=>Rel a b->Set a->Set b->ErrorTree
reportFI f xs ys = 
  if fun_inj f xs ys then nile else consET "Errors in total injection." [reportFT f xs ys, reportI f]

-- Errors related to totality 
reportRT::(Eq a, Show a)=>Rel a b->Set a->ErrorTree
reportRT f xs = 
   let es_diff = xs `sminus` (dom_of f) in
   let es_diff2 = (dom_of f) `sminus` xs in
   let errs2 = if null es_diff then nile else consSET ("No mapping for elements: " ++ (showNodes es_diff)) in
   let errs3 = if null es_diff2 then nile else consSET ("The following shouldn't be mapped: " ++ (showNodes es_diff2)) in
   if total f xs then nile else consET "The totality constraint is unsatisfied. " [errs2, errs3]

-- Errors related to a relation
errsR::(Eq a1, Eq a2, Show a1, Show a2)=>Rel a1 a2->Set a1->Set a2->[ErrorTree]
errsR r xs ys = [reportSSEq (dom_of r) xs, reportSSEq (ran_of r) ys]

reportR r xs ys = 
  if relation r xs ys then nile else consET "Errors with domain and range." (errsR r xs ys)

-- Errors related to a total function with respect to a set of domain elements
errsFT::(Eq a, Eq b, Show a, Show b)=>Rel a b->Set a->ErrorTree
errsFT f xs =
    let err1 = reportRT f xs in
    let err2 = reportF f in
    add_to_err err1 [err2]

-- Reports a total function
reportFT'::(Eq a, Eq b, Show a, Show b)=>Rel a b->Set a->ErrorTree
reportFT' f xs =
   let err = errsFT f xs in
   if tfun' f xs then nile else err

-- reporting of a total function given a set of domain and range elements
reportFT::(Eq a, Eq b, Show a, Show b)=>Rel a b->Set a->Set b->ErrorTree
reportFT f xs ys =
   let err1 = errsFT f xs in
   let ns_diff = (ran_of f) `sminus` ys in
   let errs2 = if ((ran_of f) <= ys) then nile else consSET $ "The following are targets but they shouldn't: " ++ (showElems' ns_diff) in
   add_to_err err1 [errs2]

-- reporting of a total function given a set of domain and range elements
report_fun_total_seq f xs ys =
   let err1 = errsFT f xs in
   let ns_diff = (gunion . ran_of $ f) `sminus` ys in
   let errs2 = if (null ns_diff) then nile else consSET $ "The following are targets but they shouldn't: " ++ (showElems' ns_diff) in
   add_to_err err1 [errs2]

-- reports on a partial function
reportPF :: (Eq a, Eq b, Show a, Show b) =>Rel a b -> Set a -> Set b -> ErrorTree
reportPF f xs ys =
    if pfun f xs ys then nile else consET "Errors in partial function" $ (errsR f xs ys) ++ [reportF f]

-- Reports on a partial injection
reportFPI :: (Eq a, Eq b, Show a, Show b) =>Rel a b -> Set a -> Set b -> ErrorTree
reportFPI f xs ys = 
    if pfun f xs ys then nile else consET "Errors in partial injection" $ (errsR f xs ys) ++ [reportI f]

-- Errors related to a subset constraint
reportSSEq :: (Eq a, Show a) => Set a -> Set a -> ErrorTree
reportSSEq r1 r2 =
   if r1 <= r2 then nile else consSET $ "The following are not (or should not be) included: " ++ (showElems' $ r1 `sminus` r2)

reportSEq :: (Eq a, Show a) => String->Set a -> Set a -> ErrorTree
reportSEq sk r1 r2 = -- sk is set kind
    let err1 = reportSSEq r1 r2 
        err2 = reportSSEq r2 r1 in
    if r1 == r2 then nile else consET ("The " ++ sk ++ " sets are unequal.") [err1, err2]

reportSPEq :: (Eq a, Eq b, Show a, Show b) => (Set a, Set b) -> (Set a, Set b) -> ErrorTree
reportSPEq ps1@(ds1, rs1) ps2@(ds2, rs2) = 
  let err1 = reportSEq "first" ds1 ds2
      err2 = reportSEq "second" rs1 rs2 in
      if ps1 == ps2 then nile else consET "The two pairs with sets are unequal." [err1, err2]