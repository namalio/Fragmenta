---------------------------
-- Project: PCs/Fragmenta
-- Module: 'Mult'
-- Description: Handles multiplicities of relations
-- Author: Nuno Amálio
----------------------------

module Mult (MultVal(..), mval, mmany, MultC(..), Mult, mrange, msole_many, msole_k, multwf, multOk, mlbn,
    check_multOk, mopt, allowedm, m_leq, mv_mult,
    isMultVal_k, isMultMany, isMultOpt, isMultRange, mult_mr, isMultEither, isMultLbZ) where

import SGElemTys
import Relations
import ErrorAnalysis
import SimpleFuns ( butLast)
import Logic
import Sets ( Set(..), card, singles )
import TheNil

data MultVal = Val Int | Many 
   deriving (Eq, Show)

-- 'MultVal' constructors
mval :: Int -> MultVal
mval = Val
mmany :: MultVal
mmany = Many

-- The mutliplicity compound
data MultC = Rm Int MultVal | Sm MultVal 
   deriving (Eq, Show)

-- The actual mutliplicities
type Mult = Set MultC

-- 'MultC' constructors
mrange :: Int -> MultVal -> MultC
mrange k mv = Rm k mv
msole_many :: MultC
msole_many  = Sm Many
msole_k :: Int -> MultC
msole_k k   = Sm (mval k)
mopt :: MultC
mopt        = Rm 0 (mval 1)

-- Checks that a multiplicity constraint is well-formed
multcwf :: MultC -> Bool
multcwf (Rm n Many) = n >= 0
multcwf (Rm lb (Val ub)) = lb < ub && lb >=0
multcwf (Sm Many) = True
multcwf (Sm (Val v)) = v >= 0


mv_leq _ Many = True
mv_leq (Val k) (Val j) = k <= j
mv_leq _ _ = False

instance Ord MultVal where
   (<=) = mv_leq
   --(>=) = (\s1 s2-> (ids s1) >= (ids s2))

mv_mult :: MultVal -> MultVal -> MultVal
mv_mult Many _  = Many
mv_mult _ Many  = Many
mv_mult (Val k) (Val j)  = Val (k * j)

mc_leq mc1 mc2 = mlb mc2 <= mlb mc1 && mub mc1 <= mub mc2

instance Ord MultC where
   (<=) = mc_leq

m_leq [] m2 = False
m_leq [mc1] m2 = any (\mc2->mc1 <= mc2) m2
m_leq (mc1:mcs) m2 = (any (\mc2->mc1 <= mc2) m2) && mcs `m_leq` m2


-- Predicate 'withinm' (≬)
--withinm k (m1, m2) = m1 <= mval k && mval k <= m2

-- Function mlb, which gives the lower bound of a multplicity constraint (Mult) 
mlbn :: MultC -> Int
mlbn (Sm Many) =  0
mlbn (Sm (Val k)) = k
mlbn (Rm k _) = k
mlb :: MultC -> MultVal
mlb mc = Val $ mlbn mc

-- Functions mub, which gives the upper bound of a multiplicity constraint (Mult)
mub :: MultC -> MultVal
mub (Sm m) = m
mub (Rm _ m) = m

mult_mr :: MultC -> MultC -> MultC
mult_mr (Rm n1 m_1) (Rm n2 m_2) = Rm (n1 * n2) (m_1 `mv_mult` m_2)

-- Complies to multiplicity (≬)
compliesm :: Int -> MultC -> Bool
compliesm k m  = mlb m <= mval k && mval k <= mub m

-- Either multplicity (…)
eitherm :: Foldable t=>Int ->t MultC -> Bool
eitherm k = foldl(\br m->k `compliesm` m || br) False
--eitherm k []     = False
--eitherm k (m:ms) = k `compliesm` m || eitherm k ms

-- Checks whether 'm' is a many multiplicity
isMultMany :: Mult -> Bool
isMultMany (Set (Sm Many) EmptyS)   = True
isMultMany (Set (Rm 0 Many) EmptyS) = True
isMultMany _ = False

isMultVal_k :: Mult -> Int -> Bool
isMultVal_k (Set m EmptyS) k = m == msole_k k 
isMultVal_k _ _ = False
isMultOpt :: Mult -> Bool
isMultOpt (Set m EmptyS) = m == mopt 
isMultOpt _ = False

-- Checks whether  m is a range or bounded multiplicity
isMultRange :: Mult -> Bool
isMultRange (Set (Sm (Val k)) EmptyS) = k > 1
isMultRange (Set m@(Rm lb ub) EmptyS) = lb >= 0 && mval 2 <= ub && multcwf m
isMultRange _ = False

-- Unique, non-empty, individually well-formed and no manys allowed if more than one multiplicity in set
multwf :: Mult -> Bool
multwf ms = all multcwf ms && (length ms > 1) `implies` (all (\m->not . isMultMany $ singles m) ms)

isMultEither :: Mult -> Bool
isMultEither ms = multwf ms && card ms > 1

isMultLbZ :: Mult -> Bool
isMultLbZ EmptyS = False
isMultLbZ (Set m ms) = mlbn m == 0 || isMultLbZ ms

-- Predicate 'allowedm' (∝) s
allowedm :: SGETy -> (Mult, Mult) -> Bool
allowedm (Erel Dbi) (_, _) = True
allowedm Eder (_, _) = True
allowedm (Ecomp Duni) (Set (Sm (Val 1)) EmptyS, _) = True
allowedm (Erel Duni) (m1, _) = isMultMany m1
allowedm (Ecomp Dbi) (m1, _) = isMultVal_k m1 1 || isMultOpt m1
allowedm _ _                 = False
--allowedm Ewander (m1, m2)    = isMultMany m1 && isMultMany m2



rbounded :: (Foldable t, Eq a) => Rel a a-> t a -> MultC -> Bool
rbounded r s m = all (\x->length(img r [x]) `compliesm` m)  s
eitherbounded :: (Foldable t, Eq a) => Rel a a -> t a -> Mult -> Bool
eitherbounded r s ms = all (\x->length(img r [x]) `eitherm` ms)  s

--
-- Predicate 'rmOk', which checks whether a multiplicity is satisfied by a given relation
multOk::Eq a=>Rel a a->Set a->Set a->Mult->Mult->Bool
multOk r s t m (Sm (Val 0) `Set` EmptyS) = null $ rres r t  
multOk r s t (Sm (Val 0) `Set` EmptyS) m = null $ dres r s
multOk r s t m (Sm (Val 1) `Set` EmptyS)
    | m == singles (msole_k 1) = fun_bij r s t
    | m == singles mopt      = fun_inj r s t
    | isMultMany m     = fun_total r s t
    | isMultRange m    = fun_total r s t && rbounded (inv r) t (the m)
    | isMultEither m   = fun_total r s t && eitherbounded (inv r) t m
multOk r s t (Sm (Val 1) `Set` EmptyS) m 
    | m == singles mopt = fun_inj (inv r) t s
    | isMultMany m      = fun_total (inv r) t s
    | isMultRange m     = fun_total (inv r) t s && rbounded r s (the m)
    | isMultEither m    = fun_total (inv r) s t && eitherbounded r t m
multOk r s t m (Rm 0 (Val 1) `Set` EmptyS)
    | m == singles mopt = fun_pinj r s t
    | isMultMany m      = pfun r s t
    | isMultRange m     = pfun r s t && rbounded (inv r) t (the m)
    | isMultEither m    = pfun r s t && eitherbounded (inv r) t m
multOk r s t (Rm 0 (Val 1) `Set` EmptyS) m
    | isMultMany m      = pfun (inv r) t s
    | isMultRange m     = pfun (inv r) t s && rbounded r s (the m) 
    | isMultEither m    = pfun (inv r) t s && eitherbounded r s m 
multOk r s t m1 m2 
    | all isMultMany [m1, m2]         = relation r s t
    | isMultMany m1 && isMultRange m2 = relation r s t && rbounded r s (the m2) 
    | isMultRange m1 && isMultMany m2 = relation r s t && rbounded (inv r) t (the m1)
    | all isMultRange [m1, m2]        = relation r s t && rbounded r s (the m2) && rbounded (inv r) t (the m1)
    | all isMultEither [m1, m2]       = relation r s t && eitherbounded r s m2 && eitherbounded (inv r) t m1

--
-- Predicate 'rmOk', which checks whether a multiplicity is satisfied by a given relation
--multOk::Eq a=>[(a, a)]->[a]->[a]->Mult->Mult->Bool
--multOk r s t [m1] [m2] = multcOk r s t m1 m2 
--multOk r s t _ [] = False
--multOk r s t [] _ = False
--multOk r s t [m1] (m2:ms) = multcOk r s t m1 m2 || multOk r s t [m1] ms
--multOk r s t (m1:ms) [m2] = multcOk r s t m1 m2 || multOk r s t ms [m2]
--multOk r s t (m1:ms1) ms2 = multOk r s t [m1] ms2 || multOk r s t ms1 ms2


say_mv :: MultVal -> String
say_mv (Val k) = if k == 1 then "one" else (show k)
say_mv (Many) = "many (*)"

say_multc :: MultC -> String
say_multc (Sm mv) = say_mv mv
say_multc (Rm 0 (Val 1)) = "optional (0..1)"
say_multc (Rm 0 Many) = say_mv (Many)
say_multc (Rm lb ub) = say_mv (mval lb) ++ ".." ++ (say_mv ub) 
say_mult :: Mult -> String
say_mult (m `Set` EmptyS) = say_multc m
say_mult ms = butLast (foldr (\m say->say ++ say_multc m ++ ",") "{" ms) ++ "}"

multc_err_msg :: Show a => a -> Mult -> Mult -> String
multc_err_msg me m1 m2 = (say_mult m1) ++ " to " ++ (say_mult m2) ++ " multiplicity constraint  of meta-edge " ++ (show me) ++ " is unsatisfied."

reportRB :: (Foldable t, Eq a, Show a) => Rel a a -> t a -> MultC -> ErrorTree
reportRB r s m = 
   if rbounded r s m then nile else consSET "Relation not within multiplicity bounds" 

reportEB :: (Foldable t, Eq a) => Rel a a -> t a -> Mult -> ErrorTree
reportEB r s m = if eitherbounded r s m then nile else consSET "Relation not within multiplicity bounds"

check_multOk::(Eq a, Show a, Show b)=>b->Rel a a->Set a->Set a->Mult->Mult->ErrorTree
check_multOk me r s t m1 m2@(Sm (Val 0) `Set` EmptyS) = if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) []
check_multOk me r s t m1@(Sm (Val 0) `Set` EmptyS) m2 = if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) []
check_multOk me r s t m1 m2@(Sm (Val 1) `Set` EmptyS) 
    | m1 == singles (msole_k 1)  = if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) [reportFB r s t]
    | m1 == singles mopt = if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) [reportFI r s t]
    | isMultMany m1      = if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) [reportFT r s t]
    | isMultRange m1    = 
        if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) [reportFT r s t, reportRB (inv r) t $ the m1] 
    | isMultEither m1   = if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) [reportFT r s t, reportEB (inv r) t m1]
check_multOk me r s t m1@(Sm (Val 1) `Set` EmptyS) m2 
    | m2 == singles mopt = 
        if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) [reportFI (inv r) t s]
    | isMultMany m2 = 
        if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) [reportFT (inv r) t s]
    | isMultRange m2 = 
        if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) [reportFT (inv r) t s, reportRB r s $ the m2] 
    | isMultEither m2   = if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) [reportFT (inv r) t s, reportEB r s m2]
check_multOk me r s t m1 m2@(Rm 0 (Val 1) `Set` EmptyS)
    | m1 == singles mopt  = 
        if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) [reportFPI r s t] 
    | isMultMany m1      = 
        if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) [reportPF r s t] 
    | isMultRange m1     = 
        if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) [reportPF r s t, reportRB (inv r) t $ the m1]
    | isMultEither m1   = if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) [reportPF r s t, reportEB (inv r) t m1]
check_multOk me r s t m1@(Rm 0 (Val 1) `Set` EmptyS) m2
    | isMultMany m2  = 
        if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) [reportPF (inv r) t s]  
    | isMultRange m2 = 
        if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) [reportPF (inv r) t s, reportRB (inv r) t $ the m2]
    | isMultEither m2 = if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) [reportPF (inv r) t s, reportEB (inv r) t m2]
check_multOk me r s t m1 m2 
    | all isMultMany [m1, m2]         = 
        if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) [reportR r s t]
    | isMultMany m1 && isMultRange m2 = 
        if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) [reportR r s t, reportRB r s $ the m2]
    | isMultMany m1 && isMultEither m2 = 
        if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) [reportR r s t, reportEB r s m2]
    | isMultRange m1 && isMultMany m2 = 
        if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) [reportR r s t, reportRB (inv r) t $ the m1]
    | isMultEither m1 && isMultMany m2 = 
        if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) [reportR r s t, reportEB (inv r) t  m1]
    | all isMultRange [m1, m2]        = 
        if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) [reportR r s t, reportRB r s $ the m2, reportRB (inv r) t $ the m1]
    | all isMultEither [m1, m2] = if multOk r s t m1 m2 then nile else consET (multc_err_msg me m1 m2) [reportR r s t, reportEB r s m2, reportEB (inv r) t m1]

mult_err_msg :: Show a => a -> String
mult_err_msg me = "Multiplicity errors in " ++ (show me)


--check_multOk::(Eq a, Show a)=>a->[(a, a)]->[a]->[a]->Mult->Mult->ErrorTree
--check_multOk me r s t m1 m2 = if multOk r s t m1 m2 then nile else check_multOka m1 m2
--   where check_multOka [m1] [m2] = check_multcOk me r s t m1 m2
--         check_multOka _ [] = nile
--         check_multOka [] _ = nile
--         check_multOka [m1] (m2:ms) = concat_ets (mult_err_msg me) (check_multcOk me r s t m1 m2) (check_multOk me r s t [m1] ms)
--         check_multOka (m1:ms) [m2] = concat_ets (mult_err_msg me) (check_multcOk me r s t m1 m2) (check_multOk me r s t ms [m2])
--         check_multOka (m:ms1) ms2 = concat_ets (mult_err_msg me) (check_multOk me r s t [m] ms2) (check_multOk me r s t ms1 ms2)

