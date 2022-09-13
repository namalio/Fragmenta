---------------------------
-- Project: PCs/Fragmenta
-- Module: 'Mult'
-- Description: Handles multiplicities of relations
-- Author: Nuno Amálio
----------------------------

module Mult (MultVal(..), mval, mmany, MultC(..), Mult, mrange, msole_many, msole_k, multwf, multOk, check_multOk, mopt, allowedm, m_leq, mv_mult,
    isMultVal_k, isMultMany, isMultOpt, isMultRange, mult_mr, isMultEither) where

import SGElemTys
import Relations
import ErrorAnalysis
import SimpleFuns
import Logic
import Sets

data MultVal = Val Int | Many 
   deriving (Eq, Show)

-- 'MultVal' constructors
mval k = Val k
mmany = Many

-- The mutliplicity compound
data MultC = Rm Int MultVal | Sm MultVal 
   deriving (Eq, Show)

-- The actual mutliplicities
type Mult = [MultC]

-- 'MultC' constructors
mrange k mv = Rm k mv
msole_many  = Sm Many
msole_k k   = Sm (mval k)
mopt        = Rm 0 (mval 1)

-- Checks that a multiplicity constraint is well-formed
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
mlbn (Sm Many) =  0
mlbn (Sm (Val k)) = k
mlbn (Rm k _) = k
mlb mc = Val $ mlbn mc

-- Functions mub, which gives the upper bound of a multiplicity constraint (Mult)
mub (Sm m) = m
mub (Rm _ m) = m

mult_mr (Rm n1 m_1) (Rm n2 m_2) = Rm (n1 * n2) (m_1 `mv_mult` m_2)

-- Complies to multiplicity (≬)
compliesm k m  = mlb m <= mval k && mval k <= mub m

-- Either multplicity (…)
eitherm k []     = False
eitherm k (m:ms) = k `compliesm` m || eitherm k ms

-- Checks whether 'm' is a many multiplicity
isMultMany [Sm Many]   = True
isMultMany [Rm 0 Many] = True
isMultMany _ = False

isMultVal_k [m] k = m == msole_k k 
isMultVal_k _ _ = False
isMultOpt [m] = m == mopt 
isMultOpt _ = False

-- Checks whether  m is a range or bounded multiplicity
isMultRange [Sm (Val k)] = k > 1
isMultRange [m@(Rm lb ub)] = lb >= 0 && (mval 2) <= ub && multcwf m
isMultRange _ = False

-- Unique, non-empty, individually well-formed and no manys allowed if more than one multiplicity in set
multwf ms = unique ms && length ms > 0 && all (\m->multcwf m) ms && ((length ms) > 1) `implies` (all (\m->not . isMultMany $ [m]) ms)

isMultEither ms = multwf ms && (length ms) > 1

-- Predicate 'allowedm' (∝) 
allowedm (Erel Dbi) (_, _) = True
allowedm Eder (_, _) = True
allowedm (Ecomp Duni) ([Sm (Val 1)], _) = True
allowedm (Erel Duni) (m1, _) = isMultMany m1
allowedm (Ecomp Dbi) (m1, _) = isMultVal_k m1 1 || isMultOpt m1
allowedm Ewander (m1, m2)    = isMultMany m1 && isMultMany m2
allowedm _ _                 = False


rbounded r s m = all (\x->length(img r [x]) `compliesm` m)  s
eitherbounded r s ms = all (\x->length(img r [x]) `eitherm` ms)  s

--
-- Predicate 'rmOk', which checks whether a multiplicity is satisfied by a given relation
multOk::Eq a=>[(a, a)]->[a]->[a]->Mult->Mult->Bool
multOk r s t m [Sm (Val 0)] = null $ rres r t  
multOk r s t [Sm (Val 0)] m = null $ dres r s
multOk r s t m [Sm (Val 1)]
    | m == [msole_k 1] = fun_bij r s t
    | m == [mopt]      = fun_inj r s t
    | isMultMany m     = fun_total r s t
    | isMultRange m    = fun_total r s t && rbounded (inv r) t (head m)
    | isMultEither m   = fun_total r s t && eitherbounded (inv r) t m
multOk r s t [Sm (Val 1)] m 
    | m == [mopt]      = fun_inj (inv r) t s
    | isMultMany m     = fun_total (inv r) t s
    | isMultRange m    = fun_total (inv r) t s && rbounded r s (head m)
    | isMultEither m   = fun_total (inv r) s t && eitherbounded r t m
multOk r s t m [Rm 0 (Val 1)]
    | m == [mopt]       = fun_pinj r s t
    | isMultMany m      = pfun r s t
    | isMultRange m     = pfun r s t && rbounded (inv r) t (head m)
    | isMultEither m    = pfun r s t && eitherbounded (inv r) t m
multOk r s t [Rm 0 (Val 1)] m
    | isMultMany m      = pfun (inv r) t s
    | isMultRange m     = pfun (inv r) t s && rbounded r s (head m) 
    | isMultEither m    = pfun (inv r) t s && eitherbounded r s m 
multOk r s t m1 m2 
    | all isMultMany [m1, m2]         = relation r s t
    | isMultMany m1 && isMultRange m2 = relation r s t && rbounded r s (head m2) 
    | isMultRange m1 && isMultMany m2 = relation r s t && rbounded (inv r) t (head m1)
    | all isMultRange [m1, m2]        = relation r s t && rbounded r s (head m2) && rbounded (inv r) t (head m1)
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


say_mv (Val k) = if k == 1 then "one" else (show k)
say_mv (Many) = "many (*)"

say_multc (Sm mv) = say_mv mv
say_multc (Rm 0 (Val 1)) = "optional (0..1)"
say_multc (Rm 0 Many) = say_mv (Many)
say_multc (Rm lb ub) = say_mv (mval lb) ++ ".." ++ (say_mv ub) 
say_mult [m] = say_multc m
say_mult ms = butLast (foldr (\m say->say ++ say_multc m ++ ",") "{" ms) ++ "}"

multc_err_msg me m1 m2 = (say_mult m1) ++ " to " ++ (say_mult m2) ++ " multiplicity constraint  of meta-edge " ++ (show me) ++ " is unsatisfied."

check_rbounded r s m = if rbounded r s m then nile else cons_se "Relation not within multiplicity bounds"
check_eitherbounded r s m = if eitherbounded r s m then nile else cons_se "Relation not within multiplicity bounds"

check_multOk::(Eq a, Show a, Eq b, Show b)=>b->[(a, a)]->[a]->[a]->Mult->Mult->ErrorTree
check_multOk me r s t m1 m2@[Sm (Val 0)] = if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) []
check_multOk me r s t m1@[Sm (Val 0)] m2 = if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) []
check_multOk me r s t m1 m2@[Sm (Val 1)] 
    | m1 == [msole_k 1] = if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) [check_fun_bij r s t]
    | m1 == [mopt]      = if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) [check_fun_inj r s t]
    | isMultMany m1     = if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) [check_fun_total r s t]
    | isMultRange m1    = 
        if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) [check_fun_total r s t, check_rbounded (inv r) t $ head m1] 
    | isMultEither m1   = if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) [check_fun_total r s t, check_eitherbounded (inv r) t m1]
check_multOk me r s t m1@[Sm (Val 1)] m2 
    | m2 == [mopt] = 
        if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) [check_fun_inj (inv r) t s]
    | isMultMany m2 = 
        if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) [check_fun_total (inv r) t s]
    | isMultRange m2 = 
        if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) [check_fun_total (inv r) t s, check_rbounded r s $ head m2] 
    | isMultEither m2   = if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) [check_fun_total (inv r) t s, check_eitherbounded r s m2]
check_multOk me r s t m1 m2@[Rm 0 (Val 1)]
    | m1 == [mopt]  = 
        if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) [check_fun_pinj r s t] 
    | isMultMany m1      = 
        if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) [check_pfun r s t] 
    | isMultRange m1     = 
        if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) [check_pfun r s t, check_rbounded (inv r) t $ head m1]
    | isMultEither m1   = if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) [check_pfun r s t, check_eitherbounded (inv r) t m1]
check_multOk me r s t m1@[Rm 0 (Val 1)] m2
    | isMultMany m2  = 
        if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) [check_pfun (inv r) t s]  
    | isMultRange m2 = 
        if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) [check_pfun (inv r) t s, check_rbounded (inv r) t $ head m2]
    | isMultEither m2 = if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) [check_pfun (inv r) t s, check_eitherbounded (inv r) t m2]
check_multOk me r s t m1 m2 
    | all isMultMany [m1, m2]         = 
        if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) [check_relation r s t]
    | isMultMany m1 && isMultRange m2 = 
        if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) [check_relation r s t, check_rbounded r s $ head m2]
    | isMultMany m1 && isMultEither m2 = 
        if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) [check_relation r s t, check_eitherbounded r s m2]
    | isMultRange m1 && isMultMany m2 = 
        if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) [check_relation r s t, check_rbounded (inv r) t $ head m1]
    | isMultEither m1 && isMultMany m2 = 
        if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) [check_relation r s t, check_eitherbounded (inv r) t  m1]
    | all isMultRange [m1, m2]        = 
        if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) [check_relation r s t, check_rbounded r s $ head m2, check_rbounded (inv r) t $ head m1]
    | all isMultEither [m1, m2] = if multOk r s t m1 m2 then nile else cons_et (multc_err_msg me m1 m2) [check_relation r s t, check_eitherbounded r s m2, check_eitherbounded (inv r) t m1]

mult_err_msg me = "Multiplicity errors in " ++ (show me)


--check_multOk::(Eq a, Show a)=>a->[(a, a)]->[a]->[a]->Mult->Mult->ErrorTree
--check_multOk me r s t m1 m2 = if multOk r s t m1 m2 then nile else check_multOka m1 m2
--   where check_multOka [m1] [m2] = check_multcOk me r s t m1 m2
--         check_multOka _ [] = nile
--         check_multOka [] _ = nile
--         check_multOka [m1] (m2:ms) = concat_ets (mult_err_msg me) (check_multcOk me r s t m1 m2) (check_multOk me r s t [m1] ms)
--         check_multOka (m1:ms) [m2] = concat_ets (mult_err_msg me) (check_multcOk me r s t m1 m2) (check_multOk me r s t ms [m2])
--         check_multOka (m:ms1) ms2 = concat_ets (mult_err_msg me) (check_multOk me r s t [m] ms2) (check_multOk me r s t ms1 ms2)

