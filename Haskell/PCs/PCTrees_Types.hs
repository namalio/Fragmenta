module PCs.PCTrees_Types (
    Type(..)
    , Subst
    , isEventTy
    , apply
    , freeVars
    , applySS
    , scomp
    , Env
    , nilEnv
    , applyEnv
    , removeFrEnv)
    where

import PCs.PCsCommon(Id)
import PCs.PCTrees_AST 
import Relations
import Sets
import TheNil
import PCs.SymbMap 

data Type 
    = TBool
    | TInt
    | TEvent
    | TData
    | TProc
    | TId Id -- An instance of a custom data type
    | TDt Id -- A custom data type
    | TDot Type Type 
    | TSet Type 
    -- | Dottable Type Type 
    | TFun Type Type 
    deriving (Eq, Show)

type Subst = Rel Id Type

isEventTy::Type->Bool
isEventTy TEvent = True
isEventTy (TDot _ t) = isEventTy t
isEventTy _ = False


freeVars::Type->Set Id
freeVars TBool = nil
freeVars TInt = nil
freeVars TEvent = nil
freeVars TData = nil
freeVars TProc = nil
freeVars (TId id) = set1 id
freeVars (TDt id) = set1 id
freeVars (TDot t1 t2) = freeVars t1 `union` freeVars t2
freeVars (TSet t) = freeVars t
--freeVars (Dottable t1 t2) = freeVars t1 `union` freeVars t2
freeVars (TFun t1 t2) = freeVars t1 `union` freeVars t2

apply :: Subst->Type->Type
apply _ TBool = TBool
apply _ TInt = TInt
apply _ TEvent = TEvent
apply _ TData = TData
apply _ TProc = TProc
apply s t@(TId id) = if id `elem` dom_of s then appl s id else t
apply _ t@(TDt id) = t
apply s (TDot t1 t2) =  (apply s t1) `TDot` (apply s t2)
apply s (TSet t) = TSet (apply s t)
--apply s (Dottable t1 t2) = Dottable (apply s t1) (apply s t2)
apply s (TFun t1 t2) = TFun (apply s t1) (apply s t2)

applySS::Subst->Subst->Subst
applySS s1 s0 = fmap (\(i, t)->(i, apply s1 t)) s0

scomp::Subst->Subst->Subst
scomp s1 s0 = s1 `override` (applySS s1 s0) 

-- Environments: A mapping from identifiers to types
type Env = SymMap Id Type 

-- The empty environment
nilEnv::Env
nilEnv = emptySM 

applyEnv::Subst->Env->Env
applyEnv s env = 
    smap $ applyEnv0 s (rel env)
    where
       applyEnv0 s EmptyS = EmptyS
       applyEnv0 s (Set (id, t) r) = (id, apply s t) `intoSet` applyEnv0 s r

removeFrEnv::Foldable t=>Env->t Id->Env
removeFrEnv env ids = delKeys env ids