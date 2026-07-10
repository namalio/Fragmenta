module PCs.PCTrees_Types (
    Type(..)
    , Subst
    , isEvTy
    , isDotTy
    , apply
    , freeVars
    , applySS
    , scomp
    , Env
    , nilEnv
    , applyEnv
    , removeFrEnv
    , inEnv
    , isSetTy
    , isTIdTy
    )
    where

import PCs.Common(Id)
import PCs.PCTreesAST 
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

isEvTy::Type->Bool
isEvTy TEvent = True
isEvTy (TDot _ t) = isEvTy t
isEvTy _ = False

isDotTy::Type->Bool
isDotTy (TDot _ _) = True
isDotTy _ = False

isSetTy::Type->Bool
isSetTy (TSet _ ) = True
isSetTy _ = False

isTIdTy::Type->Bool
isTIdTy (TId _) = True
isTIdTy _ = False
--fstTy::Type->Type
--fstTy (TDot t1 _) = t1
--fstTy (TSet t) = t
--fstTy (TFun t _) = t

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

-- Environments: A relation from identifiers to types
type Env = Rel Id Type 

-- The empty environment
nilEnv::Env
nilEnv = nil

applyEnv::Subst->Env->Env
applyEnv s EmptyS = EmptyS
applyEnv s (Set (id, t) r) = (id, apply s t) `intoSet` applyEnv s r

--applyEnv s env = 
--    smap $ applyEnv0 s (rel env)
--    where
--       applyEnv0 s EmptyS = EmptyS
--       applyEnv0 s (Set (id, t) r) = (id, apply s t) `intoSet` applyEnv0 s r

inEnv::Id->Env->Bool
inEnv id env = id `elem` (dom_of env)

removeFrEnv::Foldable t=>Env->t Id->Env
removeFrEnv env ids = dsub env ids