module PCs.PCTrees_Types (
    Type(..)
    , Subst
    , apply
    , freeVars
    , applySS
    , scomp)
    --, isNone
    --, hasNone)
    where

import PCs.PCsCommon(Id)
import PCs.PCTrees_AST 
import Relations
import Sets
import TheNil

--data PType 
--    = TBool 
--    | TInt 
--    | TEvent 
--    | TData 
--    | TProc 
--    | TId Id 
--    deriving (Eq, Show)

data Type 
    = TBool
    | TInt
    | TEvent
    | TData
    | TProc
    | TId Id -- A generic data type
    | TDt Id -- A custom data type
    | TDot Type Type 
    | TSet Type 
    --| Dottable Type Type 
    | TFun Type Type -- Is this needed?
    deriving (Eq, Show)

type Subst = Rel Id Type

--class TYOPS a where
--    freeVars ::  a -> Set Id
--    apply :: Subst->a->a

--instance TYOPS PType where
--    freeVars::PType->Set Id
--   freeVars TBool = nil
--    freeVars TInt = nil
--    freeVars TEvent = nil
--    freeVars TProc = nil
--    freeVars (TId id) = set1 id
--    apply s t@(TId id) = if id `elem` dom_of s then appl s id else t
--    apply _ t = t


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

--apply :: Subst->Type->Type
--apply s t 
--    | t `elem` [TBool, TInt, TEvent, TProc] = t
--    | otherwise = apply0
--    where 
--        apply0 t@(TId id) = if id `elem` dom_of s then appl s id else t
--        apply0 (Dot t1 t2) = Dot (apply s t1) (apply s t2)
--        apply0 (SetT t) = SetT (apply s t)
--        apply0 (Dottable t1 t2) = Dottable (apply s t1) (apply s t2)
--        apply0 (Fun t1 t2) = Fun (apply s t1) (apply s t2)

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

--instance Ord PType where
--    TNone <= _ = True
--    t1 <= t2 = t1 == t2
--        | t1 == t2 = True
--        | otherwise = t1 <= t2

--instance Ord Type where
--    PTy t1 <= PTy t2 = t1 <= t2
--    Fun t1 t2 <= Fun y1 y2 = t1 <= y1 && t2 <= y2
--    _ <= _ = False


--isNone::Type->Bool
--isNone (PTy TNone) = True
--isNone _ = False 

--hasNone::Type->Bool
--hasNone (PTy pt) = pt == TNone
--hasNone (Dot t1 t2) = hasNone t1 || hasNone t2
--hasNone (Set t) = hasNone t
--hasNone (Dottable t1 t2) = hasNone t1 || hasNone t2
--hasNone (Fun t1 t2) = hasNone t1 || hasNone t2