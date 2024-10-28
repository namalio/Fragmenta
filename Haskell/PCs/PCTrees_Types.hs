module PCs.PCTrees_Types (
    PType(..)
    , Type(..)
    , isNone
    , hasNone)
    where

import PCs.PCsCommon(Id)
import PCs.PCTrees_AST 

data PType = TBool | TInt | TNone | TEvent | TData | TProc | TId Id 
    deriving (Eq, Show)

data Type = PTy PType | Dot Type Type | Set Type | Dottable Type Type 
    | Fun Type Type
    deriving (Eq, Show)

instance Ord PType where
    TNone <= _ = True
    t1 <= t2 = t1 == t2
--        | t1 == t2 = True
--        | otherwise = t1 <= t2

instance Ord Type where
    PTy t1 <= PTy t2 = t1 <= t2
    Fun t1 t2 <= Fun y1 y2 = t1 <= y1 && t2 <= y2
    _ <= _ = False


isNone::Type->Bool
isNone (PTy TNone) = True
isNone _ = False 

hasNone::Type->Bool
hasNone (PTy pt) = pt == TNone
hasNone (Dot t1 t2) = hasNone t1 || hasNone t2
hasNone (Set t) = hasNone t
hasNone (Dottable t1 t2) = hasNone t1 || hasNone t2
hasNone (Fun t1 t2) = hasNone t1 || hasNone t2