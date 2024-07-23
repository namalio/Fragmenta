module PCs.PCsCommon (Id
    , Type
    , Param(..)
    , cParam)
where

import ParseUtils

type Id = String
data Type = Int | Bool | Event | Set Type
    deriving (Eq, Show)
data Param = Param Id Type
    deriving(Eq) 

instance Show Param where
   show (Param nm ty) = nm ++ " : " ++ (show ty)

cType::Id->Type
cType "Integer" = Int
cType "Boolean" = Bool
cType "Event" = Event
cType sty = 
    let (_, ty) = splitAtStr "Set " sty in 
    Set (cType ty)

cParam::Id->String->Param
cParam id tys = Param id (cType tys)