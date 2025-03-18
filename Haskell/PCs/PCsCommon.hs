module PCs.PCsCommon (Id
    , Type
    , Param(..)
    , cParam
    , OpKind(..)
    , readOp
    , toMMOp)
where

import ParseUtils
import PCs.PCs_MM_Names

type Id = String
data Type 
    = Int 
    | Bool 
    | Event 
    | Set Type 
    | None
    deriving (Eq, Show)

data Param = Param Id Type
    deriving(Eq) 

data OpKind 
    = Choice 
    | IntChoice 
    | Interleave 
    | Throw 
    | If 
    | Parallel
   deriving(Eq, Read) 

instance Show Param where
   show (Param nm ty) = nm ++ " : " ++ (show ty)

instance Show OpKind where
    show Choice = "◻︎"
    show IntChoice = "⊓"
    show Parallel = "||"
    show Interleave = "|||"
    show Throw = "Θ"
    show If = "If"

readOp :: PCs_CMM_Ns -> OpKind
readOp CMM_VOpIf            = If
readOp CMM_VOpChoice        = Choice
readOp CMM_VOpIntChoice     = IntChoice
readOp CMM_VOpParallel      = Parallel
readOp CMM_VOpInterleave    = Interleave
readOp CMM_VOpThrow         = Throw

toMMOp::OpKind->PCs_CMM_Ns
toMMOp If = CMM_VOpIf   
toMMOp Choice = CMM_VOpChoice
toMMOp IntChoice = CMM_VOpIntChoice
toMMOp Parallel = CMM_VOpParallel 
toMMOp Interleave = CMM_VOpInterleave
toMMOp Throw = CMM_VOpThrow

cType0::Id->Type
cType0 "Integer" = Int
cType0 "Boolean" = Bool
cType0 "Event" = Event
cType0 sty = let (_, ty) = splitAtStr "Set " sty in Set (cType0 ty)

cType::Maybe Id->Type
cType Nothing = None
cType (Just ts) = cType0 ts

cParam::Id->Maybe String->Param
cParam id tys = Param id (cType tys)