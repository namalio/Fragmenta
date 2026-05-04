module PCs.Common 
    ( Id
    , Type
    , Param(..)
    , cParam
    , OpKind(..)
    , readOp
    , toMMOp
    )
where

import ParseUtils
import PCs.MM_Names
import TheNil
import MyMaybe
import SimpleFuns
   ( startsWith
   )

type Id = String
data Type 
    = Int 
    | Bool 
    | Event 
    | Dt Id
    | Set Type 
    deriving (Eq, Show)

show_ty (Dt id) = id
show_ty (Set t) = "Set " ++ show_ty t
show_ty t = show t


data Param = Param Id (Maybe Type)
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
   show (Param nm oty) = nm ++ (if isSomething oty then " : " ++ (show_ty $ the oty) else "")

instance Show OpKind where
    show Choice = "◻︎"
    show IntChoice = "⊓"
    show Parallel = "||"
    show Interleave = "|||"
    show Throw = "Θ"
    show If = "If"

readOp :: PCs_CMM_Ns -> OpKind
readOp CMM_VOpIf            = If
readOp CMM_VOpExtChoice        = Choice
readOp CMM_VOpIntChoice     = IntChoice
readOp CMM_VOpParallel      = Parallel
readOp CMM_VOpInterleave    = Interleave
readOp CMM_VOpThrow         = Throw

toMMOp::OpKind->PCs_CMM_Ns
toMMOp If = CMM_VOpIf   
toMMOp Choice = CMM_VOpExtChoice
toMMOp IntChoice = CMM_VOpIntChoice
toMMOp Parallel = CMM_VOpParallel 
toMMOp Interleave = CMM_VOpInterleave
toMMOp Throw = CMM_VOpThrow

readType::Id->Type
readType "Integer"          = Int
readType "Boolean"          = Bool
readType "Event"            = Event
readType s 
   | startsWith "Dt_" s = Dt $ drop 3 s
   | startsWith "Set_" s = Set $ readType (drop 4 s)
--ctype0 ('D':'t':'_':rest) = Dt rest
--cType0 sty                = let (_, ty) = splitAtStr "Set_" sty in Set (cType0 ty)

cType::Maybe Id->Maybe Type
cType Nothing = Nothing
cType (Just ts) = Just $ readType ts

cParam::Id->Maybe String->Param
cParam id tys = Param id (cType tys)