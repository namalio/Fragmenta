{-# OPTIONS_GHC -Wno-x-partial -Wno-unrecognised-warning-flags #-}
module PCs.Common 
    ( Id
    , PCTypeD(..)
    , Param(..)
    , OpKind(..)
    , readOp
    , toMMOp
    , read_opctyd
    , cParam
    , cType
    , gParamId
    , gParamTy
    , PCTypeE(..)
    , show_pctye
    , startN
    )
where

import ParseUtils
   (words'
   ,splitAt')
import PCs.MM_Names
import TheNil
import MyMaybe
import SimpleFuns
   ( startsWith
   )

type Id = String

-- A PCT type designator — int, bool, event, some custom datatype, or some set of some type
data PCTypeD 
    = Int 
    | Bool 
    | Event 
    | Dt Id
    | SetT PCTypeD 
    deriving (Eq)

instance Show PCTypeD where
  show :: PCTypeD -> String
  show Int = "Int"
  show Bool = "Bool"
  show Event = "Event"
  show (Dt id) = strip id 
    where strip('D':'t':'_':rest) = rest
          strip s = s
  show (SetT t) = "Set " ++ show t

--show_ty (Dt id) = id
--show_ty (SetT t) = "Set " ++ show_ty t
--show_ty t = show t

instance Read PCTypeD where
    --read :: String -> PCTypeD
    readsPrec _ c = 
        let (s, r) = splitAt' (== ' ') c
        in case s of
            "Int" -> [(Int, r)]
            "Bool"    -> [(Bool, r)]
            "Event"   -> [(Event, r)]
            "Set"     -> let (s', r') = splitAt' (== ' ') r in [(SetT $ read s', r')]
            "Dt"      -> let (s', r') = splitAt' (== ' ') r in [(Dt $ read s', r')]
            _         ->[(Dt s, r)]
              
    --readsPrec s 
    --    | startsWith "Dt_" s = Dt $ drop 3 s
    --    | startsWith "Set_" s = SetT $ readsPrec (drop 4 s)

--readType::Id->PCType
--readType "Integer"          = Int
--readType "Boolean"          = Bool
--readType "Event"            = Event
--readType s 
--   | startsWith "Dt_" s = Dt $ drop 3 s
--   | startsWith "Set_" s = SetT $ readType (drop 4 s)

read_opctyd :: Maybe String -> Maybe PCTypeD
read_opctyd Nothing = Nothing
read_opctyd (Just s) = Just $ read s

data Param = Param Id (Maybe PCTypeD)
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
   show (Param nm oty) = nm ++ (if isSomething oty then " : " ++ (show $ the oty) else "")

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

-- The name of the start node constant
startN::String
startN = "StartN_"

cType::Maybe Id->Maybe PCTypeD
cType Nothing = Nothing
cType (Just ts) = Just $ read ts

cParam::Id->Maybe String->Param
cParam id tys = Param id (cType tys)

gParamId::Param->Id
gParamId (Param id _) = id

gParamTy::Param->Maybe PCTypeD
gParamTy (Param _ t) = t

-- Data type for type expressions
data PCTypeE
   = TyD PCTypeD
   | TIdE Id  
   | SetE [Id] -- A set extension
    deriving (Eq)

show_pctye::PCTypeE->String
show_pctye (TyD Int)   = "Int"
show_pctye (TyD Bool)  = "Bool"
show_pctye (TyD Event) = "Event"
show_pctye (TIdE id)   = "Id_" ++ id
show_pctye (SetE ids)  = "SetE_" ++ foldr (\id' s->id' ++ "_" ++ s) "" ids

instance Show PCTypeE where
    show (TyD td)   = show td
    show (TIdE id)   = id
    show (SetE ids) = "{" ++ foldr (\id' s->id' ++ (if null s then "" else ",") ++ s) "" ids ++ "}"

instance Read PCTypeE where
    readsPrec _ c = 
        let (s, r) = span (/= ' ') c
        in case s of
            "Int" -> [(TyD Int, r)]
            "Bool"    -> [(TyD Bool, r)]
            "Event"   -> [(TyD Event, r)]
            'I':'d':'_':r' -> [(TIdE r', r)]
            'S':'e':'t':'E':'_':r' -> [(SetE $ words' (=='_') r', r)]
            _ -> error s