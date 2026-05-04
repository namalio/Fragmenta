
module PCs.PCTrees_TypeErrors (TyError(..), errorMsg)

where

import PCs.Common(Id)
import ShowUtils
import PCs.TxtExpAST

type OpS = String
type Ty = String
type SE = String
data TyError 
    = IdExists Id 
    | TyUnknown Id 
    | IncompatibleTypesInArithmeticExp Exp OpS
    | NotIntegerExp Exp
    | IncompatibleTypesInBooleanExp Exp String 
    | NotBooleanExp Exp
    | ExpNotOfExpectedType Exp Ty Ty 
    | InvalidAtomExpression Exp 
    | ParamIdNotUnique Id Id
    | CouldNotMatchExpectedType Ty Ty
    | IncompatibleTypesInExp OpS Ty Ty
    | IncompatibleTypesInUExp OpS Ty
    | TypesDoNotUnify Ty Ty
    | UnificationOccursError Id Ty
    | NoMatchingEvents [String]
    | InvalidReferenceToProcess Id
    | ProcessAlreadyDefined Id
    | NotOfEventType Id Ty
    | NotOfDotType Id Ty
    | ExpNotOfIdType Exp 
    | ProcessDeclNotCompound Id
    deriving (Show)

errorMsg::TyError->String
errorMsg (IdExists id) = "Name '" ++ id ++ "' has already been used."
errorMsg (TyUnknown id) = "Type of identifier '" ++ id ++ "' is unknown."
errorMsg (IncompatibleTypesInArithmeticExp e op) = 
    "The types of the two individual expressions combined through arithmentic operator '" ++ op ++ "'"
    ++ " are invalid in expression " ++ show e
errorMsg (NotIntegerExp e) = 
    "Expression " ++ show e ++ " is neither of type integer, nor of a type compatible to integer, such as None."
errorMsg (IncompatibleTypesInBooleanExp e op) = 
    "The types of the two individual expressions combined through the boolean operator '" ++ op ++ "' "
    ++ " are invalid in expression " ++ show e
errorMsg (NotBooleanExp e) = "Expression '" ++ show e ++ "' is neither of type boolean, nor of a type compatible to boolean, such as None."
errorMsg (ExpNotOfExpectedType e ta te) = 
    "Expression '" ++ (show e) ++ "' has type '" ++ ta ++ "' is neither of expected type '" ++ te ++ "'"
    ++ " nor of a compatible type."
errorMsg (InvalidAtomExpression e) = "Expression '" ++ show e ++ "' is invalid. The expression of an atom "
    ++ "must consist of an identifier or a dottable expression."
errorMsg (ParamIdNotUnique idk idp) = 
    "Parameter identifier '" ++ idp ++ "' of compound '" ++ idk ++ "' is not unique."
errorMsg (CouldNotMatchExpectedType ety aty) = 
    "Wrong expected type: expecting " ++ ety ++ " but got " ++ aty
errorMsg (IncompatibleTypesInExp opS ty1 ty2) =
    "Incompatible types in expression involving operator" ++ opS ++ ", where the types are: " ++ ty1 ++ ", " ++ ty2
errorMsg (IncompatibleTypesInUExp opS ty) =
    "Incompatible types in unary expression involving operator" ++ opS ++ ", where the type is: " ++ ty
errorMsg (NoMatchingEvents ids) =
    "There are no known events for some of the ids in the set " ++ (showStrs ids ",") ++ "."
errorMsg (UnificationOccursError id t) = 
    "Could not unify " ++ id ++ " with " ++ t
errorMsg (TypesDoNotUnify t1 t2) = 
    "Could not unify type " ++ t1 ++ " with " ++ t2
errorMsg (InvalidReferenceToProcess id) = 
    "Reference to process " ++ id ++ " is invalid; the process is undefined in the current context."
errorMsg (ProcessAlreadyDefined id)= 
    "Process " ++ id ++ " is already defined in the current context."
errorMsg (NotOfEventType id ty) = 
    "Name '" ++ id++ "' has type '" ++ (show ty) ++ "', which is not an event type." 
errorMsg (NotOfDotType id ty) = 
    "Name '" ++ id++ "' has type '" ++ (show ty) ++ "', which is not a dot composable type." 
errorMsg (ExpNotOfIdType e) = 
    "Expression '" ++ show e ++ "' is not of an id type (no name within)."
errorMsg (ProcessDeclNotCompound id) = 
    "Process declarations must be process compounds:" ++ id
    
--errorMsg e =  show e