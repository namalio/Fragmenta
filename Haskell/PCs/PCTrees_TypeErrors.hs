
module PCs.PCTrees_TypeErrors (TyError(..), errorMsg)

where

import PCs.PCsCommon(Id)
import PCs.PCTrees_Exp
import ShowUtils

type OpS = String
type Ty = String
type SE = String
data TyError = IdExists Id | TyUnknown Id 
    | IncompatibleTypesInArithmeticExp PCE String | NotIntegerExp String
    | IncompatibleTypesInBooleanExp PCE String | NotBooleanExp PCE
    | ExpNotOfExpectedType SE Ty Ty | AtomTypeCannotIncludeNone PCEAtom
    | InvalidAtomExpression PCEAtom | ParamIdNotUnique Id Id
    | CouldNotMatchExpectedType Ty Ty
    | IncompatibleTypesInExp OpS Ty Ty
    | IncompatibleTypesInUExp OpS Ty
    | IncompatibleTypesInCompoundReferences Id Ty Ty 
    | TypesDoNotUnify Ty Ty
    | UnificationOccursError Id Ty
    | NoMatchingEvents [String]
    deriving (Show)

errorMsg::TyError->String
errorMsg (IdExists id) = "Name '" ++ id ++ "' has already been used."
errorMsg (TyUnknown id) = "Type of '" ++ id ++ "' is unknown."
errorMsg (IncompatibleTypesInArithmeticExp e op) = 
    "The types of the two individual expressions combined through arithmentic operator '" ++ op ++ "'"
    ++ " are invalid in expression " ++ show e
errorMsg (NotIntegerExp e) = 
    "Expression " ++ show e ++ " is neither of type integer, nor of a type compatible to integer, such as None."
errorMsg (IncompatibleTypesInBooleanExp e op) = 
    "The types of the two individual expressions combined through the boolean operator '" ++ op ++ "' "
    ++ " are invalid in expression " ++ show e
errorMsg (NotBooleanExp e) = "Expression '" ++ show e ++ "' is neither of type boolean, nor of a type compatible to boolean, such as None."
errorMsg (ExpNotOfExpectedType se ta te) = 
    "Expression '" ++ se ++ "' has type '" ++ ta ++ "' is neither of expected type '" ++ te ++ "'"
    ++ " nor of a compatible type, such as None."
errorMsg (AtomTypeCannotIncludeNone e) = 
    "A type of an atom expression cannot involve undertermined type None as is the case in expression '"
    ++ show e ++ "'"
errorMsg (InvalidAtomExpression e) = "Expression '" ++ show e ++ "' is invalid. The expression of an atom "
    ++ "must consist of an identifier or a dottable expression."
errorMsg (ParamIdNotUnique idk idp) = 
    "Parameter identifier '" ++ idp ++ "' of compound '" ++ idk ++ "' is not unique."
errorMsg (CouldNotMatchExpectedType ety aty) = 
    "Wrong expected type: expecting " ++ ety ++ " but got " ++ aty
errorMsg (IncompatibleTypesInExp opS ty1 ty2) =
    "Incompatible types in expression involving operator" ++ opS ++ ", where the types are: " ++ ty1 ++ ", " ++ ty2
errorMsg (NoMatchingEvents ids) =
    "There are no known events for some of the ids in the set " ++ (showStrs ids ",") ++ "."
errorMsg (UnificationOccursError id t)= 
    "Could not unify " ++ id ++ " with " ++ t