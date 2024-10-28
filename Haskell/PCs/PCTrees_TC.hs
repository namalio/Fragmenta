--------------------------------
-- Project: PCs
-- Module: 'PCTressTC'
-- Description: Type-checking of PCT representations of PCs
-- Author: Nuno Amálio
--------------------------------

module PCs.PCTrees_TC(
    typecheck_pctd
)
where

import PCs.PCTrees_Types
import PCs.PCTrees_AST
import Relations
import Sets
import PCs.PCsCommon(Id, OpKind)
import PCs.SymbMap
import PCs.PCTrees_TypeErrors
import TheNil
import Data.Fixed (E1)
import Control.Monad ( foldM, when)
import MyMaybe
import PCs.PCTrees_Exp

--type Env = SymMap Id Type 

data Env = Env {
    sm_::SymMap Id Type, 
    cnts_::Rel Id Type}
    deriving (Show)

empty_env::Env
empty_env = Env{sm_ = emptySM, cnts_ = nil} 

upd_sm::Env->SymMap Id Type->Env
upd_sm env sm = Env {sm_ = sm, cnts_ = cnts_ env} 

add_Kcnt::Env->Id->Type->Env
add_Kcnt env id t = Env {sm_ = sm_ env, cnts_ = singles (id, t) `union` (cnts_ env)} 

get_Kcnts::Env->Id->Set Type
get_Kcnts env id = img (cnts_ env) [id]

--rm_ref::Env->Id->(Maybe Ref, Env)
--rm_ref env id = (applM  (urs_ env) id, Env {sm_ = sm_ env, urs_ = dsub (urs_ env) (singles id)})

--is_unresolved::Env->Id->Bool
--is_unresolved env id = id `elem` dom_of (urs_ env)

data TyErr a = Ok a | Fail TyError
    deriving (Show)

instance The TyErr where
   the :: TyErr a -> a
   the (Ok x) = x

instance Functor TyErr where
    fmap f (Ok t) = Ok $ f t
    fmap _ (Fail te) = Fail te

instance Applicative TyErr where
    pure = Ok
    Fail te <*> _ = Fail te
    Ok f <*> te = fmap f te

instance Monad TyErr where
    return = pure
    Fail err >>= _ = Fail err
    Ok o >>= f = f o

--isErr::TyErr a->Bool
--isErr (Fail _) = True
--isErr _ = False

failure::TyError->TyErr a 
failure = Fail

class TypeOf_PCT a where
    typeOf::a->Env->TyErr Type

--type EnvWithErr = Either TyError Env

instance TypeOf_PCT PCTTypeD where
    typeOf Int _ = return $ PTy TInt
    typeOf Bool _ = return $ PTy TBool
    typeOf (DT id) _ = return $ PTy TData


lookupId::Env->Id->TyErr Type
lookupId env id = do
    let ot = PCs.SymbMap.lookup (sm_ env) id
    if isNil ot then 
        do failure (TyUnknown id)
    else do return (the ot)

instance TypeOf_PCT PCEAtom where
    typeOf (IdExp id) env = lookupId env id
    typeOf (NumExp _) _ = return $ PTy TInt
    typeOf TrueExp _ = return $ PTy TBool
    typeOf FalseExp _ = return $ PTy TBool
    typeOf (ParExp  e) env =  typeOf e env 
    typeOf (DotExp id e) env = do
        t<-lookupId env id 
        t2<-typeOf e env 
        return $ Dot t t2

checkBinaryExp::PCE->PCEAtom->PCE->Env->PCEBinOp->TyErr Type
checkBinaryExp e e1 e2 env op = do
    let et = if op `elem` [And, Or] then PTy TBool else PTy TInt
    t1 <- typeOf e1 env 
    t2 <- typeOf e2 env 
    --failure $ Test (show t2)
    if t1 <= t2 || t2 <= t1 then
        do return et
        else failure (IncompatibleTypesInArithmeticExp e (show op))
    

--checkBinaryArithExp::PCExp->PCExpAtom->PCExp->Env->String->TyErr Type
--checkBinaryArithExp e e1 e2 env op = do
--    t1 <- typeOf e1 env 
--    t2 <- typeOf e2 env 
--    if t1 <= PTy TInt && t2 <= PTy TInt then
--        do return $ PTy TInt
--        else failure (IncompatibleTypesInArithmeticExp e op)

--checkBinaryBoolExp::PCExp->PCExp->PCExp->Env->String->TyErr Type
--checkBinaryBoolExp e e1 e2 env op = do
--    t1 <- typeOf e1 env 
--    t2 <- typeOf e2 env 
--    if t1 <= PTy TBool && t2 <= PTy TBool then
--        do return $ PTy TBool
--        else failure (IncompatibleTypesInBooleanExp e op)

checkUnaryExp::PCEUnOp->PCE->PCE->Env->TyErr Type
checkUnaryExp UMinus e e1 env = do
    t<-typeOf e env 
    if t <= PTy TInt then
        do return $ PTy TInt
    else 
        do failure $ NotIntegerExp (show e)
checkUnaryExp UNot e e1 env = do
    t<-typeOf e env 
    if t <= PTy TBool then
        do return $ PTy TBool
    else 
        do failure $ NotBooleanExp e

checkRelOpExp::PCERelOp->PCEAtom->PCE->Env->TyErr Type
checkRelOpExp op ea e env = do
    t1<-typeOf ea env
    t2<-typeOf e env
    if t1 <= PTy TInt && t2 <= PTy TInt then
        do return $ PTy TBool
    else 
        if not $ t1 <= PTy TInt then
           do failure $ NotIntegerExp (show ea)
        else
           do failure $ NotIntegerExp (show e)

instance TypeOf_PCT PCE where
    typeOf (ExpAtom ea) env = typeOf ea env 
    typeOf e@(BinExp op e1 e2) env = checkBinaryExp e e1 e2 env op
    typeOf e@(UnExp op e1) env = checkUnaryExp op e e1 env
    typeOf (RelOpExp op ea e) env = checkRelOpExp op ea e env


class TypeCheck_PCT a where
    typecheck::a->Env->TyErr Env


newId::Id->Env->Type->TyErr Env
newId id env ty 
   | keyOf id (sm_ env) = failure (IdExists id)
   | otherwise = return (upd_sm env (put (sm_ env) id ty))

instance TypeCheck_PCT DTDef where
    typecheck (DTDef id ids) env = 
        newId id env (PTy TData) >>= do_ids
        where do_ids env' = foldl (\tcr' id'->tcr'>>= \env''->newId id' env'' (PTy $ TId id)) (return env') ids

instance TypeCheck_PCT [DTDef] where
    typecheck ds env = foldl (\tcr d->tcr>>=(\env'-> typecheck d env)) (return env) ds

--checkIsOfType::PCExpAtom->Env->Type->TyErr ()
checkIsOfType :: (TypeOf_PCT a, Show a) => a -> Env -> Type -> TyErr ()
checkIsOfType e env t = do
    t1<-typeOf e env 
    if t1 <= t then do
        return ()
    else do
        failure $ ExpNotOfExpectedType (show e) (show t1) (show t)

checkIdsUnique::Id->[Id]->TyErr ()
checkIdsUnique _ [] = return ()
checkIdsUnique idk (x:xs) = 
    if x `elem` xs then failure (ParamIdNotUnique idk x) else checkIdsUnique idk xs

checkParams::Id->[Param]->Env->TyErr Env
checkParams idk ps env = do
    checkIdsUnique idk (map gParamId ps)
    return $ foldl (\env' p->upd_sm env (put (sm_ env') (gParamId p) (gty p env'))) env ps
    where
        gty p env = if gParamTyD p == nil then PTy TNone else the $ typeOf (the . gParamTyD $ p) env

strongest::Id->Type->Type->TyErr Type
strongest _ t@(PTy TProc) (PTy TProc) = return t
strongest id (Fun t t') (Fun y y') = do
    let ost =  pick_strogest t y
    if isNil ost then
        do failure $ IncompatibleTypesInCompoundReferences id (show t) (show t')
    else 
        do return $ Fun y (the ost)
    where pick_strogest t t' 
             | t <= y = Just y 
             | y <= t = Just t
             | otherwise = Nothing


strongest_type::Id->Set Type->TyErr (Maybe Type)
strongest_type id EmptyS = return Nothing
strongest_type id (Sets.Set t ts) = foldM (strongest id) t ts >>= return . Just

updParamTys::Type->[Param]->Env->TyErr Env
updParamTys (PTy TProc) [] env = return env
updParamTys (Fun t t') (p:ps) env = do
    t''<-lookupId env (gParamId p)
    (if t''<= t then 
        do return $ upd_sm env $ put (sm_ env) (gParamId p) t
    else 
        do return env) >>= updParamTys t' ps

instance TypeCheck_PCT PDT where
    typecheck (PDT id ps cts pct) env = do
        -- checks well-formedness of parameters
        env1<-checkParams id ps env
        -- calculates type of compound
        t <- foldM (\t p->do
            t'<-lookupId env1 (gParamId p)
            return (Fun t' t)) (PTy TProc) ps
        -- Checks if there are constraints associated with the type
        ost <- strongest_type id $ get_Kcnts env1 id
        --failure $ Test (show ost)
        let t' = if isSomething ost then if t<= the ost then the ost else t else t 
        env2<-if isSomething ost then 
                 do updParamTys (the ost) ps env1
              else do return env1 
        (newId id env2 t' >>= typecheck cts)>>=typecheck pct
        --where updParamTys (PTy TProc) [] env = env
        --      updParamTys (Fun t t') (p:ps) env = 
        --         lookupId env (gParamId p) >>= \t''->if t<= t''then 
        --env3<-typecheck pct env2
        --if id == "CCVM" then
        --    do failure $ Test (show env3)
        --else do return env2
        --env3<-typecheck pct env2
        -- 

instance TypeCheck_PCT [PDT] where
    typecheck cts env = 
        foldM (\env' ct->typecheck ct env') env cts 
        --    env2<-typecheck ct env'
        --    if idCT ct == "CCVM" then
        --        do failure $ Test (show env2)
        --    else do 
        --        return env2) env cts 

instance TypeCheck_PCT TOp where
    typecheck OpExtChoice env = return env
    typecheck OpIntChoice env = return env
    typecheck (OpSeq _) env = return env
    typecheck (OpParallel es) env = 
        foldl (\r e->r>>checkIsOfType e env (PTy TEvent)) (return ()) es >> return env
    typecheck OpInterleave env = return env
    typecheck (OpThrow es) env = 
        foldl (\r e->r>>checkIsOfType e env (PTy TEvent)) (return ()) es >> return env
    typecheck (OpIf e) env = 
        checkIsOfType e env (PTy TBool) >> return env

checkGuard::Maybe PCE->Env->TyErr ()
checkGuard Nothing env = return ()
checkGuard (Just eg) env = checkIsOfType eg env (PTy TBool)

checkAtom::PCEAtom->Maybe PCE->Env->TyErr Env
checkAtom e@(IdExp id) og env = do
    checkGuard og env
    let ot = PCs.SymbMap.lookup (sm_ env) id
    if isNil ot then 
        do return $ upd_sm env (put (sm_ env) id (PTy TEvent))
    else do
        checkIsOfType e env (PTy TEvent)
        return env
checkAtom (DotExp id e) og env = do 
    checkGuard og env
    t2 <- typeOf e env
    if hasNone t2 then
        do failure $ AtomTypeCannotIncludeNone e 
    else do
        let ot = PCs.SymbMap.lookup (sm_ env) id
        if isNil ot then 
            do return $ upd_sm env (put (sm_ env) id (Dottable t2 (PTy TEvent)))
        else do 
            checkIsOfType e env (Dottable t2 (PTy TEvent))
            return env
checkAtom e _ _ = failure $ InvalidAtomExpression e

checkBOp::Id->String->Env->TyErr Env
checkBOp id e env = do
   t<-lookupId env e 
   return . upd_sm env $ put (sm_ env) id t

instance TypeCheck_PCT ROp where
    typecheck (OpRExtChoice id e) env = checkBOp id e env
    typecheck (OpRIntChoice id e) env = checkBOp id e env

pcallComplies::Type->[PCE]->Env->TyErr ()
pcallComplies t@(PTy TProc) es _ = 
    if null es then return () else failure $ CouldNotMatchExpectedType (show t) ""
pcallComplies (Fun t t') [] _ = failure $ CouldNotMatchExpectedType (show t) ""
pcallComplies (Fun t t') (e:es) env = do
    t0<-typeOf e env 
    if (isNone t) || t0 <= t then 
        do pcallComplies t' es env 
    else do failure $ CouldNotMatchExpectedType (show t) (show t0)
pcallComplies t _ _ = failure $ CouldNotMatchExpectedType (show t) ""

--instance TypeCheck_PCT Ref where
--    typecheck r@(Ref id og ps rs) env = do
--        let ot = PCs.SymbMap.lookup (sm_ env) id
--        if isNil ot then do 
--            if is_unresolved env id then 
--                failure (TyUnknown id)
--           else 
--                return $ add_ref env (id, r)
--        else do
--            checkGuard og env
--            let t = the ot
--            pcallComplies t ps env
--            foldl (\r (_, y)->r>>checkIsOfType (IdExp y) env (PTy TEvent)) (return ()) rs
--            return env

instance TypeCheck_PCT PT  where
    typecheck :: PT  -> Env -> TyErr Env
    typecheck (Atom e og) env = checkAtom e og env
    typecheck (OpB top pct1 pct2) env = do 
        --failure $ Test (show top ++ ":" ++ show env)
        typecheck top env >>= typecheck pct1 >>= typecheck pct2
        --typecheck pct1 env'
        --typecheck pct2 env'
        --return env'
    typecheck (Kappa ct) env = typecheck ct env
    typecheck (OpKappa id bop pct) env = 
        (typecheck bop env >>= \env'-> newId id env' (PTy TProc)) >>= typecheck pct
    typecheck (Rho id og bs rs) env = do
        checkGuard og env
        let ot = PCs.SymbMap.lookup (sm_ env) id
        when (isSomething ot) $ do 
            pcallComplies (the ot) bs env
            foldl (\r (_, y)->r>>checkIsOfType (IdExp y) env (PTy TEvent)) (return ()) rs
        if constrains ot then do  
            t <- foldM (\t e->do
                t'<-typeOf e env
                return (Fun t' t)) (PTy TProc) bs
            return $ add_Kcnt env id t
        else do 
            return env
        where constrains ot = isNil ot || hasNone(the ot)
    typecheck StopT env = return env
    typecheck SkipT env = return env
    typecheck NilT env = return env

instance TypeCheck_PCT [PT] where
    typecheck pts env = 
        foldM (\env' pt->typecheck pt env') env pts

typecheck_pctd::PCTD->TyErr Env
typecheck_pctd (PCTD _ dts pts) = do
    typecheck dts empty_env >>= typecheck pts
    --foldM (\env' (_, r)->typecheck r env') env (urs_ env)

