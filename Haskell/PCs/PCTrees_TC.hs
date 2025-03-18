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
import Control.Monad.Except
import Control.Monad.State

type Env = SymMap Id Type 

--data Env = Env {
--    sm_::SymMap Id Type, 
--    cnts_::Rel Id Type}
--    deriving (Show)

--type Env = 

nilEnv::Env
nilEnv = emptySM 

--upd_sm::Env->SymMap Id Type->Env
--upd_sm env sm = Env {sm_ = sm, cnts_ = cnts_ env} 

--add_Kcnt::Env->Id->Type->Env
--add_Kcnt env id t = Env {sm_ = sm_ env, cnts_ = singles (id, t) `union` (cnts_ env)} 

--get_Kcnts::Env->Id->Set Type
--get_Kcnts env id = img (cnts_ env) [id]

--rm_ref::Env->Id->(Maybe Ref, Env)
--rm_ref env id = (applM  (urs_ env) id, Env {sm_ = sm_ env, urs_ = dsub (urs_ env) (singles id)})

--is_unresolved::Env->Id->Bool
--is_unresolved env id = id `elem` dom_of (urs_ env)

--data TyErr a = Ok a | Fail TyError
--    deriving (Show)

type TyErr a = ExceptT TyError (State Int) a


--instance The TyErr where
--   the :: TyErr a -> a
--   the (Right x) = x

--instance Functor TyErr where
--    fmap f (Ok t) = Ok $ f t
--    fmap _ (Fail te) = Fail te

--instance Applicative TyErr where
--    pure = Ok
--    Fail te <*> _ = Fail te
--    Ok f <*> te = fmap f te

--instance Monad TyErr where
--    return = pure
--    Fail err >>= _ = Fail err
--    Ok o >>= f = f o

--isErr::TyErr a->Bool
--isErr (Fail _) = True
--isErr _ = False

failure::TyError->TyErr a 
failure = throwError

mgu::Type -> Type ->TyErr Subst
mgu (TFun t1 t2) (TFun t1' t2') = mgu0 t1 t2 t1' t2'
mgu (TDot t1 t2) (TDot t1' t2') = mgu0 t1 t2 t1' t2'
mgu (TDot t1 t2) (TDot t1' t2') = mgu0 t1 t2 t1' t2'
mgu (TId id) t = varSubst id t
mgu t (TId id) = varSubst id t
--mgu (PTy t1) (PTy t2) = if t1 == t2 then return nil else failure $ TypesDoNotUnify (show t1) (show t2)
mgu (TBool) (TBool) = return nil
mgu (TInt) (TInt) = return nil
mgu (TEvent) (TEvent) = return nil
mgu (TProc) (TProc) = return nil
mgu t1 t2 = failure $ TypesDoNotUnify (show t1) (show t2)

mgu0::Type->Type->Type->Type->TyErr Subst
mgu0 t1 t2 t1' t2' = do
    s1 <- mgu t1 t1'
    s2 <- mgu (apply s1 t2) (apply s1 t2') 
    return $ s2 `scomp` s1  

varSubst::Id->Type->TyErr Subst
varSubst id t 
    | t == TId id = return nil
    | id `elem` freeVars t = failure $ UnificationOccursError id (show t)
    | otherwise = return $ set1 (id, t)

class TypeOf_PCT a where
    tyCheck::a->Env->Type->TyErr Subst

--type EnvWithErr = Either TyError Env

instance TypeOf_PCT PCTTypeD where
    tyCheck Int _ t    = inferTypeTD t TInt
    tyCheck Bool _ t   = inferTypeTD t TBool
    tyCheck (DT id) _ t = inferTypeTD t TData

inferTypeTD::Type->Type->TyErr Subst
inferTypeTD t t1 = mgu t t1
--    s <- mgu t t1
--    return $ apply s t

lookupId::Env->Id->TyErr Type
lookupId env id = do
    let ot = PCs.SymbMap.lookup env id
    case ot of
        Nothing -> failure $ TyUnknown id
        Just t -> return t

newTId::TyErr Type
newTId = do
    k<-get
    Control.Monad.State.put $ k +1
    return (TId $ "a" ++ show k)

instance TypeOf_PCT PCEAtom where
    tyCheck (IdExp id) env t = do
        t'<-lookupId env id
        return $ mgu t t'
    tyCheck (NumExp _) _ t = mgu t TInt
    tyCheck (BLit l) _ t = mgu t TBool
    tyCheck (ParExp  e) env t = tyCheck e env t 
    tyCheck (DotExp id e) env t = do
        beta1 <-newTId
        beta2 <-newTId
        s1<-tyCheck (IdExp id) env beta1
        s2<-tyCheck e env beta2
        s<-mgu t ((apply s1 beta1) `Dot` (apply s2 beta2))
        return $ scomp s (scomp s1 s2)
    

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

checkRelOpExp::PCERelOp->PCEAtom->PCE->Env->Type->TyErr Subst
checkRelOpExp op ea e env t = do
    beta1 <-newTId
    beta2 <-newTId
    s1<-tyCheck ea env beta1
    s2<-tyCheck e env beta2
    let t1 = apply s1 beta1
    let t2 = apply s2 beta2
    s3<-mgu t TBool
    unless (okTypes t1 t2 op) $ failure IncompatibleTypesInExp op (show t1) (show t2)
    return $ s3 `scomp` (s2 `scomp` s1)    
    where 
        okTypes TInt TInt _ = True
        okTypes TBool TBool op = op `elem` [OEQ, ONEQ] 
        okTypes (TId id1) (TId id2) op = id1 == id2 && op `elem` [OEQ, ONEQ] 
        okTypes (TDt id1) (TDt id2) op = id1 == id2 && op `elem` [OEQ, ONEQ] 
        okTypes _ _ _ = False

checkBOpExp::PCEBinOp->PCEAtom->PCE->Env->Type->TyErr Subst 
checkBOpExp op ea e env t = do
    beta1 <-newTId
    beta2 <-newTId
    s1 <- tyCheck ea env beta1 
    s2 <- tyCheck e env beta2
    let t1 = apply s1 beta1
    let t2 = apply s2 beta2
    let et = if op `elem` [And, Or] then TBool else TInt
    s3<-mgu t et
    unless (okTypes t1 t2 et) $ failure IncompatibleTypesInExp op (show t1) (show t2)
    return $ s3 `scomp` (s2 `scomp` s1) 
    where 
        okTypes TInt TInt TInt = True
        okTypes TBool TBool TBool = True
        okTypes _ _ _ = False
    --failure $ Test (show t2)
    --if t1 <= t2 || t2 <= t1 then
    --    do return et
    --    else failure (IncompatibleTypesInArithmeticExp e (show op))

checkUOpExp::PCEUnOp->PCE->Env->Type->TyErr Type
checkUOpExp uop e env t = do
    beta <-newTId
    s1<-tyCheck e env beta
    let t' = apply s1 beta
    let et = if op == UMinus then TInt else TBool
    s2<-mgu t et
    unless (t' == et) $ failure IncompatibleTypesInUExp (show uop) (show t')
    return $ s2 `scomp` s1
--checkUOpExp UNot e env t = do
--    beta <-newTId
--    s1<-tyCheck e env beta
--    let t' = apply s1 beta
--    s2<-mgu t TBool
--    unless (t' == TBool) $ failure IncompatibleTypesInUExp (show UNot) (show t')
--    return $ s2 `scomp` s1
    --if t <= PTy TBool then
    --    do return $ PTy TBool
    --else 
    --    do failure $ NotBooleanExp e

instance TypeOf_PCT PCE where
    tyCheck (ExpAtom ea) = tyCheck ea 
    tyCheck (RelOpExp op ea e) = checkRelOpExp op ea e
    tyCheck (BinExp op ea e) = checkBOExp op ea e
    tyCheck (UnExp op e) = checkUOpExp op e

class TypeCheck_PCT a where
    typeCheck::a->Env->TyErr (Env, Subst)

newId::Id->Env->Type->TyErr Env
newId id env ty 
   | keyOf id env = failure $ IdExists id
   | otherwise = return $ PCs.SymbMap.put env id ty

instance TypeCheck_PCT DTDef where
    typecheck (DTDef id ids) env = do
        env' <- newId id env TData 
        envr<-foldM (\env'' id'->newId id' env'' (TId id)) env' ids
        return (envr, nil)
        -- >>= do_ids
        --where do_ids env' = foldl (\tcr' id'->tcr'>>= \env''->newId id' env'' (TId id)) (return env') ids

instance TypeCheck_PCT [DTDef] where
    typecheck ds env = foldM (\(env', s) d->do
                                  (env'', s')<-typecheck d env'
                                  return (env'', s `override` s')) 
                            (env, nil) ds

--checkIsOfType::PCExpAtom->Env->Type->TyErr ()
checkIsOfType :: (TypeCheck_PCT a, Show a) => a -> Env -> Type -> TyErr ()
checkIsOfType e env t = do
    --t1<-typeOf e env 
    beta <-newTId
    t'<-typeCheck e env beta
    
    failure $ ExpNotOfExpectedType (show e) (show t1) (show t)
    --if t1 <= t then do
    --    return ()
    --else do
        

checkIdsUnique::Id->[Id]->TyErr ()
checkIdsUnique _ [] = return ()
checkIdsUnique idk (x:xs) = 
    if x `elem` xs then failure (ParamIdNotUnique idk x) else checkIdsUnique idk xs

checkParams::Id->[Param]->Env->TyErr Env
checkParams idk ps env = do 
    checkIdsUnique idk (map gParamId ps)
    return $ foldl (\env' p->PCs.SymbMap.put env' (gParamId p) (gty p env')) env ps
    where
        gty p env = if gParamTyD p == nil then PTy TNone else thet $ typeOf (the . gParamTyD $ p) env
        thet (Right t) = t

--strongest::Id->Type->Type->TyErr Type
--strongest _ t@(PTy TProc) (PTy TProc) = return t
--strongest id (Fun t t') (Fun y y') = do
--    let ost =  pick_strogest t y
--   if isNil ost then
--        do failure $ IncompatibleTypesInCompoundReferences id (show t) (show t')
--    else 
--        do return $ Fun y (the ost)
--    where pick_strogest t t' 
--             | t <= y = Just y 
--             | y <= t = Just t
--             | otherwise = Nothing


--strongest_type::Id->Set Type->TyErr (Maybe Type)
--strongest_type id EmptyS = return Nothing
--strongest_type id (Sets.Set t ts) = foldM (strongest id) t ts >>= return . Just

--updParamTys::Type->[Param]->Env->TyErr Env
--updParamTys (PTy TProc) [] env = return env
--updParamTys (Fun t t') (p:ps) env = do
--    t''<-lookupId env (gParamId p)
--    (if t''<= t then 
--        return $ put env (gParamId p) t
--    else 
--        return env) >>= updParamTys t' ps

instance TypeCheck_PCT PDT where
    typecheck (PDT id ps cts pct) env = do
        -- checks well-formedness of parameters
        env1<-checkParams id ps env
        -- calculates type of compound
        t <- foldM (\t p->do
            t'<-lookupId env1 (gParamId p)
            return (Fun t' t)) (PTy TProc) ps
        -- Checks if there are constraints associated with the type
        --ost <- strongest_type id $ get_Kcnts env1 id
        --failure $ Test (show ost)
        --let t' = if isSomething ost then if t<= the ost then the ost else t else t 
        --env2<-if isSomething ost then 
        --         do updParamTys (the ost) ps env1
        --      else do return env1 
        (newId id env1 t >>= typecheck cts)>>=typecheck pct
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
    let ot = PCs.SymbMap.lookup env id
    if isNil ot then 
        do return $ put env id (PTy TEvent)
    else do
        checkIsOfType e env (PTy TEvent)
        return env
checkAtom (DotExp id e) og env = do 
    checkGuard og env
    t2 <- typeOf e env
    if hasNone t2 then
        do failure $ AtomTypeCannotIncludeNone e 
    else do
        let ot = PCs.SymbMap.lookup env id
        if isNil ot then 
            do return $ put env id (Dottable t2 (PTy TEvent))
        else do 
            checkIsOfType e env (Dottable t2 (PTy TEvent))
            return env
checkAtom e _ _ = failure $ InvalidAtomExpression e

checkBOp::Id->String->Env->TyErr Env
checkBOp id e env = do
   t<-lookupId env e 
   return $ put env id t

instance TypeCheck_PCT ROp where
    typecheck (OpRExtChoice id e) env = checkBOp id e env
    typecheck (OpRIntChoice id e) env = checkBOp id e env

pcallComplies::Type->[PCE]->Env->TyErr ()
pcallComplies t@(TProc) es _ = 
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
        let ot = PCs.SymbMap.lookup env id
        when (isSomething ot) $ do 
            pcallComplies (the ot) bs env
            foldl (\r (_, y)->r>>checkIsOfType (IdExp y) env (PTy TEvent)) (return ()) rs
        return env
        --if constrains ot then do  
        --    t <- foldM (\t e->do
        --        t'<-typeOf e env
        --        return (Fun t' t)) (PTy TProc) bs
        --    return $ add_Kcnt env id t
        --else do 
        --    return env
        --where constrains ot = isNil ot || hasNone(the ot)
    typecheck StopT env = return env
    typecheck SkipT env = return env
    typecheck NilT env = return env

instance TypeCheck_PCT [PT] where
    typecheck pts env = 
        foldM (\env' pt->typecheck pt env') env pts

typecheck_pctd::PCTD->TyErr Env
typecheck_pctd (PCTD _ dts pts) = do
    typecheck dts nilEnv >>= typecheck pts
    --foldM (\env' (_, r)->typecheck r env') env (urs_ env)

