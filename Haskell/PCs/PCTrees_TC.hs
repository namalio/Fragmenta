--------------------------------
-- Project: PCs
-- Module: 'PCTress_TC'
-- Description: Type-checking of PCT representations of PCs
-- Author: Nuno Amálio
--------------------------------

module PCs.PCTrees_TC(typecheck_pctd, Env)
where

import PCs.SymbMap as SM
import PCs.PCsCommon(Id)
import PCs.PCTrees_Types
import PCs.PCTrees_TypeErrors
import PCs.PCTrees_AST
import PCs.PCTrees_Exp
import Control.Monad.Except
import Control.Monad.State
import TheNil
import Sets
import Relations
import Control.Monad ( unless, foldM, when)

type TyErr a = ExceptT TyError (State Int) a

failure::TyError->TyErr a 
failure = throwError

-- Unification
mgu::Type -> Type->TyErr Subst
mgu (TFun t1 t2) (TFun t1' t2') = mgu0 t1 t2 t1' t2'
mgu (TDot t1 t2) (TDot t1' t2') = mgu0 t1 t2 t1' t2'
mgu (TId id) t = varSubst id t
mgu t (TId id) = varSubst id t
--mgu (PTy t1) (PTy t2) = if t1 == t2 then return nil else failure $ TypesDoNotUnify (show t1) (show t2)
mgu (TBool) (TBool) = return nil
mgu (TInt) (TInt) = return nil
mgu (TEvent) (TEvent) = return nil
mgu (TProc) (TProc) = return nil
mgu t1 t2 = failure $ TypesDoNotUnify (show t1) (show t2)
--mgu t1 t2 (Just err) = failure err

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

class TyCheck_PCT a where
    tyCheck::a->Env->Type->TyErr Subst

class TypeOf_PCT a where
    typeOf::a->Env->TyErr Type

-- Type designators
instance TyCheck_PCT PCTTypeD where
    tyCheck Int _ t    = inferTypeTD t TInt
    tyCheck Bool _ t   = inferTypeTD t TBool
    tyCheck (DT id) _ t = inferTypeTD t (TId id)

inferTypeTD::Type->Type->TyErr Subst
inferTypeTD t t1 = mgu t t1

-- Looks for an indentifier in the environment
lookupId::Env->Id->TyErr Type
lookupId env id = do
    let ot = SM.lookup env id
    case ot of
        Nothing -> failure $ TyUnknown id  
        Just t -> return t

instance TypeOf_PCT Id where
    typeOf id env = lookupId env id

instance TyCheck_PCT Id where
    tyCheck id env t = do
        t'<-typeOf id env
        mgu t t'

-- Cretes a new type identifier (The Beta in the rules)
newTId::TyErr Type
newTId = do
    k<-get
    Control.Monad.State.put $ k +1
    return (TId $ "a" ++ show k)

instance TyCheck_PCT PCEAtom where
    tyCheck (IdExp id) env t = tyCheck id env t
    tyCheck (NumExp _) _ t = mgu t TInt
    tyCheck (BLit l) _ t = mgu t TBool
    tyCheck (ParExp  e) env t = tyCheck e env t 
    tyCheck (DotExp id e) env t = do
        beta1 <- newTId
        beta2 <- newTId
        s1 <- tyCheck id env beta1
        s2 <- tyCheck e env beta2
        s<-mgu t ((apply s1 beta1) `TDot` (apply s2 beta2))
        return $ s `scomp` (s1 `scomp` s2)


checkRelOpExp::PCERelOp->PCEAtom->PCE->Env->Type->TyErr Subst
checkRelOpExp op ea e env t = do
    s1<-tyCheck ea env TInt
    s2<-tyCheck e env TInt
    s3<-mgu t TBool
    --unless (okTypes t1 t2 op) $ failure $ IncompatibleTypesInExp (show op) (show t1) (show t2)
    return $ s3 `scomp` (s2 `scomp` s1)    
    --where 
    --    okTypes TInt TInt _ = True
    --    okTypes TBool TBool op = op `elem` [OEQ, ONEQ] 
    --    okTypes (TId id1) (TId id2) op = id1 == id2 && op `elem` [OEQ, ONEQ] 
    --    okTypes (TDt id1) (TDt id2) op = id1 == id2 && op `elem` [OEQ, ONEQ] 
    --    okTypes _ _ _ = False

checkBOpExp::PCEBinOp->PCEAtom->PCE->Env->Type->TyErr Subst 
checkBOpExp op ea e env t = do
    let et = if op `elem` [And, Or] then TBool else TInt
    s1 <- tyCheck ea env et 
    s2 <- tyCheck e env et
    s3<-mgu (apply (s2 `scomp` s1) t) et
    return $ s3 `scomp` (s2 `scomp` s1) 
    --unless (okTypes t1 t2 et) $ failure $ IncompatibleTypesInExp (show op) (show t1) (show t2)
   -- where 
   --     okTypes TInt TInt TInt = True
   --     okTypes TBool TBool TBool = True
   --     okTypes _ _ _ = False

checkUOpExp::PCEUnOp->PCE->Env->Type->TyErr Subst 
checkUOpExp uop e env t = do
    let et = if uop == UMinus then TInt else TBool
    s1<-tyCheck e env et  
    s2<-mgu t et
    --unless (t == et) $ failure $ IncompatibleTypesInUExp (show uop) (show t')
    return $ s2 `scomp` s1

instance TyCheck_PCT PCE where
    tyCheck (ExpAtom ea) = tyCheck ea 
    tyCheck (RelOpExp op ea e) = checkRelOpExp op ea e
    tyCheck (BinExp op ea e) = checkBOpExp op ea e
    tyCheck (UnExp op e) = checkUOpExp op e

class TypeCheck_PCT a where
    typeCheck::a->Env->TyErr Env

--class TypeCheck_PCT2 a where
--    typeCheck2::a->Env->TyErr (Maybe Env)

newId::Id->Env->Type->TyErr Env
newId id env ty 
   | keyOf id env = failure $ IdExists id
   | otherwise    = return $ SM.put env id ty

instance TypeCheck_PCT DTDef where
    typeCheck (DTDef id ids) env = do
        env' <- newId id env TData 
        foldM (\env'' id'->newId id' env'' (TId id)) env' ids
    
instance TypeCheck_PCT [DTDef] where
    typeCheck ds env = foldM (\env' d->typeCheck d env') env ds

instance TypeOf_PCT Param where
    typeOf (Param id otd) env = do
        beta1 <- newTId
        if (isNil otd) 
        then do
            return beta1
        else do
            s<-tyCheck (the otd) env beta1
            return $ apply s beta1

--instance TypeOf_PCT [Param] where
--    typeOf ps env = foldM (\t1 p->do
--                       t2<-typeOf p env 
--                       return $ TFun t2 t1) TProc ps 

instance TypeCheck_PCT [Param] where
    typeCheck ps env = foldM (\env p->do
                           t<-typeOf p env 
                           return $ SM.put env (gParamId p) t) env ps 

typeForK::[Param]->Env->TyErr Type
typeForK ps env = foldM (\t1 p->do
                    t2<-typeOf p env 
                    return $ TFun t2 t1) TProc ps

checkIdsUnique::Id->[Id]->TyErr ()
checkIdsUnique _ [] = return ()
checkIdsUnique idk (x:xs) = 
    if x `elem` xs then failure (ParamIdNotUnique idk x) else checkIdsUnique idk xs

--tyCheckParam::Id->Param->Env->TyErr Env
--tyCheckParam idk p env = do 
--    let id = gParamId p
--    beta1 <- newTId
--    if gParamTyD p == nil
--    then do
--        return $ SM.put env id beta1
--    else do
--        s<-tyCheck (the . gParamTyD $ p) env beta1
--        return $ SM.put env id (apply s beta1)

--checkParams::Id->[Param]->Env->TyErr Env
--checkParams idk ps env = do 
--    checkIdsUnique idk (map gParamId ps)

--tyCheckParams::Id->[Param]->Env->TyErr (Env, Type)
--tyCheckParams _ [] env = return (env, TProc)
--tyCheckParams idk (p:ps) env = do 
--    env'<-tyCheckParam idk p env
--    t <- typeOf (gParamId p) env'
--    (env'', t')<-tyCheckParams idk ps env'
--    return (env'', TFun t t')

-- Processes header of a PD
tyCheckKH::PD->Env->TyErr Env
tyCheckKH(PD id ps _ _) env = do
    if SM.keyOf id env then do
        failure $ ProcessAlreadyDefined id
    else
        typeForK ps env >>= newId id env
--    t<-typeOf ps env
--    return $ newId id env t

-- Processes headers of PDs
tyCheckKHs::[PD]->Env->TyErr Env
tyCheckKHs pds env = foldM (\env' pd->tyCheckKH pd env') env pds

instance TypeCheck_PCT PD where -- Process definitions (PDs)
    typeCheck pd@(PD id ps cts pt) env = do
        -- checks that parameter ids are unique
        let ids = map gParamId ps
        checkIdsUnique id ids
        if SM.keyOf id env then do
            t<-typeForK ps env
            s<-tyCheck id env t
            env0<-typeCheck ps (SM.put env id (apply s t))>>=typeCheckPTHs cts
            env'<-typeCheckPTH pt env0>>=typeCheck cts>>=typeCheck pt 
            return $ removeFrEnv (applyEnv s env') (SM.keys env' `sminus` (evIds env') `sminus` SM.keys env)
        else do
            env0<-typeCheck ps env
            t<-typeForK ps env0
            env1<-newId id env0 t>>=typeCheck ps>>=typeCheckPTHs cts>>=typeCheckPTH pt
            env'<-typeCheck cts env1>>=typeCheck pt 
            return $ removeFrEnv env' (SM.keys env' `sminus`  (evIds env') `sminus` SM.keys env `sminus` (singles id))
        where
            evIds env = 
                let r = rel env in foldl (\ids (id, t)->if isEventTy t then id:ids else ids) nil (rel env)
       
 
instance TypeCheck_PCT [PD] where
    typeCheck pds env = 
        foldM (\env' pd->typeCheck pd env') env pds 

instance TypeCheck_PCT TOp where
    typeCheck OpExtChoice env = return env
    typeCheck OpIntChoice env = return env
    typeCheck (OpSeq _) env = return env
    typeCheck (OpParallel es) env = do
        s<-tyCheck es env TEvent
        --s2 <- foldM (\s e->do 
        --          tyCheck e env TEvent >>= \s1->return (s1 `scomp` s)) nil es 
        return (applyEnv s env)
    typeCheck OpInterleave env = return env
    typeCheck (OpThrow es) env = do
        s2 <- foldM (\s e->do 
                 tyCheck e env TEvent >>= \s1->return (s1 `scomp` s)) nil es 
        return (applyEnv s2 env)
    typeCheck (OpIf e) env = do
        s<-tyCheck e env TBool 
        return (applyEnv s env)

instance TyCheck_PCT (Maybe PCE) where
    tyCheck Nothing _ _ = return nil
    tyCheck (Just e) env t = tyCheck e env t

instance TyCheck_PCT [PCE] where
     tyCheck [] _ _ = return nil
     tyCheck (e:es) env t = do
        s1<-tyCheck e env t 
        s2<-tyCheck es env t
        return $ s2 `scomp` s1

--checkGuard::Maybe PCE->Env->TyErr Subst
--checkGuard Nothing _ = return nil
--checkGuard (Just eg) env = tyCheck eg env TBool  
--    checkIsOfType eg env 

checkAtom::PCEAtom->Maybe PCE->Env->TyErr Env
checkAtom (IdExp id) og env = do
    s<-tyCheck og env TBool
    let ot = SM.lookup env id
    if isSomething ot then do
        unless (the ot == TEvent) $ (failure $ CouldNotMatchExpectedType (show TEvent) (show . the $ ot))
        return $ applyEnv s env
    else do
        env'<-newId id env TEvent
        return $ applyEnv s env'
checkAtom (DotExp id e) og env = do 
    s<-tyCheck og env TBool
    let ot = SM.lookup env id
    if isSomething ot then do
        let t' = TDot (the ot) TEvent
        s1<-tyCheck e env t'
        return $ applyEnv (s1 `scomp` s) env
    else do
        beta <-newTId
        s1<-tyCheck e env beta
        let t' = TDot (apply s1 beta) TEvent
        env' <- newId id env t'
        return $ applyEnv (s1 `scomp` s) env'
checkAtom e _ _ = failure $ InvalidAtomExpression e

checkBOp::Id->PCTTypeD->Env->TyErr Env
checkBOp id td env = do
   t<-typeOf (Param id (Just td)) env
   return $ SM.put env id t

instance TypeCheck_PCT ROp where
    typeCheck (OpRExtChoice id td) env = checkBOp id td env
    typeCheck (OpRIntChoice id td) env = checkBOp id td env

tyCheckParamBs::[PCE]->Env->Type->TyErr Subst
tyCheckParamBs [] env t = do
    if t == TProc then do
        return nil
    else do
        failure $ CouldNotMatchExpectedType (show TProc) (show t)
tyCheckParamBs (b:bs) env (TFun t1 t2) = do
    s1<-tyCheck b env t1
    s2<-tyCheckParamBs bs env (apply s1 t2)
    return  $ s2 `scomp` s1
tyCheckParamBs _ _ t = failure $ CouldNotMatchExpectedType "TFun" (show t)

tyOfParamBsN::[PCE]->Env->TyErr Type
tyOfParamBsN [] env = return TProc
tyOfParamBsN (b:bs) env = do
    beta <-newTId
    s1<-tyCheck b env beta
    let t1 = apply s1 beta
    t2<-tyOfParamBsN bs env
    return $ TFun t1 t2

instance TypeCheck_PCT PT  where
    typeCheck :: PT->Env -> TyErr Env
    typeCheck (Atom e og) env = checkAtom e og env
    typeCheck (OpB top pt1 pt2) env = 
        typeCheck top env >>= typeCheck pt1 >>= typeCheck pt2
    typeCheck (Kappa pd) env = typeCheck pd env
    typeCheck (OpKappa id bop pt) env = 
        (typeCheck bop env >>= \env'-> newId id env' TProc) >>= typeCheck pt
    typeCheck r@(Rho id og bs rs) env = do
        unless (dom_of rs `cross` (singles TEvent) `subseteq` SM.rel env) $ failure (NoMatchingEvents $ toList . dom_of $ rs)
        unless (img (SM.rel env) (ran_of rs) `subseteq` singles TEvent) $ failure (NoMatchingEvents $ toList . ran_of $ rs)
        if SM.keyOf id env then do
            t<-typeOf id env
            s1<-tyCheckParamBs bs env t
            s2<-tyCheck og env TBool
            return $ SM.putAll (applyEnv (s2 `scomp` s1) env) (ran_of rs `cross` singles TEvent)
        else do
            failure $ NoProcessNamed id
            -- t<-tyOfParamBsN bs env
            -- env'<-newId id env t
            -- s1<-tyCheck og env' TBool
            -- return $ SM.putAll (applyEnv s1 env') (ran_of rs `cross` singles TEvent)
    typeCheck StopT env = return env
    typeCheck SkipT env = return env
    typeCheck NilT env = return env

typeCheckPTH::PT->Env->TyErr Env
typeCheckPTH (Kappa pd) env = tyCheckKH pd env
typeCheckPTH (OpB top pt1 pt2) env = typeCheckPTH pt1 env>>=typeCheckPTH pt2
typeCheckPTH _ env = return env

typeCheckPTHs::[PT]->Env->TyErr Env
typeCheckPTHs pts env = foldM (\env pt->typeCheckPTH pt env) env pts 

instance TypeCheck_PCT [PT] where
    typeCheck pts env = 
        foldM (\env' pt->typeCheck pt env') env pts

typecheck_pctd::PCTD->TyErr Env
typecheck_pctd (PCTD _ dts pds) = do
   typeCheck dts nilEnv >>= tyCheckKHs pds >>= typeCheck pds

