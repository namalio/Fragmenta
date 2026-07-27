--------------------------------
-- Project: PCs
-- Module: 'PCTress_TC'
-- Description: Type-checking of PCT representations of PCs
-- Author: Nuno Amálio
--------------------------------

module PCs.PCTreesTC
    (typecheck_pctd
    , Env
    )
where

--import PCs.SymbMap as SM
import PCs.Common
    (Id
    , PCTypeD(..)
    , PCTypeE(..)
    , Param(..)
    , gParamId)
import PCs.PCTrees_Types
import PCs.PCTrees_TypeErrors
import PCs.PCTreesAST
import PCs.TxtExpAST
import Control.Monad.Except
import Control.Monad.State
import TheNil
import Sets
import Relations
import Control.Monad 
    ( unless
    , foldM
    , when
    )
import SimpleFuns 
   (dupsL)

type TyErr a = ExceptT TyError (State Int) a

failure::TyError->TyErr a 
failure = throwError

-- Unification
mgu::Type -> Type->Env->TyErr Subst
mgu (TFun t1 t2) (TFun t1' t2') env = mgu0 t1 t2 t1' t2' env
mgu (TDot t1 t2) (TDot t1' t2') env = mgu0 t1 t2 t1' t2' env
mgu t1@(TId id1) t2@(TId id2) env 
   | id1 `inEnv` env = varSubst id2 t1
   | otherwise = varSubst id1 t2
mgu (TId id) t _ = varSubst id t
mgu t (TId id) _ = varSubst id t
--mgu (PTy t1) (PTy t2) = if t1 == t2 then return nil else failure $ TypesDoNotUnify (show t1) (show t2)
mgu TBool TBool _ = return nil
mgu TInt TInt _ = return nil
mgu TEvent TEvent _ = return nil
mgu TProc TProc _ = return nil
mgu (TSet t1) (TSet t2) env = mgu t1 t2 env
mgu t1 t2 _ = failure $ TypesDoNotUnify (show t1) (show t2)
--mgu t1 t2 (Just err) = failure err

mgu0::Type->Type->Type->Type->Env->TyErr Subst
mgu0 t1 t2 t1' t2' env = do
    s1 <- mgu t1 t1' env
    s2 <- mgu (apply s1 t2) (apply s1 t2') env
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


inferTypeTD::Type->Type->Env->TyErr Subst
inferTypeTD t t1 env = mgu t t1 env

-- Type designators
instance TyCheck_PCT PCTypeD where
    tyCheck::PCTypeD->Env->Type->TyErr Subst
    tyCheck Int env t    = inferTypeTD t TInt env
    tyCheck Bool env t   = inferTypeTD t TBool env
    tyCheck Event env t  = inferTypeTD t TEvent env
    tyCheck (Dt id) env t = inferTypeTD t (TId id) env
    tyCheck (SetT td) env t = do
        beta <- newTId
        s0 <- tyCheck td env beta
        s1<-inferTypeTD (TSet $ apply s0 beta) (apply s0 t) env
        return $ s1 `scomp` s0

-- Type expression
instance TyCheck_PCT PCTypeE where
    tyCheck::PCTypeE->Env->Type->TyErr Subst
    tyCheck (TyD td) env t   = do
        s<-tyCheck td env t
        beta <- newTId
        s1<-mgu (TSet beta) (apply s t) env
        return (s1 `scomp` s) 
    tyCheck (TIdE id) env t  = do 
        t'<-typeOf id env
        if t' == TData then
            mgu (TId id) t env
        else do
            beta <- newTId
            s1<-mgu (TSet beta) t' env
            s2<-mgu (apply s1 beta) t env
            return (s2 `scomp` s1)
    tyCheck (SetE ids) env t  = do 
        beta <- newTId
        s0<-tyCheck ids env beta 
        s1<-mgu (TSet $ apply s0 beta) (apply s0 t) env
        return $ s1 `scomp` s0

find::Env->Id->Maybe Type
find = applM 

-- Looks for an indentifier in the environment
lookupId::Env->Id->TyErr Type
lookupId env id = do
    let ot = find env id
    case ot of
        Nothing -> failure $ TyUnknown id  
        Just t -> return t

instance TypeOf_PCT Id where
    typeOf::Id->Env->TyErr Type
    typeOf id env = lookupId env id

instance TyCheck_PCT Id where
    tyCheck::Id->Env->Type->TyErr Subst
    tyCheck id env t = do
        t'<-typeOf id env
        mgu t t' env

--tyCheckNId::Id->Env->Type->TyErr Subst
--tyCheckNId id env t = do
--    let ot = SM.lookup env id
--    if isNil ot then do
--        beta <- newTId
--        mgu t beta env
--    else 
--        mgu t (the ot) env

-- Cretes a new type identifier (The Beta in the rules)
newTId::TyErr Type
newTId = do
    k<-get
    Control.Monad.State.put $ k +1
    return (TId $ "a" ++ show k)

instance TyCheck_PCT [Id] where
    tyCheck [] _ _         = return nil
    tyCheck (id:ids) env t = do
        t'<-typeOf id env
        s0<-mgu t' t env
        --failure $ TyUnknown id -- HERE
        --when (id == "grabTV") $ failure $ IncompatibleTypesInExp (show s0) (show t) (show t') -- HERE
        s1<-tyCheck ids env (apply s0 t)
        return $ s1 `scomp` s0

checkRelExpInts::Exp->Exp->Env->Type->TyErr Subst
checkRelExpInts e1 e2 env t = do
    beta1 <- newTId
    beta2 <- newTId
    s0<-tyCheck e1 env beta1
    s1<-tyCheck e2 env beta2
    s2<-mgu (apply s0 beta1) TInt env
    s3<-mgu (apply s1 beta2) TInt env
    s4<-mgu (apply (s3 `scomp` (s2 `scomp` (s1 `scomp` s0))) t) TBool env
    return $ s4 `scomp` (s3 `scomp` (s2 `scomp` (s1 `scomp` s0)))

checkRelExpEq::Exp->Exp->Env->Type->TyErr Subst
checkRelExpEq e1 e2 env t = do
    beta1 <- newTId
    beta2 <- newTId
    s0<-tyCheck e1 env beta1
    s1<-tyCheck e2 env beta2
    --beta3 <- newTId
    s2<-mgu (apply s0 beta1) (apply (s1`scomp`s0) beta2) env
    --s3<-mgu (apply s1 beta2) (apply s2 beta3) env
    s3<-mgu (apply (s2 `scomp` (s1 `scomp` s0)) t) TBool env
    return $ s3 `scomp` (s2 `scomp` (s1 `scomp` s0))

checkRelExpIn::Exp->Exp->Env->Type->TyErr Subst
checkRelExpIn e1 e2 env t = do
    beta1 <- newTId
    beta2 <- newTId
    s0<-tyCheck e1 env beta1
    s1<-tyCheck e2 env beta2
    s2<-mgu (apply (s1 `scomp` s0) beta2) (TSet $ apply s0 beta1) env
    s3<-mgu (apply (s2 `scomp` (s1 `scomp` s0)) t) TBool env
    return $ s3 `scomp` (s2 `scomp` (s1 `scomp` s0))

checkRelExp::RelOp->Exp->Exp->Env->Type->TyErr Subst
checkRelExp op e1 e2 env t 
    | op `elem` [OGT, OLT, OLEQ, OGEQ] = checkRelExpInts e1 e2 env t
    | op `elem` [OEQ, ONEQ] = checkRelExpEq e1 e2 env t
    | op `elem` [OIN] = checkRelExpIn e1 e2 env t

checkBinExpSet::Exp->Exp->Env->Type->TyErr Subst 
checkBinExpSet e1 e2 env t = do
    beta <- newTId 
    let et = TSet beta
    s1 <- tyCheck e1 env et 
    s2 <- tyCheck e2 env (apply s1 et)
    s3<-mgu (apply (s2 `scomp` s1) t) (apply (s2 `scomp` s1) et) env
    return $ s3 `scomp` (s2 `scomp` s1) 

checkBinExpIntBool::BinOp->Exp->Exp->Env->Type->TyErr Subst 
checkBinExpIntBool op e1 e2 env t = do
    let et = if op `elem` [And, Or] then TBool else TInt
    s1 <- tyCheck e1 env et 
    s2 <- tyCheck e2 env et
    s3<-mgu (apply (s2 `scomp` s1) t) et env
    return $ s3 `scomp` (s2 `scomp` s1) 

checkBinExp::BinOp->Exp->Exp->Env->Type->TyErr Subst 
checkBinExp op e1 e2 env t 
    | op `elem` [Cup, Cap, SMinus] = checkBinExpSet e1 e2 env t
    | otherwise                    = checkBinExpIntBool op e1 e2 env t
    --unless (okTypes t1 t2 et) $ failure $ IncompatibleTypesInExp (show op) (show t1) (show t2)
   -- where 
   --     okTypes TInt TInt TInt = True
   --     okTypes TBool TBool TBool = True
   --     okTypes _ _ _ = False

checkUnExp::UnOp->Exp->Env->Type->TyErr Subst 
checkUnExp uop e env t = do
    let t' = if uop == UMinus then TInt else TBool
    s1<-tyCheck e env t'  
    s2<-mgu (apply s1 t) (apply s1 t') env
    return $ s2 `scomp` s1

cmpDot::Type->Type->TyErr Type
cmpDot (TDot (TDot t1 t1') t2) t3 = cmpDot (TDot t1 (TDot t1' t2)) t3
cmpDot (TDot t1 t2) (TDot t3 t4) = if t1 == t3 then cmpDot t2 t4 else failure $ CouldNotMatchExpectedType (show t1) (show t3)
cmpDot (TDot t1 t2) t3 = if t1 == t3 then return t2 else failure $ CouldNotMatchExpectedType (show t1) (show t3)
cmpDot t1 t2 = return $ TDot t1 t2

instance TyCheck_PCT Exp where
    tyCheck::Exp->Env->Type->TyErr Subst
    tyCheck (ExpId id) env t = tyCheck id env t
    tyCheck (ExpInt _) env t = mgu t TInt env
    tyCheck (ExpB _) env t = mgu t TBool env
    tyCheck (ExpPar e) env t = tyCheck e env t 
    tyCheck (ExpDot e1 e2) env t = do
        beta1 <- newTId
        beta2 <- newTId
        s1 <- tyCheck e1 env beta1
        s2 <- tyCheck e2 env beta2
        --let t1' = if isDotTy t1 then applyDot t1 t2 else t1
        --unless (e1 /= (ExpId "pay")) $ failure (IncompatibleTypesInExp (show env) (show $ apply s1 beta1 )  (show $ apply s2 beta2 ))
        t'<-cmpDot (apply s1 beta1) (apply s2 beta2)
        s<-mgu t t' env
        return $ s `scomp` (s2 `scomp` s1)
    tyCheck (ExpRel op e1 e2) env t = checkRelExp op e1 e2 env t
    tyCheck (ExpBin op e1 e2) env t = checkBinExp op e1 e2 env t 
    tyCheck (ExpUn op e) env t = checkUnExp op e env t
    tyCheck (ExpSet es) env t = do
        beta <- newTId
        s0 <- tyCheck es env beta
        s1<-mgu (apply s0 t) (TSet $ apply s0 beta) env
        --failure $ CouldNotMatchExpectedType (show es) (show $ s1 `scomp` s0 )
        --failure $ CouldNotMatchExpectedType (show $ s1 `scomp` s0) (show $ apply s0 beta)
        --failure (CouldNotMatchExpectedType (show $ SM.lookup env "SeizeControl") (show $ s1 `scomp` s0))
        return $ s1 `scomp` s0 

class TypeCheck_PCT a where
    typeCheck::a->Env->TyErr Env

--class TypeCheck2_PCT a where
--    typeCheck'::a->Env->[Type]->TyErr Env

checkIdExists::Id->Env->TyErr ()
checkIdExists id env 
    | id `inEnv` env = failure $ IdExists id
    | otherwise = return ()

newId::Id->Env->Type->Env
newId id env ty = env `override`  set1 (id, ty) 
 --  | id `inEnv` env = failure $ IdExists id
 --  | otherwise      = return $ (id, ty) `intoSet` env

instance TypeCheck_PCT DTDef where
    typeCheck (DTDef id vts) env = do
        checkIdExists id env
        checkIdsUnique id (fmap gIdVT vts)
        let env' = newId id env TData 
        foldM (\env'' vt->checkTy vt env'' (TId id)) env' vts

class CheckTy_PCT a where
    checkTy::a->Env->Type->TyErr Env

--tyCheck_tds::[PCTypeD]->Env->TyErr Type
--tyCheck_tds [td] env = do 
--    beta <- newTId
--    s<-tyCheck td env beta 
--    return (apply s beta)
--tyCheck_tds (td:tds) env = do
--   beta <- newTId
--   s<-tyCheck td env beta
--   t2<-tyCheck_tds tds env
--   return $ (TDot (apply s beta) t2)

class DerTy_PCT a where
    derTy::a->Env->Type->TyErr Type

instance DerTy_PCT [PCTypeD] where
    derTy [] env t = return t
    derTy (td:tds) env t = do
        beta <- newTId
        s<-tyCheck td env beta
        --beta2 <- newTId
        t'<-derTy tds env t
        --mgu (apply (s1 `scomp` s0) t) (apply (s1 `scomp` s0) (TDot beta1 beta2)) env
        return (TDot (apply s beta) t') -- (s1 `scomp` s0)

instance CheckTy_PCT VTerm where
    checkTy (VTerm id tds) env t =  do 
        t'<-derTy tds env t
        --unless (id /= "pay") $ failure (CouldNotMatchExpectedType (show env) (show t'))
        return $ newId id env t'
        
instance TypeCheck_PCT [DTDef] where
    typeCheck ds env = foldM (\env' d->typeCheck d env') env ds

instance TyCheck_PCT Param where
    tyCheck::Param->Env->Type->TyErr Subst
    tyCheck (Param id Nothing) _ _ = return nil
    tyCheck (Param id (Just td)) env t = tyCheck td env t

--instance TypeOf_PCT Param where
--    typeOf (Param id otd) env = do
--        beta<-newTId
--        if (isNil otd) 
--        then 
--           return beta
--        else do
--            s<-tyCheck (the otd) env beta
--            return (apply s beta)

typeCheckPs::[Param]->Type->Env->TyErr Env
typeCheckPs [] TProc env = return env
typeCheckPs ps TProc env = failure $ UnexpectedError ("There are no types to associate with parameters" ++ (show ps))
typeCheckPs (p:ps) (TFun t1 t2) env = do
    s<-tyCheck p env t1
    let env0 = newId (gParamId p) env (apply s t1)
    env'<- typeCheckPs ps t2 env0
    return $ applyEnv s env'

instance TypeCheck_PCT [Param] where
    typeCheck ps env = 
        foldM (\env p->do
            beta<-newTId
            s<-tyCheck p env beta
            let env' = newId (gParamId p) env (apply s beta)
            return $ applyEnv s env') env ps

typeForK::[Param]->Env->TyErr Type
typeForK ps env = foldM (\t p->do
                    beta<-newTId
                    s<-tyCheck p env beta 
                    return $ apply s (TFun beta t)) TProc ps

-- Improve here
checkIdsUnique::Id->[Id]->TyErr ()
checkIdsUnique k ids = do
    when (k `elem` ids) $ failure (InvalidParamId k)
    let ds = dupsL ids
    if null ds then
        return ()
    else 
       failure (ParamIdsNotUnique k ds) 
 

--checkIdsUnique0::Id->[Id]->TyErr ()
--checkIdsUnique0 _ [] = return ()
--checkIdsUnique0 idk (x:xs) = do
--    if x `elem` xs then failure (ParamIdNotUnique idk x) else checkIdsUnique0 idk xs

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

-- Processes header of a PT
tyCheckKH::PT->Env->TyErr Env
tyCheckKH(Kappa id ps _ _) env = 
    if id `inEnv` env then
        failure $ ProcessAlreadyDefined id
    else do
        t<-typeForK ps env 
        return $ newId id env t
tyCheckKH pt _ = failure $ ProcessDeclNotCompound (show pt)
--    t<-typeOf ps env
--    return $ newId id env t

-- Processes headers of PDs
tyCheckKHs::[PT]->Env->TyErr Env
tyCheckKHs pts env = foldM (\env' pt->tyCheckKH pt env') env pts


--tyCheckEvDecl::Id->Env->TyErr Env
--tyCheckEvDecl id env =
--    if id `inEnv` env then
--        failure $ IdExists id
--    else do 
--        beta<-newTId
--        newId id env beta

-- Processes declarations of events
--tyCheckEvDecls::[Id]->Env->TyErr Env
--tyCheckEvDecls ids env = foldM (\env' id->tyCheckEvDecl id env') env ids

--instance TypeCheck_PCT PD where -- Process definitions (PDs)
--    typeCheck pd@(Kappa id ps cpds pt) env = do
--        -- checks that parameter ids are unique
--        let ids = map gParamId ps
--        checkIdsUnique id ids
--        if SM.keyOf id env then do
--            t<-typeForK ps env
--            s<-tyCheck id env t
--            env0<-typeCheck ps (SM.put env id (apply s t))>>=tyCheckKHs cpds
--            env'<- typeCheck cpds env0>>=typeCheck pt 
--            return $ removeFrEnv (applyEnv s env') (SM.keys env' `sminus` (evIds env') `sminus` SM.keys env)
--        else do
--            env0<-typeCheck ps env
--            t<-typeForK ps env0
--            env1<-newId id env0 t>>=typeCheck ps>>=tyCheckKHs cpds
--           env'<-typeCheck cpds env1>>=typeCheck pt 
--            return $ removeFrEnv env' (SM.keys env' `sminus`  (evIds env') `sminus` SM.keys env `sminus` (singles id))
--        where
--            evIds env = 
--                let r = rel env in foldl (\ids (id, t)->if isEventTy t then id:ids else ids) nil (rel env)
       
 
--instance TypeCheck_PCT [PT] where
--    typeCheck pds env = foldM (\env' pd->typeCheck pd env') env pds 

tyCheckTOpEvs::Env->[Exp]->TyErr Env
tyCheckTOpEvs env es = do 
    s <- foldM (\s e->do 
                --beta<-newTId
                --when (gId e == "frI") $ failure (NotOfEventType (show e) (show env))
                s1<-tyCheck e env TEvent
                --let t = apply s1 beta
               -- s2<-mgu t TEvent env
                return (s1 `scomp` s)) nil es 
    return (applyEnv s env)
    where gId (ExpId id) = id
          gId (ExpDot e1 e2) = gId e1
    
instance TypeCheck_PCT TOp where
    typeCheck::TOp->Env->TyErr Env
    typeCheck OpExtChoice env = return env
    typeCheck OpIntChoice env = return env
    typeCheck OpSeq env = return env
    typeCheck (OpParallel es) env = do
        tyCheckTOpEvs env es
    typeCheck OpInterleave env = return env
    typeCheck (OpThrow es) env = do
        tyCheckTOpEvs env es
    typeCheck (OpIf e) env = do
        s<-tyCheck e env TBool 
        return (applyEnv s env)

instance TyCheck_PCT (Maybe Exp) where
    tyCheck Nothing _ _    = return nil
    tyCheck (Just e) env t = tyCheck e env t

instance TyCheck_PCT [Exp] where
    tyCheck::[Exp]->Env->Type->TyErr Subst
    tyCheck [] _ _       = return nil
    tyCheck (e:es) env t = do
        s0<-tyCheck e env t 
        s1<-tyCheck es env (apply s0 t)
        --when (e == ExpId "grabTV") $ failure $ IncompatibleTypesInExp (show e) (show t) (show $ s2 `scomp` s1)
        return $ s1 `scomp` s0

checkAtom::Exp->Maybe Exp->Env->TyErr Env
checkAtom (ExpId id) og env = do
    s<-tyCheck og env TBool
    let ot = find env id
    --failure $ CouldNotMatchExpectedType (show TEvent) (show . the $ ot)
    --unless (id /= "e") $ failure $ CouldNotMatchExpectedType id (show . the $ ot)
    if isSomething ot then do
        --unless (the ot == TEvent) $ failure $ CouldNotMatchExpectedType (show TEvent) (show . the $ ot)
        s2<-mgu (the ot) TEvent env
        return $ applyEnv (s2 `scomp` s) env
    else do
        let env' = newId id env TEvent
        return $ applyEnv s env'
checkAtom e@(ExpDot e1 e2) og env = do 
    s<-tyCheck og env TBool
    unless (isExpId e1) $ (failure $ ExpNotOfIdType e1)
    let (ExpId id) = e1 
    let ot = find env id 
    --when (id == "frI") $ (failure $ IncompatibleTypesInArithmeticExp e (show ot))
    if isSomething ot then do
        unless (isDotTy (the ot)) $ failure $ NotOfDotType (show id) (show . the $ ot)
        let (TDot t1 t2 ) = the ot
        unless (isEvTy t2) $ failure $ NotOfEventType (show id) (show . the $ ot)
        --let t0 = fstTy beta
        s1<-tyCheck e2 env t1
        return $ applyEnv (s1 `scomp` s) env
    else do
        beta <-newTId
        s1<-tyCheck e2 env beta
        let t' = TDot (apply s1 beta) TEvent
        --unless (id /= "frPay") $ failure $ IncompatibleTypesInExp (show e2) (show s1) (show t')
        let env' = newId id env t' 
        return $ applyEnv (s1 `scomp` s) env'
checkAtom e _ _ = failure $ InvalidAtomExpression e


--checkROp::Id->PCTypeExp->Env->TyErr Env 
--checkROp id (TyD td) env = do
--   t<-typeOf (Param id (Just td)) env
--   return $ SM.put env id t
--checkROp id (TIdExp tid) env = do 
--    t<-typeOf tid env
--    return $ SM.put env id t
--checkROp id (SetE ids) env = do 
--    beta<-newTId
--    s<-tyCheck id env beta
--    return $ SM.put env id (apply s beta)

instance TypeCheck_PCT ROp where
    typeCheck (ROp _ id te) env = do
        --when (te == TIdE "aes") $ failure (TyUnknown (show env))
        beta<-newTId
        s<-tyCheck te env beta
        let beta0 = apply s beta
        --(s', t)<-doRopTy beta0 env
        let env' = newId id env (trimTy beta0)
        return $ applyEnv s env'
        where
            trimTy (TSet t) = t
            trimTy t = t  
        

tyCheckArgs::[Exp]->Env->Type->TyErr Subst
tyCheckArgs [] _ t = 
    if t == TProc then
        return nil
    else 
        failure $ CouldNotMatchExpectedType (show TProc) (show t)
tyCheckArgs (b:bs) env (TFun t1 t2) = do
    --when (b == ExpSet [ExpId "mainDoor",ExpId "roomWindow"]) $ failure (CouldNotMatchExpectedType (show s1) (show $ apply s1 t1))
    s1<-tyCheck b env t1
    s2<-tyCheckArgs bs env (apply s1 t2)
    --failure (TyUnknown (show $ s2 `scomp` s1))
    return $ s2 `scomp` s1
tyCheckArgs _ _ t = failure $ CouldNotMatchExpectedType "TFun" (show t)

tyOfParamBsN::[Exp]->Env->TyErr Type
tyOfParamBsN [] env = return TProc
tyOfParamBsN (b:bs) env = do
    beta <-newTId
    s1<-tyCheck b env beta
    let t1 = apply s1 beta
    t2<-tyOfParamBsN bs env
    return $ TFun t1 t2

--evIds::Env->Set Id
--evIds env = foldl (\ids (id, t)->if isEventTy t then set1 id `union` ids else ids) nil (rel env)

instance TypeCheck_PCT PT  where
    typeCheck :: PT->Env ->TyErr Env
    typeCheck (Atom e og) env = checkAtom e og env
    typeCheck (OpB top pt1 pt2) env = 
        typeCheck top env>>=typeCheck pt1>>=typeCheck pt2
        --env0<-typeCheck top env
        --env1<-typeCheck pt1 env0
        --when (top == OpInterleave) $ failure $ CouldNotMatchExpectedType (show env0) (show env1)
        -- remove the previous context
        --let env2 = removeFrEnv env1 (SM.keys env1 `sminus` iKs pt1 `sminus` (evIds env1) `sminus` SM.keys env0)
        --typeCheck pt2 env2
    typeCheck (Kappa id ps cts pt) env = do
        -- checks that parameter ids are unique
        let ids = map gParamId ps
        checkIdsUnique id ids
        --when (id == "HouseAlarm") $ failure $ TyUnknown (show env) 
        env'<-if id `inEnv` env then do
               t<-typeForK ps env
               s<-tyCheck id env t
               let env0 = applyEnv s (env `override` (set1 $ (id, apply s t)))
               env1<-typeCheckPs ps (apply s t) env0 >>= tyCheckKHs cts
            --when (id == "SeizeControl") $ failure $ IncompatibleTypesInExp (show s) (show env0) (show $ apply s t)
            --env1<-tyCheckKHs cts env0
            --env0<-typeCheckPs ps (apply s t) (env `override` (set1 $ (id, apply s t))) 
            --env0<-tyCheckKHs cts (env `override` (set1 $ (id, apply s t))) 
               env2<- typeCheck cts env1
               env3<- typeCheck pt env2 
               --when (id == "HouseAlarm") $ failure $ IncompatibleTypesInExp  (show s) (show env3) (show $ apply s t)
            --let env' = (applyEnv s env2)
            --removeFrEnv (applyEnv s env2) (SM.keys env2 `sminus` (evIds env2) `sminus` SM.keys env)
               return env3
            else do
               t<-typeForK ps env
               let env1 = newId id env t
               env2<-typeCheck ps env1>>=tyCheckKHs cts>>=typeCheck cts>>=typeCheck pt
               --env3<-typeCheck cts env1>>=typeCheck pt 
               return env2
               -- removeFrEnv env' (SM.keys env' `sminus`  (evIds env') `sminus` SM.keys env `sminus` (set1 id)) 
        return $ (dsub env' ids) `union` (dres env ids)      
        --when (isAtom pt1 && (isExpDot . gExpOfAt $ pt1) && (gIdFrExp . gExp1OfDot . gExpOfAt $ pt1) == "steal") $ do
        --    let ot' = SM.lookup env' "steal"
        --    failure $ CouldNotMatchExpectedType (show env) (show env')
        --where isAtom (Atom _ _) = True
        --      isAtom _ = False
        --      gExpOfAt (Atom e _) = e
        --      isExpDot (ExpDot _ _) = True
        --      isExpDot _ = False
        --      gExp1OfDot (ExpDot e _) = e
--    typeCheck (Kappa pd) env = typeCheck pd env
    typeCheck (OpKappa rop pt) env = do
        env''<-typeCheck rop env 
        env'<-typeCheck pt env''
        --when (gIdOfRop rop == "e") $ do failure $ TyUnknown (show env') 
        return $ dsub env' (set1 $ gIdOfRop rop) `union` (dres env (set1 $ gIdOfRop rop))
        --newId id env' TProc >>= typeCheck pt
    typeCheck (Rho id og bs rs) env = do
        unless (dom_of rs `cross` (singles TEvent) `subseteq` env) $ failure (NoMatchingEvents $ toList . dom_of $ rs)
        unless (img env (ran_of rs) `subseteq` singles TEvent) $ failure (NoMatchingEvents $ toList . ran_of $ rs)
        if id `inEnv` env then do
            t<-typeOf id env
            --when (id == "HouseAlarm") $ failure (TyUnknown (show t))
            s1<-tyCheckArgs bs env t
            s2<-tyCheck og env TBool
            --let env' = applyEnv (s2 `scomp` s1) env
            --let env'' = SM.putAll env' (ran_of rs `cross` singles TEvent)
            --when (id == "SeizeControl") $ failure $ IncompatibleTypesInExp (show bs) (show env'') (show s1)
            return $ (applyEnv (s2 `scomp` s1) env) `override` (ran_of rs `cross` singles TEvent)
        else do
            failure $ InvalidReferenceToProcess id
            --failure $ CouldNotMatchExpectedType id (show env)
            -- t<-tyOfParamBsN bs env
            -- env'<-newId id env t
            -- s1<-tyCheck og env' TBool
            -- return $ SM.putAll (applyEnv s1 env') (ran_of rs `cross` singles TEvent)
    typeCheck StopT env = return env
    typeCheck SkipT env = return env
    typeCheck NilT env = return env

--typeCheckPTH::PT->Env->TyErr Env
--typeCheckPTH (Kappa pd) env = tyCheckKH pd env
--typeCheckPTH (OpB top pt1 pt2) env = typeCheckPTH pt1 env>>=typeCheckPTH pt2
--typeCheckPTH _ env = return env

--typeCheckPTHs::[PT]->Env->TyErr Env
--typeCheckPTHs pts env = foldM (\env pt->typeCheckPTH pt env) env pts 

instance TypeCheck_PCT [PT] where
    typeCheck :: [PT]->Env ->TyErr Env
    typeCheck pts env = 
        foldM (\env' pt->typeCheck pt env') env pts

typecheck_pctd::PCTD->TyErr Env
typecheck_pctd (PCTD _ dts ps pds) = do
   typeCheck dts nilEnv >>= typeCheck ps>>=tyCheckKHs pds >>=typeCheck pds
   

