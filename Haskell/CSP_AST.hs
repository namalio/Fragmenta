
------------------
-- Project: PCs/Fragmenta
-- Module: 'CSP_AST'
-- Description: Module that represents CSP's abstract syntax tree (AST)
-- Author: Nuno Amálio
-----------------
module CSP_AST(Id, Decl(..), Exp(..), CSPSpec(..), isAtomicExp, isComposite, isExtChoice) where

import Sets

type Id = String

data Decl = Channel (Set Id) | EqDecl Exp Exp | Include (Set Id) deriving(Show) 
--data Stmt = Stmt Id Exp deriving(Show) 
data Exp = ExpId Id -- a name
   | ExpApp Id [Id] -- function application
   | ExpPar Exp -- a parenthesised expression
   | GExp Exp Exp
   | IfExp Exp Exp Exp
   | Prfx Exp Exp
   | ExtChoice Exp Exp
   | IntChoice Exp Exp
   | RExtChoice Id Id Exp -- name of variable, identifier of set and expression '[] x : s @ Exp' 
   | SeqComp Exp Exp
   | Parallel [Id] Exp Exp
--   | SyncInterrupt [String] Exp Exp
   | Throw [String] Exp Exp
   | Interleave Exp Exp
   | STOP 
   | SKIP
   | LetW [Decl] Exp 
   | ExpRen Exp [(Id, Id)] -- Renaming
   deriving(Show) 

data CSPSpec = CSP [Decl] deriving(Show) 

isAtomicExp :: Exp -> Bool
isAtomicExp (ExpId _)    = True
isAtomicExp (ExpApp _ _) = True
isAtomicExp (ExpPar _)   = True
isAtomicExp (GExp _ _)   = True
isAtomicExp (IfExp _ _ _) = True
isAtomicExp (Prfx _ _) = True
isAtomicExp (STOP) = True
isAtomicExp (SKIP) = True
isAtomicExp (LetW _ _) = True
isAtomicExp (ExpRen _ _) = True
isAtomicExp _ = False

isComposite :: Exp -> Bool
isComposite = not . isAtomicExp

isExtChoice :: Exp -> Bool
isExtChoice (ExtChoice _ _) = True
isExtChoice _ = False