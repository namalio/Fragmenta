
------------------
-- Project: PCs/Fragmenta
-- Module: 'CSP_AST'
-- Description: Module that represents CSP's abstract syntax tree (AST)
-- Author: Nuno Amálio
-----------------
module CSP.CSP_AST
   (Id
   , Ty(..)
   , TyE(..)
   , DTyTerm (..)
   , Decl(..)
   , Exp(..)
   , Spec(..)
   , BOp(..)
   , UOp(..)
   , Token(..)
   , ChL(..)
   , isAtomicExp
   , isComposite
   , isExtChoice) 
where

import Sets

type Id = String

data Ty = TyInt | TyBool | TyEvent | TyDot Ty Ty | TySet Ty | TyId Id
   deriving (Show)

data TyE = Ty Ty | Sete [Id]
   deriving (Show)
   
data DTyTerm = DTyTerm Id [Ty]
   deriving(Show) 
data Decl = Channel (Set Id) (Maybe Ty) | EqDecl Exp Exp | Include (Set Id) | DataTy Id [DTyTerm]
   deriving(Show) 

data BOp = Plus | Minus | Product | Div | Remainder | Or | And | GEQ | LEQ | GT | LT | EQ | NEQ 
         | Member | NotMember | Union | Intersection | SMinus
   deriving(Show, Eq) 

data UOp = UMinus | UNot
   deriving(Show) 

data Token = TokenInt Int | TokenT | TokenF
   deriving(Show) 

-- Choice literal: internal or external
data ChL = Int | Ext
   deriving (Show)

--data Stmt = Stmt Id Exp deriving(Show) 
data Exp = 
   ExpId String -- a name 
   | ExpApp Id [Exp]    -- function application
   | ExpPar Exp         -- a parenthesised expression
   | ExpBOp Exp BOp Exp -- A binary expression
   | ExpUOp UOp Exp     -- A unary expression
   | ExpToken Token     -- An expression with a recognised token
   | ExpSetE [Exp]      -- A set extension expression
   | GExp Exp Exp       -- A guarded expression
   | ExpDotted Exp Exp  -- A dotted expression: c.e
   | IfExp Exp Exp Exp  -- An if expression
   | Prfx Exp Exp       -- Prefix
   | Choice ChL Exp Exp
   | RChoice ChL Id TyE Exp -- name of variable, identifier of set and expression '[] x : s @ Exp' 
   -- | RIntChoice Id Id Exp -- name of variable, identifier of set and expression '|~| x : s @ Exp' 
   | SeqComp Exp Exp
   | Parallel [Exp] Exp Exp
--   | SyncInterrupt [String] Exp Exp
   | Throw [Exp] Exp Exp
   | Interleave Exp Exp
   | STOP 
   | SKIP
   | LetW [Decl] Exp 
   | ExpRen Exp [(Id, Id)] -- Renaming
   deriving(Show) 

data Spec = CSP [Decl] deriving(Show) 

isAtomicExp :: Exp -> Bool
isAtomicExp (ExpId _)    = True
isAtomicExp (ExpApp _ _) = True
isAtomicExp (ExpPar _)   = True
isAtomicExp (ExpToken _)    = True
isAtomicExp (GExp _ _)   = True
isAtomicExp (IfExp _ _ _) = True
isAtomicExp (Prfx _ _) = True
isAtomicExp STOP = True
isAtomicExp SKIP = True
isAtomicExp (LetW _ _) = True
isAtomicExp (ExpRen _ _) = True
isAtomicExp _ = False

isComposite :: Exp -> Bool
isComposite = not . isAtomicExp

isExtChoice :: Exp -> Bool
isExtChoice (Choice Ext _ _) = True
isExtChoice _ = False