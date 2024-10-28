
------------------
-- Project: PCs/Fragmenta
-- Module: 'CSP_AST'
-- Description: Module that represents CSP's abstract syntax tree (AST)
-- Author: Nuno Amálio
-----------------
module CSP.CSP_AST(Id
   , Decl(..)
   , Exp(..)
   , CSPSpec(..)
   , BOp(..)
   , UOp(..)
   , Token(..)
   , isAtomicExp
   , isComposite
   , isExtChoice) 
where

import Sets
import Data.Bits (And)

type Id = String

data Decl = Channel (Set Id) | EqDecl Exp Exp | Include (Set Id) 
   deriving(Show) 

data BOp = Plus | Minus | Product | Div | Remainder | Or | And | GEQ | LEQ | GT | LT | EQ | NEQ
   deriving(Show) 

data UOp = UMinus | UNot
   deriving(Show) 

data Token = TokenInt Int | TokenT | TokenF
   deriving(Show) 

--data Stmt = Stmt Id Exp deriving(Show) 
data Exp = ExpId String -- a name 
   | ExpApp Id [Exp]    -- function application
   | ExpPar Exp         -- a parenthesised expression
   | ExpBOp Exp BOp Exp -- A binary expression
   | ExpUOp UOp Exp     -- A unary expression
   | ExpToken Token     -- An expression with a recognised token
   | ExpSetE [Exp]      -- A set extension expression
   | GExp Exp Exp       -- A guarded expression
   | ExpChannel Id Exp  -- A channel expression: c.e
   | IfExp Exp Exp Exp  -- An if expression
   | Prfx Exp Exp       -- Prefix
   | ExtChoice Exp Exp
   | IntChoice Exp Exp
   | RExtChoice Id Id Exp -- name of variable, identifier of set and expression '[] x : s @ Exp' 
   | RIntChoice Id Id Exp -- name of variable, identifier of set and expression '|~| x : s @ Exp' 
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

data CSPSpec = CSP [Decl] deriving(Show) 

isAtomicExp :: Exp -> Bool
isAtomicExp (ExpId _)    = True
isAtomicExp (ExpApp _ _) = True
isAtomicExp (ExpPar _)   = True
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
isExtChoice (ExtChoice _ _) = True
isExtChoice _ = False