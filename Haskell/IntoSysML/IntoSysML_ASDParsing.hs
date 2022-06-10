---------------------
-- Project: Fragmenta
-- Module: 'ASDParsing'
-- Description: Parses SysML architecture structure diagrams (a subset of SysML block diagrams) textual descriptions to produce 
--  a graph with typing
-- Author: Nuno Amálio
--------------------
module IntoSysML.ASDParsing(loadASD) where

import Text.ParserCombinators.ReadP
import Control.Applicative
import Control.Monad(when)
import Grs
import SGrs
import Sets
import Relations
import The_Nil
import MyMaybe
import GrswT
import ParseUtils
import IntoSysML.ASD_MM_Names
import SimpleFuns
import CommonParsing
--import Statecharts.StCsCommon


-- Names are represented as strings
type Name = String

-- Expressions are represented as strings
type Exp = String

-- Primitive types
data PType = PReal | PString | PBool | PNat | PInt | Pinterval int int
  deriving(Eq, Show, Read) 

-- A mulplicity value is either a natural number or many ('*') 
data MultVal = MultN int | MMany
   deriving(Eq, Show) 

data Mult =  MultS MultVal | MultR int MultVal
   deriving(Eq, Show) 

data MultCompSrc = Optional | Compulsory
   deriving(Eq, Show, Read) 

-- Properties, a name, a type id, and an optional initialisation expression
data Property = Property Name Name Exp
   deriving(Eq, Show) 

-- Variable kinds: either plain variables or parameters
data VariableKind = Var | Parameter
   deriving(Eq, Show) 

-- A variable has a kind and an embedded property
data Variable = Variable VariableKind Property 
   deriving(Eq, Show) 

-- A flowport has a kind, an embedded property and a lists of dependencies (names of other ports)
data FlowPort = InFlowPort Property | OutFlowPort Property [Name]
   deriving(Eq, Show) 

-- Components are either cyber, subsystem or physical
data ComponentKind = Cyber | Subsystem | Physical 
   deriving(Eq, Show) 

-- The phenomena of a compound component can either be discrete or continuous
data PhenomenaKind = Discrete | Continuous
   deriving(Eq, Show, Read) 

--
-- A block component comprises a kind, a list of flow ports and a list of variables
data BComponent = BComponent ComponentKind [FlowPort] [Variable] 
   deriving(Eq, Show) 

-- A Block is either a system, a compound, or a block element
data Block = BSystem Name [FlowPort] 
   | BCompound Name PhenomenaKind BComponent
   | BElement Name BComponent
   deriving(Eq, Show) 

-- A value type definition is either an enumeration, a structural type, a derived type or a unit type
data VTypeDef = VTypeEnum Name [Name] | VTypeStrt Name [Property] | DType Name PType | UnitType Name PType Name
   deriving(Eq, Show) 

-- A composition has a source and target block and a source and a target multiplicity
--data Composition = Composition Block Block Mult Mult

 -- An ASD element is either a value type definition, a block definition or a composition
data ASDElem = ElemVT VTypeDef 
   | ElemB Block 
   | ElemC Name Name MultCompSrc Mult -- A composition has a source and target block (two names) and a source and a target multiplicity
   deriving(Eq, Show)

-- An ASD description comprises a name followed by a number of elements
data ASDDesc = ASDDesc Name [ASDElem]
   deriving(Eq, Show)

-- Functions to retrieve components of a composition
getSrc (Composition s _ _ _) = s
getTgt (Composition _ t _ _) = t
getSrcM (Composition _ _ sm _) = sm
getTgtM (Composition _ _ _ tm) = tm

-- getStates desc = foldr (\e es-> if isState e then (getSt e):es else es) [] (gElems desc)
-- getTransitions desc = foldr (\e es-> if isTransition e then (getT e):es else es) [] (gElems desc)
-- getTheCs elems = foldl (\es e-> if not . isNode $ e then (getC e):es else es) [] elems

parse_ASD :: ReadP ASD
parse_ASD = do
   string "ASD"
   skipSpaces
   nm<-parse_id 
   skipSpaces
   char ':'
   skipSpaces
   es<- manyTill (asd_elem) eof
   skipSpaces
   return (ASDDesc nm es)

parse_venum :: ReadP VTypeDef
parse_venum = do
   string "enum"
   skipSpaces
   nm<-parse_id 
   skipSpaces
   char ':'
   skipSpaces
   ls<-parse_ls_ids ";" ","
   skipSpaces
   return (VTypeEnum nm ls)

parse_init_exp :: ReadP String
parse_init_exp = do
   char "\""
   iexp<-parse_until_chs "\"" -- Parses until terminators
   skipSpaces
   return (iexp)

parse_property :: ReadP Property
parse_property = do
  string "property"
  skipSpaces
  nm<-parse_id 
  skipSpaces
  vty<-parse_id
  skipSpaces
  iexp<-init_exp <++ return ""
  skipSpaces
  return (Property nm vty iexp)

parse_asd_vstrt :: ReadP VTypeDef
parse_asd_vstrt = do
  string "strt"
  skipSpaces
  nm<-parse_id 
  skipSpaces
  char '{'
  skipSpaces
  ps<-manyTill parse_property (char '}')
  skipSpaces
  return (VTypeStrt nm ps)

parse_pint :: ReadP PType
Parse_pint = do
   string "Int"
   return (PInt)

parse_pnat :: ReadP PType
Parse_pnat = do
   string "Nat"
   return (PNat)

parse_preal :: ReadP PType
Parse_preal = do
   string "Real"
   return (PNat)

parse_pbool :: ReadP PType
Parse_pbool = do
   string "Bool"
   return (PBool)

parse_pstring :: ReadP PType
Parse_pstring = do
   string "String"
   return (PString)

parse_pinterval :: ReadP PType
parse_pinterval = do
  string "Interval" 
  skipSpaces
  n1<-parse_number
  skipSpaces
  n2<-parse_number
  skipSpaces
  return (PInterval (read n1) (read n2))

parse_ptype :: ReadP PType
parse_ptype = do
  pt <- parse_pint <|> parse_pnat <|> parse_preal <|> parse_pbool <|> parse_pstring <|> into_pinterval 
  return pt

parse_dtype :: ReadP VTypeDef
parse_dtype = do
   string "dtype"
   skipSpaces
   nm<-parse_id 
   skipSpaces
   pt<-parse_ptype
   skipSpaces
   return (DType nm pt)

parse_utype :: ReadP VTypeDef
parse_utype = do
   string "utype"
   skipSpaces
   nm<-parse_id 
   skipSpaces
   pt<-parse_ptype
   skipSpaces
   idu<-parse_id
   skipSpaces
   return (UType nm pt idu)

parse_vtype :: ReadP ASDElem
parse_vtype = do
  vt <-parse_vstrt <|> parse_dtype <|> parse_utype <|> parse_venum
  return (ElemVT vt)

parse_infport :: ReadP FlowPort
parse_infport = do
  string "in fport"
  skipSpaces
  p<-parse_property
  skipSpaces
  return (InFlowPort p)


parse_outfport :: ReadP FlowPort
parse_outfport = do
  string "out fport"
  skipSpaces
  p<-parse_property
  skipSpaces
  char '{'
  skipSpaces
  ds<-parse_ls_ids "}" ","
  skipSpaces
  return (OutFlowPort p ds)

parse_fport :: ReadP FlowPort
parse_fport = do
  fp<- parse_infport <|> parse_outfport
  return fp

parse_fports :: ReadP [FlowPort]
parse_fports = do
   string "ports"
   skipSpaces
   char '{'
   skipSpaces
   fps<-manyTill parse_fport (char '}')
   skipSpaces
   return fps

parse_vars :: ReadP [Variable]
parse_vars = do
   string "vars"
   skipSpaces
   char '{'
   skipSpaces
   vs<-manyTill asd_variable (char '}')
   skipSpaces
   return vs

parse_bsys :: ReadP BBlock
parse_bsys = do
   string "system"
   skipSpaces
   nm<-parse_id 
   skipSpaces
   fps<-parse_fports
   skipSpaces
   return (BSystem nm fps)

parse_bphenomena :: ReadP PhenomenaKind
parse_bphenomena = do
  p<- string "Discrete" <|> string "Continuous"
  return (read p)

parse_bcomponent :: ReadP BComponent
parse_bcomponent = do
  sck<-string "cyber" <|> string "physical" <|> string "subsystem" 
  skipSpaces
  fps<-asd_fports
  skipSpaces
  vs<-asd_fports
  skipSpaces
  return (BComponent (read sck) fps vs)

parse_bcompound :: ReadP Block
parse_bcompound = do
   string "compound"
   skipSpaces
   nm<-parse_id 
   skipSpaces
   pk<-parse_bphenomena
   skipSpaces
   c<-parse_bcomponent
   skipSpaces
   return (BCompound nm pk c)

parse_belement :: ReadP Block
parse_belement = do
   string "element"
   skipSpaces
   nm<-parse_id 
   skipSpaces
   c<-parse_bcomponent
   skipSpaces
   return (BElement nm c)

parse_block :: ReadP Block
parse_block = do
   b<-parse_bcompound <|> parse_belement <|> parse_bsys
   return b

parse_eblock :: ReadP ASDElem
parse_eblock = do
   b<-parse_block
   return (ElemB b)

parse_mult_comp_src :: ReadP MultCompSrc
parse_mult_comp_src = do 
   ms<-string "Optional" <|> string "Compulsory"
   return (read ms)

parse_mult_many::ReadP MultVal
parse_mult_many = do
   char '*'
   return (MMany)

parse_mult_n::ReadP MultVal
parse_mult_n = do
   n<-parse_number
   return (MultN $ read n)

parse_mult_val::ReadP MultVal
parse_mult_val = do
   m<-parse_mult_many <|> parse_mult_b
   return m

parse_mults::ReadP Mult
parse_mults = do
   m<-parse_mult_val
   skipSpaces
   return (MultS m)

parse_mult_range::ReadP Mult
parse_mult_range = do
   n<-parse_number
   skipSpaces
   string ".."
   skipSpaces
   m<-parse_mult_val
   skipSpaces
   return (MultR (read n) m)

parse_mult::ReadP Mult
parse_mult = do
   m<-parse_mult_range <|> parse_mults
   return m

parse_composition :: ReadP ASDElem
parse_composition = do
   b1<-parse_id 
   skipSpaces
   b2<-parse_id 
   skipSpaces
   srcM<-parse_mult_comp_src 
   skipSpaces
   tgtM<-parse_mult
   skipSpaces
   return (ElemC b1 b2 srcM tgtM)

asd_elem :: ReadP ASDElem
asd_elem = do
   e<-parse_bblock <|> parse_vtype <|> parse_composition
   return e


def_path = "IntoSysML/"

test1 = readP_to_S parse_mults "5"
--test2 = readP_to_S stc_transition "transition FalseToTrue VFalse->VTrue:assignT"
--test3 = do 
--   stc<-loadStC (def_path ++ "boolSetter.stc")
--   putStrLn $ show stc
--test4 = readP_to_S stc_transition "transition BuzzingToMuted Buzzing->Muted:after(3sec)/mute"
--test5 = readP_to_S stc_transition "transition BuzzerInit init->Muted"
--test6 = readP_to_S stc_end_state "end endSt"
--test7 = readP_to_S stc_state complexSt

-- test1 = readP_to_S pc_def tb_pc_def
-- test2 = process_pc_def (def_path ++ "PC_CashMachine.pc")
-- test3 = process_pc_def (def_path ++ "PC_CashMachineOps.pc")
-- test4 = readP_to_S (pc_params '.' "@;\n") ".abc1;abc2@"
-- test5 = readP_to_S pc_atom "atom someoneEnters-e:ges\n"
-- test6 = readP_to_S pc_reference "reference RefTimer.Timer;3[timeout/mute]\n"
-- test7 = readP_to_S pc_refC "ref_connector RefHouseAttacker->HouseAttacker.bes,mes,ses\n"
-- test8 = readP_to_S pc_afterC "after_connector open a->b\n"
-- test9 = readP_to_S pc_refC "ref_connector RefHouseAlarm0->HouseAlarm0.False,False\n"
-- test10 = readP_to_S pc_opBG "op_connector_g OpAuthenticate->OpAuthenticateChoice{n>0}\n"
-- test11 = readP_to_S pc_atom "atom timeout{t==0}\n"
-- test12 = readP_to_S pc_atom "atom someoneMoves<:eas>{active and (not triggered)}\n"
-- test13 = readP_to_S pc_atom "atom grab<:{grabLaptop,grabJewels}>\n"
-- test14 = readP_to_S 
-- test9 = loadPC get_sg_pcs_mm def_path "../pcs/PC_SimpleLife.pc"