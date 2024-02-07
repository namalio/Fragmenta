---------------------
-- Project: Fragmenta
-- Module: 'StCsParsing'
-- Description: Parses statechart textual descriptions to produce a graph with typing
-- Author: Nuno Amálio
--------------------
module Statecharts.StCsParsing(loadStC) where

import Text.ParserCombinators.ReadP
import Control.Applicative
import Control.Monad(when)
import Grs
import SGrs
import Sets
import Relations
import TheNil
import MyMaybe
import GrswT
import ParseUtils
import Statecharts.StCs_MM_Names
import SimpleFuns
import ParsingCommon
import Statecharts.StCsCommon
import Gr_Cls


-- An actual state has a name, a kind and a list of descriptions (for mutable states only)
data State = State Name StateTy [StCDesc]
   deriving(Eq, Show)

-- A transition has a name, source and target states, an event, an optional guard, and an optional action
data Transition = Transition Name Name Name (Maybe Event) (Maybe Guard) (Maybe Action) 
   deriving(Eq, Show) 

-- An element is either a state or a transition
data Elem = ElemSt State | ElemT Transition
   deriving(Eq, Show) 

 -- A StC description has a name and a list of elements
data StCDesc = StCDesc Name [Elem]
   deriving(Eq, Show)

data StCModel = StCModel Name [StCDesc]
   deriving(Eq, Show)

isState (ElemSt _) = True
isState _ = False
isEndState (State _ EndSt _) = True
isEndState _ = False
isHistoryState (State _ HistorySt _) = True
isHistoryState _ = False
isTransition (ElemT _) = True
isTransition _ = False

-- isNode (ElemC _) = False
gDescName (StCDesc nm _) = nm
gElems :: StCDesc -> Set Elem
gElems (StCDesc _ es) = set es
getSt (ElemSt st) = st
getT (ElemT t) = t



getNameOfT(Transition nm _ _ _ _ _) = nm
getEventOfT(Transition _ _ _ e _ _) = e
getGuardOfT(Transition _ _ _ _ g _) = g
getActionOfT(Transition _ _ _ _ _ a) = a
getSrcOfT(Transition _ s _ _ _ _) = s
getTgtOfT(Transition _ _ t _ _ _) = t

gStName (State nm _ _) = nm
gStTy (State _ ty _) = ty
gStDescs :: State -> Set StCDesc
gStDescs (State _ _ ds) = set ds

gCMMTy (State _ StartSt _) = CMM_StartState
gCMMTy (State _ EndSt _) = CMM_EndState
gCMMTy (State _ HistorySt _) = CMM_HistoryState
gCMMTy (State _ MutableSt _) = CMM_MutableState

getStates desc = foldr (\e es-> if isState e then (getSt e) `intoSet` es else es) nil (gElems desc)
getTransitions desc = foldr (\e es-> if isTransition e then (getT e) `intoSet` es else es) nil (gElems desc)
-- getTheCs elems = foldl (\es e-> if not . isNode $ e then (getC e):es else es) [] elems

stc_model :: ReadP StCModel
stc_model = do
   string "StCModel"
   skipSpaces
   nm<-parse_id 
   skipSpaces
   char ':'
   skipSpaces
   ds<- manyTill (stc_desc) eof
   skipSpaces
   return (StCModel nm ds)

stc_desc :: ReadP StCDesc
stc_desc = do
   string "StC"
   skipSpaces
   nm<-parse_id 
   skipSpaces
   char '{'
   skipSpaces
   es<-manyTill stc_elem (char '}')
   skipSpaces
   return (StCDesc nm es)

stc_state_inner::ReadP [StCDesc]
stc_state_inner = do
   char '{'
   skipSpaces
   descs<- many1 (stc_desc)
   skipSpaces
   char '}'
   return (descs)

stc_state :: ReadP State
stc_state = do
   string "state"
   skipSpaces
   nm<-parse_id
   skipSpaces
   descs<- stc_state_inner <++ return [] 
   skipSpaces
   return (State nm MutableSt descs)

stc_start_state :: ReadP State
stc_start_state = do
   string "start"
   skipSpaces
   nm<-parse_id
   skipSpaces
   return (State nm StartSt [])

stc_end_state :: ReadP State
stc_end_state = do
   string "end"
   skipSpaces
   nm<-parse_id
   skipSpaces
   return (State nm EndSt [])

stc_history_state :: ReadP State
stc_history_state = do
   string "history"
   skipSpaces
   nm<-parse_id
   skipSpaces
   return (State nm HistorySt [])

tevent :: ReadP (Maybe Action)
tevent = do
   char ':'
   e <- parse_until_chs "\n/["
   return (Just e)

tguard :: ReadP (Maybe String)
tguard = do
   char '['
   g <- parse_until_chs "]"
   char ']'
   return (Just g)

taction :: ReadP (Maybe Action)
taction = do
   char '/'
   a <- parse_id
   return (Just a)

stc_transition :: ReadP Transition
stc_transition = do
   string "transition"
   skipSpaces
   nm<-parse_id
   skipSpaces
   src<-parse_id
   skipSpaces
   string "->"
   skipSpaces
   tgt<-parse_id
   skipSpaces
   ev<-option Nothing tevent
   skipSpaces
   g<-option Nothing tguard
   skipSpaces
   a<-option Nothing taction
   skipSpaces
   return (Transition nm src tgt ev g a)

stc_elemSt :: ReadP Elem
stc_elemSt = do
   st<-stc_state <|> stc_start_state <|> stc_end_state <|> stc_history_state
   return (ElemSt st)

stc_elemT :: ReadP Elem
stc_elemT = do
   t<-stc_transition
   return (ElemT t)

stc_elem :: ReadP Elem
stc_elem  = do
   e<- stc_elemSt <|> stc_elemT
   return e

loadStCFrFile :: FilePath -> IO (Maybe StCModel)
loadStCFrFile fn = do   
    contents <- readFile fn
    --makes sure it is read
    let stc = parseMaybe stc_model contents
    return stc

-- builds the name of an edge from a node
mkenm_frn n = "E"++n

cNm nm = nm++"_"
descId nm = nm ++ "_Desc"
stId :: String -> String
stId nm = nm ++ "_St"

-- builds id of entity being named and actual id being assigned to entity
mk_nm_info_q :: String->String-> ((String, String), (String, String), (String, String), (String, String))
mk_nm_info_q snm nm = ((nm, show_cmm_n CMM_Name), ("ENmOf"++snm, show_cmm_e CMM_ENamed_name), 
                      ("ENmOf"++snm, snm), ("ENmOf"++snm, nm))

-- builds the contains
consContainsT nm src = ((mkenm_frn $ "Contains"++ nm, show_cmm_e CMM_EContains), 
   (mkenm_frn $ "Contains" ++ nm, src), (mkenm_frn $ "Contains" ++ nm, nm))

consGwT_InitQ :: String->(Set (String, String), Set (String, String),Set (String, String), Set (String, String))
consGwT_InitQ nm  = 
   let ns_m_i = singles ("StCModel_", show_cmm_n CMM_StCModel) in 
   (mk_nm_info_q "StCModel_" nm) `combineQwIntoS` (ns_m_i, nil, nil, nil)

consGwT_desc :: String-> StCDesc->(Set (String, String), Set (String, String),Set (String, String), Set (String, String))
consGwT_desc snm desc  = 
   let dnm = descId $ gDescName desc 
       ns_m_i = singles (dnm, show_cmm_n CMM_StCDesc) 
       es_m_i = (singles (mkenm_frn $ snm ++ "_" ++ dnm, show_cmm_e CMM_EHasDesc), 
                 singles (mkenm_frn $ snm ++ "_" ++ dnm, snm), 
                 singles (mkenm_frn $ snm ++ "_" ++ dnm, dnm)) 
       names_q = (mk_nm_info_q dnm (gDescName desc)) `combineQwIntoS` nilQS in
   names_q `combineQwUnion` (makeQFrTFst ns_m_i es_m_i)
   `combineQwUnion` (consGwT_Sts desc) `combineQwUnion` (consGwT_Ts desc)

consGwT_Sts :: StCDesc->(Set (String, String), Set (String, String),Set (String, String), Set (String, String))
consGwT_Sts desc = 
   let cons_st_q_final s = let snm = stId $ gStName s in let sty = gCMMTy s in 
                           if sty /= CMM_MutableState then nilQS
                               else (mk_nm_info_q snm (gStName s)) 
                               `combineQwIntoS` (foldr(\d aq->(consGwT_desc snm d) `combineQwUnion` aq) nilQS $ gStDescs s) in
   let cons_st_q s = let snm = stId $ gStName s in  
          (makeQFrTFst (snm, show_cmm_n $ gCMMTy s) (consContainsT snm $ descId (gDescName desc))) 
          `combineQwIntoS` (cons_st_q_final s) in
   foldr (\s ss->(cons_st_q s) `combineQwUnion` ss) nilQS (getStates desc)

consGwT_Ts::StCDesc ->(Set (String, String), Set (String, String),Set (String, String), Set (String, String))
consGwT_Ts desc = 
   foldr (\t qs->(consGwT_T t desc) `combineQwUnion` qs) nilQS (getTransitions desc)

consGwT_T :: Transition-> StCDesc-> (Set (Name, String), Set ([Char], [Char]), Set ([Char], [Char]),
    Set ([Char], [Char]))
consGwT_T t desc = 
   let tnm = getNameOfT t 
       tq = (makeQFrTFst (tnm, show_cmm_n CMM_Transition) $ consContainsT tnm (descId $ gDescName desc)) 
       enm = "Ev" ++ tnm 
       exp_nm nm e = nm ++ "Exp:" ++ e 
       oe = getEventOfT t 
       ev_q = if isNil oe then nilQS 
              else (set [(enm, show_cmm_n CMM_Event), (exp_nm enm $ the oe, show_cmm_n CMM_Exp)], 
              set [(mkenm_frn enm, show_cmm_e CMM_ETransition_event), 
               (mkenm_frn $ exp_nm enm "", show_cmm_e CMM_EWExp_exp)], 
              set [(mkenm_frn enm, tnm), (mkenm_frn $ exp_nm enm "", enm)], 
              set [(mkenm_frn enm, enm), (mkenm_frn $ exp_nm enm "", exp_nm enm $ the oe)])
       og = getGuardOfT t
       gnm = "G" ++ tnm 
       g_q = if isNil og then nilQS
           else (set [(gnm, show_cmm_n CMM_Guard), (exp_nm gnm (the og), show_cmm_n CMM_Exp)], 
                set [(mkenm_frn gnm, show_cmm_e CMM_ETransition_guard), 
               (mkenm_frn $ exp_nm gnm "", show_cmm_e CMM_EWExp_exp)],
               set [(mkenm_frn gnm, tnm), (mkenm_frn $ exp_nm gnm "", gnm)], 
               set [(mkenm_frn gnm, gnm), (mkenm_frn $ exp_nm gnm "", exp_nm gnm $ the og)])
       oa = getActionOfT t 
       anm = "A" ++ tnm 
       a_q = if isNil oa then nilQS 
          else (set [(anm, show_cmm_n CMM_Action), (exp_nm anm (the oa), show_cmm_n CMM_Exp)], 
          set [(mkenm_frn anm, show_cmm_e CMM_ETransition_action), 
           (mkenm_frn $ exp_nm anm "", show_cmm_e CMM_EWExp_exp)],
          set [(mkenm_frn anm, tnm), (mkenm_frn $ exp_nm anm "", anm)], 
          set [(mkenm_frn anm, anm), (mkenm_frn $ exp_nm anm "", exp_nm anm $ the oa)]) 
       s_t_q = (nil, set [(mkenm_frn $ tnm ++ "src", show_cmm_e CMM_ETransition_src), 
               (mkenm_frn $ tnm ++ "tgt", show_cmm_e CMM_ETransition_tgt)], 
               set [(mkenm_frn $ tnm ++ "src", tnm), (mkenm_frn $ tnm ++ "tgt", tnm)], 
               set [(mkenm_frn $ tnm ++ "src", stId $ getSrcOfT t), 
                (mkenm_frn $ tnm ++ "tgt", stId $ getTgtOfT t)]) in
   (((tq `combineQwIntoS` ev_q) `combineQwUnion` g_q) `combineQwUnion` a_q) `combineQwUnion` s_t_q

-- Constructs the graph with typing for given  StC model
consGwTFrStc :: StCModel -> GrwT String String
consGwTFrStc (StCModel nm descs)  = 
   -- initial set of nodes with type mapping
   let (ns_m, es_m, src_m, tgt_m) = (consGwT_InitQ nm) 
               `combineQwUnion` foldr(\d q->(consGwT_desc "StCModel_" d) `combineQwUnion` q) nilQS (set descs)
       pcg = consG (fmap fst ns_m) (fmap fst es_m) src_m tgt_m in
   consGWT pcg (consGM ns_m es_m)
   
--is_wf_stcdef (StCDef d) = start `elem` (map (\(Node nm _)->nm) (getTheNodes elems))

loadStC :: FilePath -> IO (GrwT String String)
loadStC fn = do
   ostc <- loadStCFrFile fn
   if (isNil ostc) 
      then do
         putStrLn "The StC definition could not be parsed."
         return Gr_Cls.empty
      else do
         let pc_gs = consGwTFrStc $ the ostc
         return pc_gs

process_stc_def :: FilePath -> IO ()
process_stc_def fn = do
   stc<-loadStCFrFile fn
   putStrLn $ show stc

def_path = "StateCharts/"

complexSt = "state Processing {\n"
   ++ "StC Processing (DoingAs) {\n"
   ++ "state DoingAs\n"
   ++ "state DoingBs\n"
   ++ "state DoingCs\n"
   ++ "transition AsToBs DoingAs->DoingBs:b\n"
   ++ "transition KeepAs DoingAs->DoingAs:a\n"
   ++ "transition KeepBs DoingBs->DoingBs:b\n"
   ++ "transition BsToCs DoingBs->DoingCs:c\n"
   ++ "transition KeepCs DoingCs->DoingCs:c\n"
   ++ "}\n"
   ++ "}"

test1 = readP_to_S stc_state "state VFalse"
test2 = readP_to_S stc_transition "transition FalseToTrue VFalse->VTrue:assignT"
test3 = do 
   stc<-loadStC (def_path ++ "boolSetter.stc")
   putStrLn $ show stc
test4 = readP_to_S stc_transition "transition BuzzingToMuted Buzzing->Muted:after(3sec)/mute"
test5 = readP_to_S stc_transition "transition BuzzerInit init->Muted"
test6 = readP_to_S stc_end_state "end endSt"
test7 = readP_to_S stc_state complexSt

test8 = readP_to_S stc_transition "transition FrHappy Happy->Angry:chSound[in(Muted)]"

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