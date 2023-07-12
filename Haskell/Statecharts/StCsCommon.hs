---------------------
-- Project: Fragmenta
-- Module: 'StCsCommon'
-- Description: Module with common statecharts data types 
-- Author: Nuno Amálio
--------------------
module Statecharts.StCsCommon(StateTy(..), Name, Exp, Guard, Event, Action, frCMMTyToStTy) where

import Statecharts.StCs_MM_Names

type Name = String
type Exp = String
type Guard = Exp
type Event = Exp
type Action = Exp 


-- A state may either be start, end, mutable, or history
data StateTy = StartSt | EndSt | MutableSt | HistorySt
   deriving(Eq, Show)

frCMMTyToStTy :: StCs_CMM_Ns -> StateTy
frCMMTyToStTy (CMM_StartState) = StartSt
frCMMTyToStTy (CMM_EndState) = EndSt
frCMMTyToStTy (CMM_MutableState ) = MutableSt
frCMMTyToStTy (CMM_HistoryState) = HistorySt