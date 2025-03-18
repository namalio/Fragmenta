------------------------
-- Project: Fragmenta
-- Module: 'MMI'
-- Description: The MMI (meta-model information) structure
-- Author: Nuno Amálio
------------------------
{-# LANGUAGE TemplateHaskell #-}
module MMI (
  MMI
  , consMMI
  , gCMM
  , gAMM
  , gRM
  , gCRSG)
where

import Gr_Cls
import Grs
import SGrs
import Mdls 
import Control.Lens

data MMI a b = MMI 
  {_cmm :: Mdl a b -- concrete metamodel
  , _amm :: Mdl a b -- abstract metamodel
  , _rm :: GrM a b -- refinement morphism
  , _crsg :: SGr a b -- concrete and resolved SG
  } deriving (Show)

makeLenses ''MMI

consMMI::Mdl a b->Mdl a b->GrM a b->SGr a b->MMI a b
consMMI = MMI 

-- extracts concrete metamodel
gCMM::MMI a b->Mdl a b
gCMM mmi = mmi^.cmm

-- extracts abstract metamodel
gAMM::MMI a b->Mdl a b
gAMM mmi = mmi^.amm

-- extracts refinement morphism
gRM::MMI a b->GrM a b
gRM mmi = mmi^.rm

-- extracts metamodel's concrete and resolved SG 
gCRSG::MMI a b->SGr a b
gCRSG mmi = mmi^.crsg

