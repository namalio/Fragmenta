------------------------
-- Project: Fragmenta
-- Module: 'MMI'
-- Description: The MMI (meta-model information) structure
-- Author: Nuno Amálio
------------------------

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

data MMI a b = MMI (Mdl a b) (Mdl a b) (GrM a b) (SGr a b) 
  deriving (Show)

consMMI::Mdl a b->Mdl a b->GrM a b->SGr a b->MMI a b
consMMI = MMI 

-- extracts concrete metamodel
gCMM::MMI a b->Mdl a b
gCMM (MMI cmm _ _ _) = cmm
-- extracts abstract metamodel
gAMM::MMI a b->Mdl a b
gAMM (MMI _ amm _ _) = amm
-- extracts refinement morphism
gRM::MMI a b->GrM a b
gRM (MMI _ _ rm _) = rm
-- extracts resolved sg of concrete metamodel
gCRSG::MMI a b->SGr a b
gCRSG  (MMI _ _ _ sgcmm) = sgcmm
-- extracts the graph with typing 
--gGwT::MMI a b->Maybe (GrwT a b)
--gGwT(MMI _ _ _ _ gwt) = gwt

--mmi_cmm MMI {cmm_ = cmm, amm_ = _, rm_ = _, sg_cmm_ = _} = cmm
--mmi_amm MMI {cmm_ = _, amm_ = amm, rm_ = _, sg_cmm_ = _} = amm
--mmi_rm MMI {cmm_ = _, amm_ = _, rm_ = rm, sg_cmm_ = _} = rm
--mmi_sg_cmm MMI {cmm_ = _, amm_ = _, rm_ = _ , sg_cmm_ = sgcmm} = sgcmm