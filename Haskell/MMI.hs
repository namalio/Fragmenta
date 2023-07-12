------------------------
-- Project: Fragmenta
-- Module: 'MMI'
-- Description: The MMI (meta-model information) structure
-- Author: Nuno Amálio
------------------------

module MMI (MMI, cons_mm_info, mmi_cmm, mmi_amm, mmi_rm, mmi_sg_cmm)
where

import Gr_Cls
import Grs
import SGrs
import Mdls 

data MMI a b = MMI {cmm_ :: Mdl a b, amm_ :: Mdl a b, rm_:: GrM a b, sg_cmm_ :: SGr a b}
  deriving (Show)

cons_mm_info cmm amm rm sgcmm = MMI {cmm_ = cmm, amm_ = amm, rm_ = rm, sg_cmm_ = sgcmm}

mmi_cmm MMI {cmm_ = cmm, amm_ = _, rm_ = _, sg_cmm_ = _} = cmm
mmi_amm MMI {cmm_ = _, amm_ = amm, rm_ = _, sg_cmm_ = _} = amm
mmi_rm MMI {cmm_ = _, amm_ = _, rm_ = rm, sg_cmm_ = _} = rm
mmi_sg_cmm MMI {cmm_ = _, amm_ = _, rm_ = _ , sg_cmm_ = sgcmm} = sgcmm