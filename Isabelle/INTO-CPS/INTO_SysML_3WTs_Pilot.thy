
(*  File:      'INTO_SysML_3WTs_Pilot' 
    Description: The INTO-CPS pilot case study of 3 Water tanks 
    Author:     Nuno Amálio
*)

theory INTO_SysML_3WTs_Pilot
imports INTO_SysML_MM_Gbl PDGs
  
begin

(*The ASD corresponding to the ASD of 3WTs*)
definition SG_ASD_3WTsP :: "SGr_ls"
where
  "SG_ASD_3WTsP = \<lparr>NsG=[''3WaterTanksASD'', ''3WaterTanksSys'', ''CompWaterTanksSys1'',
    ''CompWaterTanksSys2'', ''CompWaterTanksSys3'',
    ''WaterTanks1'', ''WaterTanks2'', ''Controller'', 
    ''CompWaterTanks1Inflow'', ''CompWaterTanks1Pipe'', 
    ''CompWaterTanks1TankIO'', ''CompWaterTanks2TankIOV'', 
    ''CompWaterTanks2Drain'',
    ''Inflow'', ''Pipe'', ''TankIO'', ''TankIOV'', ''Drain'', ''FlowRate'', 
    ''WaterLevel'', ''ValveState'',
    ''WaterTanks1_wout'', ''WaterTanks2_win'', ''WaterTanks2_wlout'', 
    ''WaterTanks2_vi'', ''Controller_wlin'', ''Controller_vo'',
    ''Inflow_wout'', ''Pipe_win'', ''Pipe_wout'', ''TankIO_win'', ''TankIO_wout'', 
    ''TankIOV_win'', ''TankIOV_wout'', ''TankIOV_wlout'', ''TankIOV_vi'',
    ''Drain_win''], 
      EsG = [''E_3WaterTanksASD_3WaterTanksSys'', ''E_3WaterTanksASD_WaterTanks1'', 
        ''E_3WaterTanksASD_WaterTanks2'', ''E_3WaterTanksASD_Controller'', 
        ''E_3WaterTanksASD_TankIO'', ''E_3WaterTanksASD_TankIOV'', 
        ''E_3WaterTanksASD_Inflow'', ''E_3WaterTanksASD_Pipe'', 
        ''E_3WaterTanksASD_Drain'',
        ''E_3WaterTanksASD_FlowRate'', 
        ''E_3WaterTanksASD_WaterLevel'', 
        ''E_3WaterTanksASD_ValveState'', 
        ''E_CompWaterTanksSys1_src'', ''E_CompWaterTanksSys1_tgt'',  
        ''E_CompWaterTanksSys2_src'', ''E_CompWaterTanksSys2_tgt'', 
        ''E_CompWaterTanksSys3_src'', ''E_CompWaterTanksSys3_tgt'', 
        ''E_CompWaterTanks1Inflow_src'', ''E_CompWaterTanks1Inflow_tgt'',
        ''E_CompWaterTanks1Pipe_src'', ''E_CompWaterTanks1Pipe_tgt'',
        ''E_CompWaterTanks1TankIO_src'', ''E_CompWaterTanks1TankIO_tgt'', 
        ''E_CompWaterTanks2TankIOV_src'', ''E_CompWaterTanks2TankIOV_tgt'',
        ''E_CompWaterTanks2Drain_src'', ''E_CompWaterTanks2Drain_tgt'',
        ''E_WaterTanks1_wout'', ''E_WaterTanks2_win'', ''E_WaterTanks2_wlout'', 
        ''E_WaterTanks2_vi'', ''E_Controller_wlin'', ''E_Controller_vo'',
        ''E_Inflow_wout'', ''E_Pipe_win'', ''E_Pipe_wout'', ''E_TankIO_win'', 
        ''E_TankIO_wout'', 
        ''E_TankIOV_win'', ''E_TankIOV_wout'', ''E_TankIOV_wlout'', ''E_TankIOV_vi'',
        ''E_Drain_win'', ''E_Dep_Pipe_wout_win'', ''E_Dep_TankIO_wout_win'',
        ''E_Dep_WaterTanks2_wlout_win'', ''E_Dep_TankIOV_wlout_win'',
        ''E_Dep_TankIOV_wout_win'', ''E_Dep_TankIOV_wlout_win'',
        ''E_Dep_TankIOV_wout_vi'', ''E_Dep_Controller_vo_wlin''], 
      srcG =  [(''E_3WaterTanksASD_3WaterTanksSys'', ''3WaterTanksASD''), 
        (''E_3WaterTanksASD_WaterTanks1'', ''3WaterTanksASD''),
        (''E_3WaterTanksASD_WaterTanks2'', ''3WaterTanksASD''),
        (''E_3WaterTanksASD_Controller'', ''3WaterTanksASD''),
        (''E_3WaterTanksASD_TankIO'', ''3WaterTanksASD''),
        (''E_3WaterTanksASD_TankIOV'', ''3WaterTanksASD''),
        (''E_3WaterTanksASD_Inflow'', ''3WaterTanksASD''),
        (''E_3WaterTanksASD_Pipe'',  ''3WaterTanksASD''),
        (''E_3WaterTanksASD_Drain'', ''3WaterTanksASD''),
        (''E_3WaterTanksASD_FlowRate'', ''3WaterTanksASD''),
        (''E_3WaterTanksASD_WaterLevel'', ''3WaterTanksASD''),
        (''E_3WaterTanksASD_ValveState'', ''3WaterTanksASD''),
        (''E_CompWaterTanksSys1_src'', ''CompWaterTanksSys1''), 
        (''E_CompWaterTanksSys1_tgt'', ''CompWaterTanksSys1''),
        (''E_CompWaterTanksSys2_src'', ''CompWaterTanksSys2''), 
        (''E_CompWaterTanksSys2_tgt'', ''CompWaterTanksSys2''),
        (''E_CompWaterTanksSys3_src'', ''CompWaterTanksSys3''), 
        (''E_CompWaterTanksSys3_tgt'', ''CompWaterTanksSys3''),
        (''E_CompWaterTanks1Inflow_src'', ''CompWaterTanks1Inflow''),
        (''E_CompWaterTanks1Inflow_tgt'', ''CompWaterTanks1Inflow''),
        (''E_CompWaterTanks1Pipe_src'', ''CompWaterTanks1Pipe''),
        (''E_CompWaterTanks1Pipe_tgt'', ''CompWaterTanks1Pipe''),
        (''E_CompWaterTanks1TankIO_src'', ''CompWaterTanks1TankIO''), 
        (''E_CompWaterTanks1TankIO_tgt'', ''CompWaterTanks1TankIO''), 
        (''E_CompWaterTanks2TankIOV_src'', ''CompWaterTanks2TankIOV''),
        (''E_CompWaterTanks2TankIOV_tgt'', ''CompWaterTanks2TankIOV''),
        (''E_CompWaterTanks2Drain_src'', ''CompWaterTanks2Drain''),
        (''E_CompWaterTanks2Drain_tgt'', ''CompWaterTanks2Drain''),
        (''E_WaterTanks1_wout'', ''WaterTanks1''),
        (''E_WaterTanks2_win'', ''WaterTanks2''),
        (''E_WaterTanks2_wlout'', ''WaterTanks2''),
        (''E_WaterTanks2_vi'', ''WaterTanks2''),
        (''E_Controller_wlin'', ''Controller''),
        (''E_Controller_vo'', ''Controller''),
        (''E_Inflow_wout'', ''Inflow''), 
        (''E_Pipe_win'', ''Pipe''), (''E_Pipe_wout'', ''Pipe''),
        (''E_TankIO_win'', ''TankIO''), (''E_TankIO_wout'', ''TankIO''),
        (''E_TankIOV_win'', ''TankIOV''), (''E_TankIOV_wout'', ''TankIOV''),
        (''E_TankIOV_wlout'', ''TankIOV''), (''E_TankIOV_vi'', ''TankIOV''),
        (''E_Drain_win'', ''Drain''),
        (''E_Dep_Pipe_wout_win'', ''Pipe_wout''), 
        (''E_Dep_TankIO_wout_win'', ''TankIO_wout''),
        (''E_Dep_WaterTanks2_wlout_win'', ''WaterTanks2_wlout''),
        (''E_Dep_TankIOV_wout_win'', ''TankIOV_wout''), 
        (''E_Dep_TankIOV_wlout_win'', ''TankIOV_wlout''),
        (''E_Dep_TankIOV_wout_vi'', ''TankIOV_wout''),
        (''E_Dep_Controller_vo_wlin'', ''Controller_vo'')], 
      tgtG =  [(''E_3WaterTanksASD_3WaterTanksSys'', ''3WaterTanksSys''), 
        (''E_3WaterTanksASD_WaterTanks1'', ''WaterTanks1''),
        (''E_3WaterTanksASD_WaterTanks2'', ''WaterTanks2''),
        (''E_3WaterTanksASD_Controller'', ''Controller''),
        (''E_3WaterTanksASD_TankIO'', ''TankIO''),
        (''E_3WaterTanksASD_TankIOV'', ''TankIOV''),
        (''E_3WaterTanksASD_Inflow'', ''Inflow''),
        (''E_3WaterTanksASD_Pipe'',  ''Pipe''),
        (''E_3WaterTanksASD_Drain'', ''Drain''),
        (''E_3WaterTanksASD_FlowRate'', ''FlowRate''),
        (''E_3WaterTanksASD_WaterLevel'', ''WaterLevel''),
        (''E_3WaterTanksASD_ValveState'', ''ValveState''),
        (''E_CompWaterTanksSys1_src'', ''3WaterTanksSys''), 
        (''E_CompWaterTanksSys1_tgt'', ''WaterTanks1''),
        (''E_CompWaterTanksSys2_src'', ''3WaterTanksSys''), 
        (''E_CompWaterTanksSys2_tgt'', ''WaterTanks2''),
        (''E_CompWaterTanksSys3_src'', ''3WaterTanksSys''), 
        (''E_CompWaterTanksSys3_tgt'', ''Controller''),
        (''E_CompWaterTanks1Inflow_src'', ''WaterTanks1''),
        (''E_CompWaterTanks1Inflow_tgt'', ''Inflow''),
        (''E_CompWaterTanks1Pipe_src'', ''WaterTanks1''),
        (''E_CompWaterTanks1Pipe_tgt'', ''Pipe''),
        (''E_CompWaterTanks1TankIO_src'', ''WaterTanks1''), 
        (''E_CompWaterTanks1TankIO_tgt'', ''TankIO''), 
        (''E_CompWaterTanks2TankIOV_src'', ''WaterTanks2''),
        (''E_CompWaterTanks2TankIOV_tgt'', ''TankIOV''),
        (''E_CompWaterTanks2Drain_src'', ''WaterTanks2''),
        (''E_CompWaterTanks2Drain_tgt'', ''Drain''),
        (''E_WaterTanks1_wout'', ''WaterTanks1_wout''),
        (''E_WaterTanks2_win'', ''WaterTanks2_win''),
        (''E_WaterTanks2_wlout'', ''WaterTanks2_wlout''),
        (''E_WaterTanks2_vi'', ''WaterTanks2_vi''),
        (''E_Controller_wlin'', ''Controller_wlin''),
        (''E_Controller_vo'', ''Controller_vo''),
        (''E_Inflow_wout'', ''Inflow_wout''), 
        (''E_Pipe_win'', ''Pipe_win''), (''E_Pipe_wout'', ''Pipe_wout''),
        (''E_TankIO_win'', ''TankIO_win''), (''E_TankIO_wout'', ''TankIO_wout''),
        (''E_TankIOV_win'', ''TankIOV_win''), (''E_TankIOV_wout'', ''TankIOV_wout''),
        (''E_TankIOV_wlout'', ''TankIOV_wlout''), (''E_TankIOV_vi'', ''TankIOV_vi''),
        (''E_Drain_win'', ''Drain_win''),
        (''E_Dep_Pipe_wout_win'', ''Pipe_win''), 
        (''E_Dep_TankIO_wout_win'', ''TankIO_win''),
        (''E_Dep_WaterTanks2_wlout_win'', ''WaterTanks2_win''),
        (''E_Dep_TankIOV_wout_win'', ''TankIOV_win''), 
        (''E_Dep_TankIOV_wlout_win'', ''TankIOV_win''),
        (''E_Dep_TankIOV_wout_vi'', ''TankIOV_vi''),
        (''E_Dep_Controller_vo_wlin'', ''Controller_wlin'')],
      ntyG =[(''3WaterTanksASD'', nnrml), 
      (''3WaterTanksSys'',  nnrml), (''CompWaterTanksSys1'',  nnrml),
      (''CompWaterTanksSys2'',  nnrml), (''CompWaterTanksSys3'',  nnrml),
      (''WaterTanks1'',  nnrml), (''WaterTanks2'',  nnrml), 
      (''Controller'',  nnrml), (''CompWaterTanks1Inflow'',  nnrml),
      (''CompWaterTanks1Pipe'',  nnrml), (''CompWaterTanks1TankIO'',  nnrml),
      (''CompWaterTanks2TankIOV'',  nnrml), (''CompWaterTanks2Drain'',  nnrml),
      (''Inflow'',  nnrml), (''Pipe'',  nnrml), (''TankIO'',  nnrml), 
      (''TankIOV'',  nnrml), (''Drain'',  nnrml), (''FlowRate'',  nnrml),
      (''WaterLevel'',  nnrml), (''ValveState'',  nnrml),
      (''WaterTanks1_wout'',  nnrml), (''WaterTanks2_win'',  nnrml), 
      (''WaterTanks2_wlout'',  nnrml), (''WaterTanks2_vi'',  nnrml), 
      (''Controller_wlin'',  nnrml), (''Controller_vo'',  nnrml),
      (''Inflow_wout'',  nnrml), (''Pipe_win'',  nnrml), 
      (''Pipe_wout'',  nnrml), (''TankIO_win'',  nnrml),
      (''TankIO_wout'',  nnrml), (''TankIOV_win'',  nnrml),
      (''TankIOV_wout'',  nnrml), (''TankIOV_wlout'',  nnrml), 
      (''TankIOV_vi'',  nnrml), (''Drain_win'',  nnrml)],
      etyG =[(''E_3WaterTanksASD_3WaterTanksSys'', elnk), 
        (''E_3WaterTanksASD_WaterTanks1'', elnk),
        (''E_3WaterTanksASD_WaterTanks2'', elnk),
        (''E_3WaterTanksASD_Controller'', elnk),
        (''E_3WaterTanksASD_TankIO'', elnk),
        (''E_3WaterTanksASD_TankIOV'', elnk),
        (''E_3WaterTanksASD_Inflow'', elnk),
        (''E_3WaterTanksASD_Pipe'',  elnk),
        (''E_3WaterTanksASD_Drain'', elnk),
        (''E_3WaterTanksASD_FlowRate'', elnk),
        (''E_3WaterTanksASD_WaterLevel'', elnk),
        (''E_3WaterTanksASD_ValveState'', elnk),
        (''E_CompWaterTanksSys1_src'', ecompuni), 
        (''E_CompWaterTanksSys1_tgt'', ecompuni),
        (''E_CompWaterTanksSys2_src'', ecompuni), 
        (''E_CompWaterTanksSys2_tgt'', ecompuni),
        (''E_CompWaterTanksSys3_src'', ecompuni), 
        (''E_CompWaterTanksSys3_tgt'', ecompuni),
        (''E_CompWaterTanks1Inflow_src'', ecompuni),
        (''E_CompWaterTanks1Inflow_tgt'', ecompuni),
        (''E_CompWaterTanks1Pipe_src'', ecompuni),
        (''E_CompWaterTanks1Pipe_tgt'', ecompuni),
        (''E_CompWaterTanks1TankIO_src'', ecompuni), 
        (''E_CompWaterTanks1TankIO_tgt'', ecompuni), 
        (''E_CompWaterTanks2TankIOV_src'', ecompuni),
        (''E_CompWaterTanks2TankIOV_tgt'', ecompuni),
        (''E_CompWaterTanks2Drain_src'', ecompuni),
        (''E_CompWaterTanks2Drain_tgt'', ecompuni),
        (''E_WaterTanks1_wout'', elnk),
        (''E_WaterTanks2_win'', elnk),
        (''E_WaterTanks2_wlout'', elnk),
        (''E_WaterTanks2_vi'', elnk),
        (''E_Controller_wlin'', elnk),
        (''E_Controller_vo'', elnk),
        (''E_Inflow_wout'', elnk), 
        (''E_Pipe_win'', elnk), (''E_Pipe_wout'', elnk),
        (''E_TankIO_win'', elnk), (''E_TankIO_wout'', elnk),
        (''E_TankIOV_win'', elnk), (''E_TankIOV_wout'', elnk),
        (''E_TankIOV_wlout'', elnk), (''E_TankIOV_vi'', elnk),
        (''E_Drain_win'', elnk),
        (''E_Dep_Pipe_wout_win'', elnk), 
        (''E_Dep_TankIO_wout_win'', elnk),
        (''E_Dep_WaterTanks2_wlout_win'', elnk),
        (''E_Dep_TankIOV_wout_win'', elnk), 
        (''E_Dep_TankIOV_wlout_win'', elnk),
        (''E_Dep_TankIOV_wout_vi'', elnk),
        (''E_Dep_Controller_vo_wlin'', elnk)],
      srcmG = [], 
      tgtmG = [(''E_CompWaterTanksSys1_src'', sm (val 1)), 
        (''E_CompWaterTanksSys2_src'', sm (val 1)), 
        (''E_CompWaterTanksSys3_src'', sm (val 1)), 
        (''E_CompWaterTanksSys1_tgt'', sm (val 1)), 
        (''E_CompWaterTanksSys2_tgt'', sm (val 1)), 
        (''E_CompWaterTanksSys3_tgt'', sm (val 1)), 
        (''E_CompWaterTanks1Inflow_src'', sm (val 1)),
        (''E_CompWaterTanks1Inflow_tgt'', sm (val 1)),
        (''E_CompWaterTanks1Pipe_src'', sm (val 1)),
        (''E_CompWaterTanks1Pipe_tgt'', sm (val 1)),
        (''E_CompWaterTanks1TankIO_src'', sm (val 1)), 
        (''E_CompWaterTanks1TankIO_tgt'', sm (val 2)), 
        (''E_CompWaterTanks2TankIOV_src'', sm (val 1)),
        (''E_CompWaterTanks2TankIOV_tgt'', sm (val 1)),
        (''E_CompWaterTanks2Drain_src'', sm (val 1)),
        (''E_CompWaterTanks2Drain_tgt'', sm (val 1))]\<rparr>"

axiomatization
where
  Es_SG_ASD_3WTsP: "Es (toSGr SG_ASD_3WTsP) \<subseteq> E_A"
  and Ns_SG_ASD_3WTsP: "Ns (toSGr SG_ASD_3WTsP) \<subseteq> V_A"

value "consInh SG_ASD_3WTsP"

lemma wf_SG_ASD_3WTsP: "is_wf_sg (toSGr SG_ASD_3WTsP)"
  proof -
    have h_wf_g: "is_wf_g (toSGr SG_ASD_3WTsP)"
      proof (simp add: is_wf_g_def, rule conjI)
        show "Ns (toSGr SG_ASD_3WTsP) \<subseteq> V_A"
          using Ns_SG_ASD_3WTsP by simp
      next
        apply_end(rule conjI)
        show "Es (toSGr SG_ASD_3WTsP) \<subseteq> E_A"
          using Es_SG_ASD_3WTsP by simp
      next
        apply_end(rule conjI)
        show "ftotal_on (src (toSGr SG_ASD_3WTsP)) (Es (toSGr SG_ASD_3WTsP)) (Ns (toSGr SG_ASD_3WTsP))"
          by (auto simp add: ftotal_on_def toSGr_def SG_ASD_3WTsP_def)
      next
        show "ftotal_on (tgt (toSGr SG_ASD_3WTsP)) (Es (toSGr SG_ASD_3WTsP)) (Ns (toSGr SG_ASD_3WTsP))"
          by (auto simp add: ftotal_on_def toSGr_def SG_ASD_3WTsP_def)
      qed
    show ?thesis
    proof (simp add: is_wf_sg_def, rule conjI)
      show "is_wf_g (toSGr SG_ASD_3WTsP)"
        using h_wf_g by simp
    next
      apply_end(rule conjI)
      show "ftotal_on (nty (toSGr SG_ASD_3WTsP)) (Ns (toSGr SG_ASD_3WTsP)) SGNTy_set"
        by (auto simp add: ftotal_on_def SGNTy_set_def SG_ASD_3WTsP_def toSGr_def)
    next
      apply_end(rule conjI) 
      show "ftotal_on (ety (toSGr SG_ASD_3WTsP)) (Es (toSGr SG_ASD_3WTsP)) SGETy_set"
        by (auto simp add: ftotal_on_def SGNTy_set_def SG_ASD_3WTsP_def toSGr_def SGETy_set_def)
    next
      apply_end(rule conjI) 
      show "dom (srcm (toSGr SG_ASD_3WTsP)) = EsTy (toSGr SG_ASD_3WTsP) {Some erelbi, Some ecompbi}"
        by (simp add: SG_ASD_3WTsP_def toSGr_def EsTy_def vimage_def)
    next
      apply_end(rule conjI) 
      show "dom (tgtm (toSGr SG_ASD_3WTsP)) = EsTy (toSGr SG_ASD_3WTsP) {Some erelbi, Some ereluni, Some ecompbi, Some ecompuni}"
        by (rule equalityI, 
          simp add: SG_ASD_3WTsP_def toSGr_def EsTy_def vimage_def, rule subsetI,
          simp add: SG_ASD_3WTsP_def toSGr_def EsTy_def vimage_def split: if_splits)
    next
      apply_end(rule conjI)
      show "EsR (toSGr SG_ASD_3WTsP) \<subseteq> EsId (toSGr SG_ASD_3WTsP)"
        by (simp add: EsR_def toSGr_def EsTy_def vimage_def SG_ASD_3WTsP_def)
    next
      apply_end(rule conjI)
      show "srcm (toSGr SG_ASD_3WTsP) ` EsTy (toSGr SG_ASD_3WTsP) {Some ecompbi}
        \<subseteq> {Some (rm 0 (val (Suc 0))), Some (sm (val (Suc 0)))}"
        by (simp add: toSGr_def image_def SG_ASD_3WTsP_def EsTy_def)
    next
      show "acyclicGr (inhG (toSGr SG_ASD_3WTsP))"
        using h_wf_g by (simp add: inh_eq acyclicGr_def rtrancl_in inh_eq_consInh)(eval)
    qed
  qed

(*'F_CD' Fragment*)
definition F_ASD_3WTsP :: "Fr_ls"
where
   "F_ASD_3WTsP \<equiv> \<lparr>sg_ls = SG_ASD_3WTsP, 
    tr_ls = []\<rparr>"

value "consRefs F_ASD_3WTsP"

(* Well-formedness proof obligation of fragments"*)
lemma wf_F_ASD_3WTsP: "is_wf_fr (toFr F_ASD_3WTsP)"
  proof -
    let ?refs_F_ASD_3WTsP = "{}"
    have h_ftotal_tr: "ftotal_on (tr (toFr F_ASD_3WTsP)) (EsRP (sg (toFr F_ASD_3WTsP))) V_A"
      proof (simp add: ftotal_on_def)
        apply_end(rule conjI)
        show "dom (tr (toFr F_ASD_3WTsP)) = EsRP (sg (toFr F_ASD_3WTsP))"
        proof
          show "dom (tr (toFr F_ASD_3WTsP)) \<subseteq> EsRP (sg (toFr F_ASD_3WTsP))"
            by (simp add: F_ASD_3WTsP_def SG_ASD_3WTsP_def toSGr_def toFr_def  
          SG_F_Props_def EsRP_def EsR_def NsP_def EsTy_def NsTy_def) 
        next
          show "EsRP (sg (toFr F_ASD_3WTsP)) \<subseteq> dom (tr (toFr F_ASD_3WTsP))"
            by (auto simp add: F_ASD_3WTsP_def SG_ASD_3WTsP_def toSGr_def toFr_def SG_F_Common_def 
              SG_F_Props_def EsRP_def EsR_def NsP_def EsTy_def NsTy_def)
        qed
      next
        show "ran (tr (toFr F_ASD_3WTsP)) \<subseteq> V_A"
        using Ns_SG_F_ASD Ns_SG_F_Comps Ns_SG_F_Blocks Ns_SG_F_Common Ns_SG_F_VTypes
        by (simp add: F_ASD_3WTsP_def SG_ASD_3WTsP_def toSGr_def toFr_def SG_F_Comps_def 
          SG_F_Blocks_def F_Common_def SG_F_Common_def F_VTypes_def SG_F_VTypes_def)
      qed
      from wf_SG_ASD_3WTsP have hb: "is_wf_sg (sg (toFr F_ASD_3WTsP))"
      by (simp add: toFr_def F_ASD_3WTsP_def)
    have refs_F_ASD_3WTsP: "refs (toFr F_ASD_3WTsP) = ?refs_F_ASD_3WTsP"
      using h_ftotal_tr hb by (simp add: refs_eq_consRefs, eval)
    show ?thesis
    proof (simp add: is_wf_fr_def)
      apply_end(rule conjI)
      show "is_wf_sg (sg (toFr F_ASD_3WTsP))"  
        by (simp add: wf_SG_ASD_3WTsP toFr_def F_ASD_3WTsP_def)
    next
      apply_end(rule conjI) 
      show "ftotal_on (tr (toFr F_ASD_3WTsP)) (EsRP (sg (toFr F_ASD_3WTsP))) V_A"
        by (simp add: h_ftotal_tr)
    next
      apply_end(rule conjI)  
      show "inj_on (src (sg (toFr F_ASD_3WTsP))) (EsRP (sg (toFr F_ASD_3WTsP)))"
        by (simp add: F_ASD_3WTsP_def inj_on_def EsRP_def EsR_def NsP_def EsTy_def NsTy_def 
          SG_ASD_3WTsP_def toFr_def toSGr_def) 
    next
      apply_end(rule conjI)  
      show "ran (src (sg (toFr F_ASD_3WTsP)) |` EsRP (sg (toFr F_ASD_3WTsP))) = NsP (sg (toFr F_ASD_3WTsP))"
        by (simp add: F_ASD_3WTsP_def restrict_map_def NsP_def NsTy_def EsRP_def 
          toFr_def SG_ASD_3WTsP_def EsR_def EsTy_def toSGr_def vimage_def)
    next
      apply_end(rule conjI)
      show "\<forall>v. v \<in> NsP (sg (toFr F_ASD_3WTsP)) \<longrightarrow> nonPRefsOf (toFr F_ASD_3WTsP) v \<noteq> {}"
        by (simp add: NsP_def NsTy_def nonPRefsOf_def refsOf_def refs_F_ASD_3WTsP)
          (simp add: F_ASD_3WTsP_def SG_ASD_3WTsP_def toFr_def toSGr_def)
    next
      apply_end(rule conjI)
      have h_wf_g: "is_wf_g (toSGr SG_ASD_3WTsP)"
        using wf_SG_ASD_3WTsP
        by (simp add: is_wf_sg_def)
      show "acyclic_fr (toFr F_ASD_3WTsP)"
        using  h_wf_g by (simp add: acyclic_fr_def refs_F_ASD_3WTsP)
          (simp add: inh_eq rtrancl_in inh_eq_consInh F_ASD_3WTsP_def toFr_def, eval)
    next
      show "proxies_dont_inherit (toFr F_ASD_3WTsP)"
        by (simp add: proxies_dont_inherit_def restrict_map_def NsP_def NsTy_def
          F_ASD_3WTsP_def toFr_def vimage_def SG_ASD_3WTsP_def toSGr_def)
    qed
  qed

definition SG_CD_3WTsP :: "SGr_ls"
where
  "SG_CD_3WTsP = \<lparr>
    NsG=[''PrTankIO'', ''PrTankIOV'', ''PrInflow'', ''PrPipe'', ''PrDrain'', 
      ''PrWaterTanks1'', 
      ''PrWaterTanks2'', ''PrController'', ''CD_3WTs'', ''WTSys'',
      ''I'', ''P'', ''T1'', ''T2'', ''T3'',  ''C'', ''D'', ''WT1'', ''WT2'',
      ''iout'', ''t1in'', ''t1out'', ''pin'', ''pout'', ''t2in'', ''t2out'', 
      ''wout'', ''win'', ''wlout'', ''vi1'', ''t3in'', ''t3wlout'', ''t3out'', ''vi2'',   
      ''din'', ''din'', ''wlin'', ''vo'',
      ''C_iout_t1in'', ''C_t1out_pin'', ''C_pout_t2in2'', ''C_t2out_wout'',
      ''C_wout_win'', ''C_win_t3in'', ''C_t3lout_wlout'', ''C_t3out_din'',
      ''C_wlout_wlin'', ''C_vo_vi1'', ''C_vi1_vi2'',
      ''PrInflow_wout'', ''PrTankIO_win'', ''PrTankIO_wout'', ''PrPipe_win'',
      ''PrPipe_wout'', ''PrWaterTanks1_wout'', ''PrWaterTanks2_win'', 
      ''PrWaterTanks2_wlout'', ''PrWaterTanks2_vi'',
      ''PrController_wlin'', ''PrController_vo'', ''PrDrain_win'', 
      ''PrTankIOV_win'', ''PrTankIOV_wout'', ''PrTankIOV_wlout'', 
      ''PrTankIOV_vi''], 
    EsG = [''ECD_WTSys'', ''ECD_I'', ''ECD_P'', ''ECD_T1'', ''ECD_T2'', 
      ''ECD_T3'', ''ECD_C'', ''ECD_D'', ''ECD_WT1'', ''ECD_WT2'', 
      ''ECD_C_iout_t1in'', ''ECD_C_t1out_pin'', ''ECD_C_pout_t2in2'', ''ECD_C_t2out_wout'',
      ''ECD_C_wout_win'', ''ECD_C_win_t3in'', ''ECD_C_t3lout_wlout'', ''ECD_C_t3out_din'',
      ''ECD_C_wlout_wlin'', ''ECD_C_vo_vi1'', ''ECD_C_vi1_vi2'',
      ''E_WTSys_WT1'', ''E_WTSys_WT2'', ''E_WTSys_C'',
      ''E_WT1_I'', ''E_WT1_P'', ''E_WT1_T1'', ''E_WT1_T2'', 
      ''E_WT2_T3'', ''E_WT2_D'', 
      ''E_I_iout'', ''E_P_pin'', ''E_P_pout'', ''E_T1_t1in'', ''E_T1_t1out'', 
      ''E_T2_t2in'', ''E_T2_t2out'', 
      ''E_T3_t3in'', ''E_T3_t3wlout'', ''E_T3_vi2'', 
      ''E_C_wlin'', ''E_C_vo'', ''E_D_din'', ''E_WT1_wout'', ''E_WT2_win'', 
      ''E_WT2_wlout'', ''E_WT2_vi1'',
      ''E_C_iout_t1in_src'', ''E_C_iout_t1in_tgt'', 
      ''E_C_t1out_pin_src'', ''E_C_t1out_pin_tgt'', 
      ''E_C_pout_t2in2_src'', ''E_C_pout_t2in2_tgt'',
      ''E_C_t2out_wout_src'', ''E_C_t2out_wout_tgt'',
      ''E_C_wout_win_src'', ''E_C_wout_win_tgt'', 
      ''E_C_win_t3in_src'', ''E_C_win_t3in_tgt'', 
      ''E_C_t3lout_wlout_src'', ''E_C_t3lout_wlout_tgt'', 
      ''E_C_t3out_din_src'', ''E_C_t3out_din_tgt'',
      ''E_C_wlout_wlin_src'', ''E_C_wlout_wlin_tgt'', 
      ''E_C_vo_vi1_src'', ''E_C_vo_vi1_tgt'', 
      ''E_C_vi1_vi2_src'', ''E_C_vi1_vi2_tgt'',
      ''E_iout_ty'', ''E_t1in_ty'', ''E_t1out_ty'', ''E_pin_ty'', ''E_pout_ty'', ''E_t2in_ty'', 
      ''E_t2out_ty'', ''E_wout_ty'', ''E_win_ty'', ''E_wlout_ty'', ''E_vi1_ty'', 
      ''E_t3in_ty'', ''E_t3wlout_ty'', ''E_t3out_ty'', ''E_vi2_ty'',   
      ''E_din_ty'', ''E_wlin_ty'', ''E_vo_ty'',
      ''ERPrTankIO'', ''ERPrTankIOV'', ''ERPrInflow'', ''ERPrPipe'', ''ERPrDrain'', 
      ''ERPrWaterTanks1'', ''ERPrWaterTanks2'', ''ERPrController'',
      ''ERPrInflow_wout'', ''ERPrTankIO_win'', ''ERPrTankIO_wout'', ''ERPrPipe_win'',
      ''ERPrPipe_wout'', ''ERPrWaterTanks1_wout'', ''ERPrWaterTanks2_win'', 
      ''ERPrWaterTanks2_wlout'', ''ERPrWaterTanks2_vi'',
      ''ERPrController_wlin'', ''ERPrController_vo'', ''ERPrDrain_win'', 
      ''ERPrTankIOV_win'', ''ERPrTankIOV_wout'', ''ERPrTankIOV_wlout'', 
      ''ERPrTankIOV_vi''], 
    srcG =  [
      (''ECD_WTSys'', ''CD_3WTs''), (''ECD_I'', ''CD_3WTs''), 
      (''ECD_P'', ''CD_3WTs''), (''ECD_T1'', ''CD_3WTs''), 
      (''ECD_T2'', ''CD_3WTs''), (''ECD_T3'', ''CD_3WTs''), 
      (''ECD_C'', ''CD_3WTs''), (''ECD_D'', ''CD_3WTs''),
      (''ECD_WT1'', ''CD_3WTs''), (''ECD_WT2'', ''CD_3WTs''),
      (''ECD_C_iout_t1in'', ''CD_3WTs''), (''ECD_C_t1out_pin'', ''CD_3WTs''), 
      (''ECD_C_pout_t2in2'', ''CD_3WTs''), (''ECD_C_t2out_wout'', ''CD_3WTs''),
      (''ECD_C_wout_win'', ''CD_3WTs''), (''ECD_C_win_t3in'', ''CD_3WTs''),
      (''ECD_C_t3lout_wlout'', ''CD_3WTs''), (''ECD_C_t3out_din'', ''CD_3WTs''),
      (''ECD_C_wlout_wlin'', ''CD_3WTs''), (''ECD_C_vo_vi1'', ''CD_3WTs''), 
      (''ECD_C_vi1_vi2'', ''CD_3WTs''),
      (''E_WTSys_WT1'', ''WTSys''), (''E_WTSys_WT2'', ''WTSys''), 
      (''E_WTSys_C'', ''WTSys''), (''E_WT1_I'', ''WT1''),
      (''E_WT1_P'', ''WT1''), (''E_WT1_T1'', ''WT1''), (''E_WT1_T2'', ''WT1''),
      (''E_WT2_T3'', ''WT2''), (''E_WT2_D'', ''WT2''),
      (''E_I_iout'', ''I''), (''E_P_pin'', ''P''), 
      (''E_P_pout'', ''P''), (''E_T1_t1in'', ''T1''), 
      (''E_T1_t1out'', ''T1''), (''E_T2_t2in'', ''T2''),
      (''E_T2_t2out'', ''T2''), (''E_T3_t3in'', ''T3''), 
      (''E_T3_t3wlout'', ''T3''), (''E_T3_vi2'', ''T3''),
      (''E_C_wlin'', ''C''), (''E_C_vo'', ''C''), (''E_D_din'', ''D''),
      (''E_WT1_wout'', ''WT1''), (''E_WT2_win'', ''WT2''),
      (''E_WT2_wlout'', ''WT2''), (''E_WT2_vi1'', ''WT2''),
      (''E_C_iout_t1in_src'', ''C_iout_t1in''), 
      (''E_C_iout_t1in_tgt'', ''C_iout_t1in''),
      (''E_C_t1out_pin_src'', ''C_t1out_pin''), 
      (''E_C_t1out_pin_tgt'', ''C_t1out_pin''),
      (''E_C_pout_t2in2_src'', ''C_pout_t2in2''), 
      (''E_C_pout_t2in2_tgt'', ''C_pout_t2in2''),
      (''E_C_t2out_wout_src'', ''C_t2out_wout''), 
      (''E_C_t2out_wout_tgt'', ''C_t2out_wout''),
      (''E_C_wout_win_src'', ''C_wout_win''), 
      (''E_C_wout_win_tgt'', ''C_wout_win''), 
      (''E_C_win_t3in_src'', ''C_win_t3in''),
      (''E_C_win_t3in_tgt'', ''C_win_t3in''),
      (''E_C_t3lout_wlout_src'', ''C_t3lout_wlout''), 
      (''E_C_t3lout_wlout_tgt'', ''C_t3lout_wlout''),
      (''E_C_t3out_din_src'', ''C_t3out_din''),
      (''E_C_t3out_din_tgt'', ''C_t3out_din''),
      (''E_C_wlout_wlin_src'', ''C_wlout_wlin''),
      (''E_C_wlout_wlin_tgt'', ''C_wlout_wlin''),
      (''E_C_vo_vi1_src'', ''C_vo_vi1''),
      (''E_C_vo_vi1_tgt'', ''C_vo_vi1''),
      (''E_C_vi1_vi2_src'', ''C_vi1_vi2''), 
      (''E_C_vi1_vi2_tgt'', ''C_vi1_vi2''), 
      (''E_iout_ty'', ''iout''), (''E_t1in_ty'', ''t1in''), 
      (''E_t1out_ty'', ''t1out''), (''E_pin_ty'', ''pin''), 
      (''E_pout_ty'', ''pout''), (''E_t2in_ty'', ''t2in''),
      (''E_t2out_ty'', ''t2out''), (''E_wout_ty'', ''wout''),
      (''E_win_ty'', ''win''), (''E_wlout_ty'', ''wlout''),
      (''E_vi1_ty'', ''vi1''), (''E_t3in_ty'', ''t3in''), 
      (''E_t3wlout_ty'', ''t3wlout''), (''E_t3out_ty'', ''t3out''),
      (''E_vi2_ty'', ''vi2''), (''E_din_ty'', ''din''), 
      (''E_wlin_ty'', ''wlin''), (''E_vo_ty'', ''vo''),
      (''ERPrTankIO'', ''PrTankIO''), 
      (''ERPrTankIOV'', ''PrTankIOV''), (''ERPrInflow'', ''PrInflow''),
      (''ERPrPipe'', ''PrPipe''), (''ERPrDrain'', ''PrDrain''),
      (''ERPrWaterTanks1'', ''PrWaterTanks1''), (''ERPrWaterTanks2'', ''PrWaterTanks2''),
      (''ERPrController'', ''PrController''), 
      (''ERPrInflow_wout'', ''PrInflow_wout''), 
      (''ERPrTankIO_win'', ''PrTankIO_win''), (''ERPrTankIO_wout'', ''PrTankIO_wout''), 
      (''ERPrPipe_win'', ''PrPipe_win''), 
      (''ERPrPipe_wout'', ''PrPipe_wout''), 
      (''ERPrWaterTanks1_wout'', ''PrWaterTanks1_wout''), 
      (''ERPrWaterTanks2_win'', ''PrWaterTanks2_win''),
      (''ERPrWaterTanks2_wlout'', ''PrWaterTanks2_wlout''), 
      (''ERPrWaterTanks2_vi'', ''PrWaterTanks2_vi''),
      (''ERPrController_wlin'', ''PrController_wlin''),
      (''ERPrController_vo'', ''PrController_vo''),
      (''ERPrDrain_win'', ''PrDrain_win''), 
      (''ERPrTankIOV_win'', ''PrTankIOV_win''), 
      (''ERPrTankIOV_wout'', ''PrTankIOV_wout''), 
      (''ERPrTankIOV_wlout'', ''PrTankIOV_wlout''),
      (''ERPrTankIOV_vi'', ''PrTankIOV_vi'')],
    tgtG =  [
      (''ECD_WTSys'', ''WTSys''), (''ECD_I'', ''I''), 
      (''ECD_P'', ''P''), (''ECD_T1'', ''T1''), 
      (''ECD_T2'', ''T2''), (''ECD_T3'', ''T3''), 
      (''ECD_C'', ''C''), (''ECD_D'', ''D''),
      (''ECD_WT1'', ''WT1''), (''ECD_WT2'', ''WT2''),
      (''ECD_C_iout_t1in'', ''C_iout_t1in''), 
      (''ECD_C_t1out_pin'', ''C_t1out_pin''), 
      (''ECD_C_pout_t2in2'', ''C_pout_t2in2''), 
      (''ECD_C_t2out_wout'', ''C_t2out_wout''),
      (''ECD_C_wout_win'', ''C_wout_win''), (''ECD_C_win_t3in'', ''C_win_t3in''),
      (''ECD_C_t3lout_wlout'', ''C_t3lout_wlout''), (''ECD_C_t3out_din'', ''C_t3out_din''),
      (''ECD_C_wlout_wlin'', ''C_wlout_wlin''), (''ECD_C_vo_vi1'', ''C_vo_vi1''), 
      (''ECD_C_vi1_vi2'', ''C_vi1_vi2''),
      (''E_WTSys_WT1'', ''WT1''), (''E_WTSys_WT2'', ''WT2''), 
      (''E_WTSys_C'', ''C''), (''E_WT1_I'', ''I''),
      (''E_WT1_P'', ''P''), (''E_WT1_T1'', ''T1''), (''E_WT1_T2'', ''T2''),
      (''E_WT2_T3'', ''T3''), (''E_WT2_D'', ''D''),
      (''E_I_iout'', ''iout''), (''E_P_pin'', ''pin''), 
      (''E_P_pout'', ''pout''), (''E_T1_t1in'', ''t1in''), 
      (''E_T1_t1out'', ''t1out''), (''E_T2_t2in'', ''t2in''),
      (''E_T2_t2out'', ''t2out''), (''E_T3_t3in'', ''t3in''), 
      (''E_T3_t3wlout'', ''t3wlout''), (''E_T3_vi2'', ''vi2''),
      (''E_C_wlin'', ''wlin''), (''E_C_vo'', ''vo''), (''E_D_din'', ''din''),
      (''E_WT1_wout'', ''wout''), (''E_WT2_win'', ''win''),
      (''E_WT2_wlout'', ''wlout''), (''E_WT2_vi1'', ''vi1''),
      (''E_C_iout_t1in_src'', ''iout''), 
      (''E_C_iout_t1in_tgt'', ''t1in''),
      (''E_C_t1out_pin_src'', ''t1out''), 
      (''E_C_t1out_pin_tgt'', ''pin''),
      (''E_C_pout_t2in2_src'', ''pout''), 
      (''E_C_pout_t2in2_tgt'', ''t2in2''),
      (''E_C_t2out_wout_src'', ''t2out''), 
      (''E_C_t2out_wout_tgt'', ''wout''),
      (''E_C_wout_win_src'', ''wout''), 
      (''E_C_wout_win_tgt'', ''win''), 
      (''E_C_win_t3in_src'', ''win''),
      (''E_C_win_t3in_tgt'', ''t3in''),
      (''E_C_t3lout_wlout_src'', ''t3lout''), 
      (''E_C_t3lout_wlout_tgt'', ''wlout''),
      (''E_C_t3out_din_src'', ''t3out''),
      (''E_C_t3out_din_tgt'', ''din''),
      (''E_C_wlout_wlin_src'', ''wlout''),
      (''E_C_wlout_wlin_tgt'', ''wlin''),
      (''E_C_vo_vi1_src'', ''vo''),
      (''E_C_vo_vi1_tgt'', ''vi1''),
      (''E_C_vi1_vi2_src'', ''vi1''), 
      (''E_C_vi1_vi2_tgt'', ''vi2''), 
      (''E_iout_ty'', ''PrInflow_wout''), 
      (''E_t1in_ty'', ''PrTankIO_win''), 
      (''E_t1out_ty'', ''PrTankIO_wout''), 
      (''E_pin_ty'', ''PrPipe_win''), 
      (''E_pout_ty'', ''PrPipe_wout''), 
      (''E_t2in_ty'', ''PrTankIO_win''),
      (''E_t2out_ty'', ''PrTankIO_wout''), 
      (''E_wout_ty'', ''PrWaterTanks1_wout''),
      (''E_win_ty'', ''PrWaterTanks2_win''), 
      (''E_wlout_ty'', ''PrWaterTanks2_wlout''),
      (''E_vi1_ty'', ''PrWaterTanks2_vi''), 
      (''E_t3in_ty'', ''PrTankIOV_win''), 
      (''E_t3wlout_ty'', ''PrTankIOV_wlout''), (''E_t3out_ty'', ''PrTankIOV_wout''),
      (''E_vi2_ty'', ''PrTankIOV_vi''), (''E_din_ty'', ''PrDrain_win''), 
      (''E_wlin_ty'', ''PrController_wlin''), (''E_vo_ty'', ''PrController_vo''),
      (''ERPrTankIO'', ''PrTankIO''), 
      (''ERPrTankIOV'', ''PrTankIOV''), (''ERPrInflow'', ''PrInflow''),
      (''ERPrPipe'', ''PrPipe''), (''ERPrDrain'', ''PrDrain''),
      (''ERPrWaterTanks1'', ''PrWaterTanks1''), (''ERPrWaterTanks2'', ''PrWaterTanks2''),
      (''ERPrController'', ''PrController''), 
      (''ERPrInflow_wout'', ''PrInflow_wout''), 
      (''ERPrTankIO_win'', ''PrTankIO_win''), (''ERPrTankIO_wout'', ''PrTankIO_wout''), 
      (''ERPrPipe_win'', ''PrPipe_win''), 
      (''ERPrPipe_wout'', ''PrPipe_wout''), 
      (''ERPrWaterTanks1_wout'', ''PrWaterTanks1_wout''), 
      (''ERPrWaterTanks2_win'', ''PrWaterTanks2_win''),
      (''ERPrWaterTanks2_wlout'', ''PrWaterTanks2_wlout''), 
      (''ERPrWaterTanks2_vi'', ''PrWaterTanks2_vi''),
      (''ERPrController_wlin'', ''PrController_wlin''),
      (''ERPrController_vo'', ''PrController_vo''),
      (''ERPrDrain_win'', ''PrDrain_win''), 
      (''ERPrTankIOV_win'', ''PrTankIOV_win''), 
      (''ERPrTankIOV_wout'', ''PrTankIOV_wout''), 
      (''ERPrTankIOV_wlout'', ''PrTankIOV_wlout''),
      (''ERPrTankIOV_vi'', ''PrTankIOV_vi'')],
   ntyG =[(''PrTankIO'', nprxy), (''PrTankIOV'', nprxy), (''PrInflow'', nprxy), 
    (''PrPipe'', nprxy), (''PrDrain'', nprxy),
    (''PrWaterTanks1'', nprxy), (''PrWaterTanks2'', nprxy), 
    (''PrController'', nprxy), (''CD_3WTs'', nnrml), (''WTSys'', nnrml),
    (''I'', nnrml), (''P'', nnrml), (''T1'', nnrml), (''T2'', nnrml), (''T3'', nnrml),
    (''C'', nnrml), (''D'', nnrml), (''WT1'', nnrml), (''WT2'', nnrml),
    (''iout'', nnrml), (''t1in'', nnrml), (''t1out'', nnrml), (''pin'', nnrml), 
    (''pout'', nnrml), (''t2in'', nnrml), (''t2out'', nnrml),
    (''wout'', nnrml), (''win'', nnrml), (''wlout'', nnrml), (''vi1'', nnrml),
    (''t3in'', nnrml), (''t3wlout'', nnrml), (''t3out'', nnrml), (''vi2'', nnrml), 
    (''din'', nnrml), (''din'', nnrml), (''wlin'', nnrml), (''vo'', nnrml),
    (''C_iout_t1in'', nnrml), (''C_t1out_pin'', nnrml), (''C_pout_t2in2'', nnrml),
    (''C_t2out_wout'', nnrml), (''C_wout_win'', nnrml), (''C_win_t3in'', nnrml), 
    (''C_t3lout_wlout'', nnrml), (''C_t3out_din'', nnrml),
    (''C_wlout_wlin'', nnrml), (''C_vo_vi1'', nnrml), (''C_vi1_vi2'', nnrml),
    (''PrInflow_wout'', nprxy), (''PrTankIO_win'', nprxy), (''PrTankIO_wout'', nprxy), 
    (''PrPipe_win'', nprxy), (''PrPipe_wout'', nprxy), (''PrWaterTanks1_wout'', nprxy), 
    (''PrWaterTanks2_win'', nprxy), (''PrWaterTanks2_wlout'', nprxy), 
    (''PrWaterTanks2_vi'', nprxy), (''PrController_wlin'', nprxy), 
    (''PrController_vo'', nprxy), (''PrDrain_win'', nprxy),
    (''PrTankIOV_win'', nprxy), (''PrTankIOV_wout'', nprxy), (''PrTankIOV_wlout'', nprxy),
    (''PrTankIOV_vi'', nprxy)],
      etyG =[
        (''ECD_WTSys'', elnk), (''ECD_I'', elnk), 
      (''ECD_P'', elnk), (''ECD_T1'', elnk), 
      (''ECD_T2'', elnk), (''ECD_T3'', elnk), 
      (''ECD_C'', elnk), (''ECD_D'', elnk),
      (''ECD_WT1'', elnk), (''ECD_WT2'', elnk),
      (''ECD_C_iout_t1in'', elnk), 
      (''ECD_C_t1out_pin'', elnk), 
      (''ECD_C_pout_t2in2'', elnk), 
      (''ECD_C_t2out_wout'', elnk),
      (''ECD_C_wout_win'', elnk), (''ECD_C_win_t3in'', elnk),
      (''ECD_C_t3lout_wlout'', elnk), (''ECD_C_t3out_din'', elnk),
      (''ECD_C_wlout_wlin'', elnk), (''ECD_C_vo_vi1'', elnk), 
      (''ECD_C_vi1_vi2'', elnk),
      (''E_WTSys_WT1'', elnk), (''E_WTSys_WT2'', elnk), 
      (''E_WTSys_C'', elnk), (''E_WT1_I'', elnk),
      (''E_WT1_P'', elnk), (''E_WT1_T1'', elnk), (''E_WT1_T2'', elnk),
      (''E_WT2_T3'', elnk), (''E_WT2_D'', elnk),
      (''E_I_iout'', elnk), (''E_P_pin'', elnk), 
      (''E_P_pout'', elnk), (''E_T1_t1in'', elnk), 
      (''E_T1_t1out'', elnk), (''E_T2_t2in'', elnk),
      (''E_T2_t2out'', elnk), (''E_T3_t3in'', elnk), 
      (''E_T3_t3wlout'', elnk), (''E_T3_vi2'', elnk),
      (''E_C_wlin'', elnk), (''E_C_vo'', elnk), (''E_D_din'', elnk),
      (''E_WT1_wout'', elnk), (''E_WT2_win'', elnk),
      (''E_WT2_wlout'', elnk), (''E_WT2_vi1'', elnk),
      (''E_C_iout_t1in_src'', elnk), 
      (''E_C_iout_t1in_tgt'', elnk),
      (''E_C_t1out_pin_src'', elnk), 
      (''E_C_t1out_pin_tgt'', elnk),
      (''E_C_pout_t2in2_src'', elnk), 
      (''E_C_pout_t2in2_tgt'', elnk),
      (''E_C_t2out_wout_src'', elnk), 
      (''E_C_t2out_wout_tgt'', elnk),
      (''E_C_wout_win_src'', elnk), 
      (''E_C_wout_win_tgt'', elnk), 
      (''E_C_win_t3in_src'', elnk),
      (''E_C_win_t3in_tgt'', elnk),
      (''E_C_t3lout_wlout_src'', elnk), 
      (''E_C_t3lout_wlout_tgt'', elnk),
      (''E_C_t3out_din_src'', elnk),
      (''E_C_t3out_din_tgt'', elnk),
      (''E_C_wlout_wlin_src'', elnk),
      (''E_C_wlout_wlin_tgt'', elnk),
      (''E_C_vo_vi1_src'', elnk),
      (''E_C_vo_vi1_tgt'', elnk),
      (''E_C_vi1_vi2_src'', elnk), 
      (''E_C_vi1_vi2_tgt'', elnk), 
      (''E_iout_ty'', elnk), 
      (''E_t1in_ty'', elnk), 
      (''E_t1out_ty'', elnk), 
      (''E_pin_ty'', elnk), 
      (''E_pout_ty'', elnk), 
      (''E_t2in_ty'', elnk),
      (''E_t2out_ty'', elnk), 
      (''E_wout_ty'', elnk),
      (''E_win_ty'', elnk), 
      (''E_wlout_ty'', elnk),
      (''E_vi1_ty'', elnk), 
      (''E_t3in_ty'', elnk), 
      (''E_t3wlout_ty'', elnk), (''E_t3out_ty'', elnk),
      (''E_vi2_ty'', elnk), (''E_din_ty'', elnk), 
      (''E_wlin_ty'', elnk), (''E_vo_ty'', elnk),
      (''ERPrTankIO'', eref), 
      (''ERPrTankIOV'', eref), (''ERPrInflow'', eref),
      (''ERPrPipe'', eref), (''ERPrDrain'', eref),
      (''ERPrWaterTanks1'', eref), (''ERPrWaterTanks2'', eref),
      (''ERPrController'', eref), 
      (''ERPrInflow_wout'', eref), 
      (''ERPrTankIO_win'', eref), (''ERPrTankIO_wout'', eref), 
      (''ERPrPipe_win'', eref), 
      (''ERPrPipe_wout'', eref), 
      (''ERPrWaterTanks1_wout'', eref), 
      (''ERPrWaterTanks2_win'', eref),
      (''ERPrWaterTanks2_wlout'', eref), 
      (''ERPrWaterTanks2_vi'', eref),
      (''ERPrController_wlin'', eref),
      (''ERPrController_vo'', eref),
      (''ERPrDrain_win'', eref), 
      (''ERPrTankIOV_win'', eref), 
      (''ERPrTankIOV_wout'', eref), 
      (''ERPrTankIOV_wlout'', eref),
      (''ERPrTankIOV_vi'', eref)],
      srcmG = [], 
      tgtmG = []\<rparr>"

axiomatization
where
  Es_SG_CD_3WTs: "Es (toSGr SG_CD_3WTsP) \<subseteq> E_A"
  and Ns_SG_CD_3WTs: "Ns (toSGr SG_CD_3WTsP) \<subseteq> V_A"

value "consInh SG_CD_3WTsP"

lemma wf_SG_CD_3WTs: "is_wf_sg (toSGr SG_CD_3WTsP)"
  proof -
    have h_wf_g: "is_wf_g (toSGr SG_CD_3WTsP)"
    proof (simp add: is_wf_g_def, rule conjI)
      show "Ns (toSGr SG_CD_3WTsP) \<subseteq> V_A"
      using Ns_SG_CD_3WTs by (simp add: SG_CD_3WTsP_def)
    next
      apply_end(rule conjI)
      show "Es (toSGr SG_CD_3WTsP) \<subseteq> E_A"
      using Es_SG_CD_3WTs by (simp add: SG_CD_3WTsP_def)
    next
      apply_end(rule conjI)
      show "ftotal_on (src (toSGr SG_CD_3WTsP)) (Es (toSGr SG_CD_3WTsP)) (Ns (toSGr SG_CD_3WTsP))"
      by (auto simp add: ftotal_on_def SG_CD_3WTsP_def toSGr_def)
    next
      show "ftotal_on (tgt (toSGr SG_CD_3WTsP)) (Es (toSGr SG_CD_3WTsP)) (Ns (toSGr SG_CD_3WTsP))"
      by (simp add: ftotal_on_def, rule conjI, simp add: SG_CD_3WTsP_def toSGr_def)
        (rule subsetI, simp add: SG_CD_3WTsP_def toSGr_def, erule disjE, simp, 
          erule disjE, simp, erule disjE, simp, erule disjE, simp, erule disjE, simp,
          erule disjE, simp, erule disjE, simp, erule disjE, simp,
          erule disjE, simp, erule disjE, simp, erule disjE, simp, erule disjE, simp,
          erule disjE, simp, erule disjE, simp, erule disjE, simp, erule disjE, simp,
          erule disjE, simp, erule disjE, simp, erule disjE, simp, erule disjE, simp,
          erule disjE, simp, erule disjE, simp, erule disjE, simp, erule disjE, simp,
          erule disjE, simp, erule disjE, simp, erule disjE, simp, erule disjE, simp,
          erule disjE, simp, erule disjE, simp, erule disjE, simp, erule disjE, simp,
          erule disjE, simp, erule disjE, simp, erule disjE, simp, erule disjE, simp,
          erule disjE, simp, erule disjE, simp, erule disjE, simp, erule disjE, simp,
          erule disjE, simp, erule disjE, simp, erule disjE, simp, erule disjE, simp,
          erule disjE, simp, erule disjE, simp, erule disjE, simp, erule disjE, simp,
          erule disjE, simp, erule disjE, simp, erule disjE, simp, erule disjE, simp,
          erule disjE, simp, erule disjE, simp, erule disjE, simp, erule disjE, simp)
    qed      
    show ?thesis
    proof (simp add: is_wf_sg_def, rule conjI)
      show "is_wf_g (toSGr SG_CD_3WTsP)"
        using h_wf_g by simp
    next
      apply_end(rule conjI)
      show "ftotal_on (nty (toSGr SG_CD_3WTsP)) (Ns (toSGr SG_CD_3WTsP)) SGNTy_set"
        by (simp add: ftotal_on_def SGNTy_set_def SG_CD_3WTsP_def toSGr_def)
    next
      apply_end(rule conjI) 
      show "ftotal_on (ety (toSGr SG_CD_3WTsP)) (Es (toSGr SG_CD_3WTsP)) SGETy_set"
        by (simp add: ftotal_on_def, rule conjI, rule equalityI)
        (simp_all add: SGNTy_set_def SG_CD_3WTsP_def toSGr_def SGETy_set_def)
    next
      apply_end(rule conjI) 
      show "dom (srcm (toSGr SG_CD_3WTsP)) = EsTy (toSGr SG_CD_3WTsP) {Some erelbi, Some ecompbi}"
        by (simp add: SG_CD_3WTsP_def toSGr_def EsTy_def vimage_def)
    next
      apply_end(rule conjI) 
      show "dom (tgtm (toSGr SG_CD_3WTsP)) = EsTy (toSGr SG_CD_3WTsP) {Some erelbi, Some ereluni, Some ecompbi, Some ecompuni}"
        by (auto simp add: SG_CD_3WTsP_def toSGr_def EsTy_def vimage_def)
    next
      apply_end(rule conjI)
      show "EsR (toSGr SG_CD_3WTsP) \<subseteq> EsId (toSGr SG_CD_3WTsP)"
      proof
        fix x
        assume " x \<in> EsR (toSGr SG_CD_3WTsP)"
        then show "x \<in> EsId (toSGr SG_CD_3WTsP)"
        by (auto simp add: EsR_def toSGr_def EsTy_def vimage_def SG_CD_3WTsP_def EsId_def
          split: if_splits)
      qed
    next
      apply_end(rule conjI)
      show "srcm (toSGr SG_CD_3WTsP) ` EsTy (toSGr SG_CD_3WTsP) {Some ecompbi}
        \<subseteq> {Some (rm 0 (val (Suc 0))), Some (sm (val (Suc 0)))}"
        by (simp add: toSGr_def image_def SG_CD_3WTsP_def EsTy_def)
    next
      show "acyclicGr (inhG (toSGr SG_CD_3WTsP))"
        using h_wf_g by (simp add: inh_eq acyclicGr_def rtrancl_in inh_eq_consInh)(eval)
    qed
  qed

(*'F_CD' Fragment*)
definition F_CD_3WTsP :: "Fr_ls"
where
   "F_CD_3WTsP \<equiv> \<lparr>sg_ls = SG_CD_3WTsP, 
    tr_ls = [(''ERPrWaterTank'', ''WaterTank''), (''ERPrValve'', ''Valve''), 
    (''ERPrTanksControl1'', ''TanksControl1''), (''ERPrTanksControl2'', ''TanksControl2''),
    (''ERPrController'', ''Controller''),
    (''ERPrValve_v2'', ''Valve_v2''), (''ERPrValve_w'', ''Valve_w''), 
    (''ERPrWaterTank_win'', ''WaterTank_win''),
    (''ERPrWaterTank_wout'', ''WaterTank_wout''), 
    (''ERPrController_v1'', ''Controller_v1'')]\<rparr>"

value "consRefs F_CD_3WTs"

value "consUFs [F_ASD_3WTs, F_CD_3WTs]"

(* Well-formedness proof obligation of fragments"*)
lemma wf_F_CD_3WTs: "is_wf_fr (toFr F_CD_3WTs)"
  proof -
    let ?refs_F_CD_3WTs = "{(''PrWaterTank'', ''WaterTank''), 
      (''PrValve'', ''Valve''),
      (''PrTanksControl1'', ''TanksControl1''), 
      (''PrTanksControl2'', ''TanksControl2''),
      (''PrController'', ''Controller''), 
      (''PrValve_v2'', ''Valve_v2''),
      (''PrValve_w'', ''Valve_w''), 
      (''PrWaterTank_win'', ''WaterTank_win''),
      (''PrWaterTank_wout'', ''WaterTank_wout''), 
      (''PrController_v1'', ''Controller_v1'')}"
    have h_EsRP: "EsRP (sg (toFr F_CD_3WTs)) = {''ERPrWaterTank'', ''ERPrValve'',
          ''ERPrTanksControl1'', ''ERPrTanksControl2'',
          ''ERPrController'', ''ERPrValve_v2'',
          ''ERPrValve_w'', ''ERPrWaterTank_win'', 
          ''ERPrWaterTank_wout'', ''ERPrController_v1''}"
      by (rule equalityI, rule subsetI, simp_all add: EsRP_def EsR_def EsTy_def NsP_def NsTy_def 
        toFr_def F_CD_3WTs_def toSGr_def SG_CD_3WTs_def split: if_splits)
    have h_ftotal_tr: "ftotal_on (tr (toFr F_CD_3WTs)) (EsRP (sg (toFr F_CD_3WTs))) V_A"
      using Ns_SG_ASD_3WTs
      by (simp add: h_EsRP)(simp add: F_CD_3WTs_def SG_CD_3WTs_def toSGr_def toFr_def  
          ftotal_on_def SG_ASD_3WTs_def) 
    from wf_SG_CD_3WTs have hb: "is_wf_sg (sg (toFr F_CD_3WTs))"
      by (simp add: toFr_def F_CD_3WTs_def)
    have refs_F_CD_3WTs: "refs (toFr F_CD_3WTs) = ?refs_F_CD_3WTs"
      using h_ftotal_tr hb by (simp add: refs_eq_consRefs, eval)
    have h_NsP: "NsP (sg (toFr F_CD_3WTs)) = {''PrWaterTank'', 
      ''PrValve'', ''PrTanksControl1'', ''PrTanksControl2'', 
      ''PrController'', ''PrValve_v2'', ''PrValve_w'', ''PrWaterTank_win'', 
      ''PrWaterTank_wout'', ''PrController_v1''}"
      by (rule equalityI, rule subsetI, simp_all add: F_CD_3WTs_def NsP_def NsTy_def 
        toFr_def SG_CD_3WTs_def toSGr_def vimage_def split: if_splits)
    show ?thesis
    proof (simp add: is_wf_fr_def)
      apply_end(rule conjI)
      show "is_wf_sg (sg (toFr F_CD_3WTs))"  
        by (simp add: wf_SG_CD_3WTs toFr_def F_CD_3WTs_def)
    next
      apply_end(rule conjI) 
      show "ftotal_on (tr (toFr F_CD_3WTs)) (EsRP (sg (toFr F_CD_3WTs))) V_A"
        by (simp add: h_ftotal_tr)
    next
      apply_end(rule conjI)  
      show "inj_on (src (sg (toFr F_CD_3WTs))) (EsRP (sg (toFr F_CD_3WTs)))"
      proof (simp add: inj_on_def, clarify)
        fix x y
        assume "x \<in> EsRP (sg (toFr F_CD_3WTs))"
          and "y \<in> EsRP (sg (toFr F_CD_3WTs))"
          and "src (sg (toFr F_CD_3WTs)) x = src (sg (toFr F_CD_3WTs)) y"
        then show "x = y"
        by (simp add: h_EsRP) (simp add: F_CD_3WTs_def  
          SG_CD_3WTs_def toFr_def toSGr_def split: if_splits) 
      qed
    next
      apply_end(rule conjI)  
      show "ran (src (sg (toFr F_CD_3WTs)) |` EsRP (sg (toFr F_CD_3WTs))) = NsP (sg (toFr F_CD_3WTs))"
      by (simp add: h_EsRP h_NsP)(rule equalityI, simp_all add: F_CD_3WTs_def SG_CD_3WTs_def  
        toFr_def toSGr_def)
    next
      apply_end(rule conjI)
      show "\<forall>v. v \<in> NsP (sg (toFr F_CD_3WTs)) \<longrightarrow> nonPRefsOf (toFr F_CD_3WTs) v \<noteq> {}"
      proof (rule allI, rule impI)
        fix v
        assume h1: "v \<in> NsP (sg (toFr F_CD_3WTs))"
        then show "nonPRefsOf (toFr F_CD_3WTs) v \<noteq> {}"
        proof (case_tac  "v = ''PrWaterTank''")
          assume "v = ''PrWaterTank''"
          then show "nonPRefsOf (toFr F_CD_3WTs) v \<noteq> {}"
            by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTs trancl_in)
        next  
          assume h2: "v \<noteq> ''PrWaterTank''"
          then show "nonPRefsOf (toFr F_CD_3WTs) v \<noteq> {}"
          proof (case_tac  "v = ''PrValve''")
            assume "v = ''PrValve''"
            then show "nonPRefsOf (toFr F_CD_3WTs) v \<noteq> {}"
              by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTs trancl_in)
          next
            assume h3: "v \<noteq> ''PrValve''"
            then show "nonPRefsOf (toFr F_CD_3WTs) v \<noteq> {}"
            proof (case_tac  "v = ''PrTanksControl1''")
              assume "v = ''PrTanksControl1''"
              then show "nonPRefsOf (toFr F_CD_3WTs) v \<noteq> {}"
                by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTs trancl_in)
            next
              assume h4: "v \<noteq> ''PrTanksControl1''"
              then show "nonPRefsOf (toFr F_CD_3WTs) v \<noteq> {}"
              proof (case_tac  "v = ''PrTanksControl2''")
                assume "v = ''PrTanksControl2''"
                then show "nonPRefsOf (toFr F_CD_3WTs) v \<noteq> {}"
                  by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTs trancl_in)
              next
                assume h5: "v \<noteq> ''PrTanksControl2''"
                then show "nonPRefsOf (toFr F_CD_3WTs) v \<noteq> {}"
                proof (case_tac  "v = ''PrController''")
                  assume "v = ''PrController''"
                  then show "nonPRefsOf (toFr F_CD_3WTs) v \<noteq> {}"
                    by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTs trancl_in)
                next
                  assume h6: "v \<noteq> ''PrController''"
                  then show "nonPRefsOf (toFr F_CD_3WTs) v \<noteq> {}"
                  proof (case_tac "v = ''PrValve_v2''")
                    assume "v = ''PrValve_v2''"
                    then show "nonPRefsOf (toFr F_CD_3WTs) v \<noteq> {}"
                      by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTs trancl_in)
                  next
                    assume h7: "v \<noteq> ''PrValve_v2''"
                    then show "nonPRefsOf (toFr F_CD_3WTs) v \<noteq> {}"
                    proof (case_tac "v = ''PrValve_w''")
                      assume "v = ''PrValve_w''"
                      then show "nonPRefsOf (toFr F_CD_3WTs) v \<noteq> {}"
                        by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTs trancl_in)
                    next
                      assume h8: "v \<noteq> ''PrValve_w''"
                      then show "nonPRefsOf (toFr F_CD_3WTs) v \<noteq> {}"
                      proof (case_tac "v = ''PrWaterTank_win''")
                        assume "v = ''PrWaterTank_win''"
                        then show "nonPRefsOf (toFr F_CD_3WTs) v \<noteq> {}"
                          by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTs trancl_in)
                      next
                        assume h9: "v \<noteq> ''PrWaterTank_win''"
                        then show "nonPRefsOf (toFr F_CD_3WTs) v \<noteq> {}"
                        proof (case_tac "v = ''PrWaterTank_wout''")
                          assume "v = ''PrWaterTank_wout''"
                          then show "nonPRefsOf (toFr F_CD_3WTs) v \<noteq> {}"
                            by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTs trancl_in)
                        next
                          assume h10: "v \<noteq> ''PrWaterTank_wout''"
                          then show "nonPRefsOf (toFr F_CD_3WTs) v \<noteq> {}"
                          using h2 h3 h4 h5 h6 h7 h8 h9 
                          proof (case_tac "v = ''PrController_v1''")
                            assume "v = ''PrController_v1''"
                            then show "nonPRefsOf (toFr F_CD_3WTs) v \<noteq> {}"
                              by (simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTs 
                                trancl_in)
                          next
                            assume "v \<noteq> ''PrController_v1''"
                            show "nonPRefsOf (toFr F_CD_3WTs) v \<noteq> {}"
                            using h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 
                              by (auto simp add: h_NsP nonPRefsOf_def refsOf_def refs_F_CD_3WTs image_def)
                          qed
                        qed
                      qed
                    qed
                  qed 
                qed
              qed
            qed
          qed
        qed
      qed
    next
      apply_end(rule conjI)
      have h_wf_g: "is_wf_g (toSGr SG_CD_3WTs)"
        using wf_SG_CD_3WTs
        by (simp add: is_wf_sg_def)
      show "acyclic_fr (toFr F_CD_3WTs)"
      proof -
          from wf_SG_CD_3WTs have "acyclic (inh (sg (toFr F_CD_3WTs)))"
            by (simp add: is_wf_sg_def acyclicGr_def inh_def F_CD_3WTs_def toFr_def)
          then show "acyclic_fr (toFr F_CD_3WTs)"
          proof (simp add: acyclic_fr_def)
            assume h1: "acyclic (inh (sg (toFr F_CD_3WTs)))"
            have h2: "is_wf_g (toSGr (sg_ls (F_CD_3WTs)))"
              using wf_SG_CD_3WTs by (simp add: F_CD_3WTs_def is_wf_sg_def)
            have h3: "Domain (inh (sg (toFr F_CD_3WTs))) \<inter> Domain (refs (toFr F_CD_3WTs)) = {}"
              using h2 
                by (simp add: refs_F_CD_3WTs)(simp add: toFr_def inh_eq_consInh, eval)
            have h4: "Range (refs (toFr F_CD_3WTs)) \<inter> Domain (inh (sg (toFr F_CD_3WTs))) = {}"
              using h2 by (simp add: refs_F_CD_3WTs)(simp add: toFr_def inh_eq_consInh, eval)
            have h5: "acyclic(refs (toFr F_CD_3WTs))"
              by (simp add: refs_F_CD_3WTs)(auto simp add: rtrancl_in acyclic_def)
            from h1 h3 h4 h5 show "acyclic (inh (sg (toFr F_CD_3WTs)) \<union> refs (toFr F_CD_3WTs))"
              by (simp add: acyclic_Un)
          qed
        qed
    next
      show "proxies_dont_inherit (toFr F_CD_3WTs)"
      proof (simp add: proxies_dont_inherit_def, rule equalityI, rule subsetI)
        fix x
        assume "x \<in> ran (src (sg (toFr F_CD_3WTs)) |` EsI (sg (toFr F_CD_3WTs))) \<inter>
             NsP (sg (toFr F_CD_3WTs))"
        then show "x \<in> {}"
        by (simp add: h_NsP)(auto simp add: restrict_map_def 
          F_CD_3WTs_def toFr_def vimage_def SG_CD_3WTs_def toSGr_def EsI_def EsTy_def ran_def
          split: if_splits)
      next
        show "{} \<subseteq> ran (src (sg (toFr F_CD_3WTs)) |` EsI (sg (toFr F_CD_3WTs))) \<inter> NsP (sg (toFr F_CD_3WTs))"
        by (simp)
      qed
    qed
  qed

definition T_F_ASD_3WTs :: "MorphL"
where
   "T_F_ASD_3WTs \<equiv> \<lparr>fVL = [(''WaterTanksASD'', ''ASD''), 
   (''WaterTanksSys'', ''System''), 
   (''CompWaterTanksSys1'', ''Composition''),
   (''CompWaterTanksSys2'', ''Composition''), 
   (''CompWaterTanksSys3'', ''Composition''),
   (''TanksControl1'', ''EComponent''), 
   (''TanksControl2'', ''EComponent''),
   (''CompTanksControl1Valve'', ''Composition''),
   (''CompTanksControl1WaterTank'', ''Composition''),
   (''CompTanksControl2WaterTank'', ''Composition''),
   (''Controller'', ''EComponent''),
   (''Valve'', ''POComponent''), 
   (''WaterTank'', ''POComponent''),
   (''FlowRate'', ''DType''), (''Area'', ''DType''), 
   (''Height'', ''DType''), (''OpenClosed'', ''Enumeration''),
   (''WaterTank_win'', ''FlowPort''), (''WaterTank_wout'', ''FlowPort''), 
   (''Valve_v2'', ''FlowPort''), (''Valve_w'', ''FlowPort''), 
   (''Controller_v1'', ''FlowPort'')], 
    fEL = [
      (''EWaterTanksASD_WaterTanksSys'', ''Eblocks''), 
      (''EWaterTanksASD_TanksControl1'', ''Eblocks''), 
      (''EWaterTanksASD_TanksControl2'', ''Eblocks''), 
      (''EWaterTanksASD_Valve'', ''Eblocks''), 
      (''EWaterTanksASD_WaterTank'', ''Eblocks''), 
      (''EWaterTanksASD_FlowRate'', ''Etypes''), 
      (''EWaterTanksASD_Area'', ''Etypes''), 
      (''EWaterTanksASD_Height'', ''Etypes''), 
      (''EWaterTanksASD_OpenClosed'', ''Etypes''),
      (''ECompWaterTanksSys1_src'', ''Esrc''),
      (''ECompWaterTanksSys2_src'', ''Esrc''),
      (''ECompWaterTanksSys3_src'', ''Esrc''),
      (''ECompWaterTanksSys1_tgt'', ''Etgt''),
      (''ECompWaterTanksSys2_tgt'', ''Etgt''),
      (''ECompWaterTanksSys3_tgt'', ''Etgt''),
      (''ECompTanksControl1Valve_src'', ''Esrc''),
      (''ECompTanksControl1WaterTank_src'', ''Esrc''), 
      (''ECompTanksControl2WaterTank_src'', ''Esrc''),
      (''ECompTanksControl1Valve_tgt'', ''Etgt''),
      (''ECompTanksControl1WaterTank_tgt'', ''Etgt''), 
      (''ECompTanksControl2WaterTank_tgt'', ''Etgt''),
      (''E_WaterTank_win'', ''EBlockProps''), 
      (''E_WaterTank_out'', ''EBlockProps''), 
      (''E_Valve_v2'', ''EBlockProps''), 
      (''E_Valve_w'', ''EBlockProps''), 
      (''E_Controller_v1'', ''EBlockProps''),
      (''E_Dep_w_v2'', ''EFlowPortDepends''), 
      (''E_Dep_wout_win'', ''EFlowPortDepends'')]\<rparr>"

(*Define the other morphism*)
definition T_F_CD_3WTs :: "MorphL"
where
   "T_F_CD_3WTs \<equiv> \<lparr>fVL = [(''PrWaterTank'', ''PrBlock3''), 
      (''PrValve'', ''PrBlock3''), 
      (''PrTanksControl1'', ''PrBlock3''), 
      (''PrTanksControl2'', ''PrBlock3''), 
      (''PrController'', ''PrBlock3''), 
      (''CD_3WTs'', ''ConnectionsDiagram''), 
      (''WTSys'', ''BlockInstance''), 
      (''V'', ''BlockInstance''), 
      (''WT1'', ''BlockInstance''), 
      (''WT2'', ''BlockInstance''), 
      (''WT3'', ''BlockInstance''), 
      (''C'', ''BlockInstance''),
      (''TC1'', ''BlockInstance''), 
      (''TC2'', ''BlockInstance''), 
      (''C_w_win1'', ''Connector''), 
      (''C_wout1_win2'', ''Connector''), 
      (''C_wout2_win3'', ''Connector''),
      (''C_v1_v2'', ''Connector''),
      (''v1'', ''Port''), (''v2'', ''Port''), 
      (''w'', ''Port''), (''win1'', ''Port''), 
      (''wout1'', ''Port''), (''win2'', ''Port''), 
      (''wout2'', ''Port''),
      (''win3'', ''Port''), (''wout3'', ''Port''), 
      (''PrValve_v2'', ''PrFlowPort2''), 
      (''PrValve_w'', ''PrFlowPort2''), 
      (''PrWaterTank_win'', ''PrFlowPort2''), 
      (''PrWaterTank_wout'', ''PrFlowPort2''), 
      (''PrController_v1'', ''PrFlowPort2'')],
    fEL = [(''ECD_WTSys'', ''ECDblocks''), (''ECD_V'', ''ECDblocks''), 
      (''ECD_WT1'', ''ECDblocks''), (''ECD_WT2'', ''ECDblocks''),
      (''ECD_WT3'', ''ECDblocks''), (''ECD_C'', ''ECDblocks''),
      (''ECD_TC1'', ''ECDblocks''), (''ECD_TC2'', ''ECDblocks''),
      (''ECD_C_v1_v2'', ''ECDconnectors''), (''ECD_C_w_win1'', ''ECDconnectors''),
      (''ECD_C_wout1_win2'', ''ECDconnectors''), 
      (''ECD_C_wout2_win3'', ''ECDconnectors''),
      (''E_C_v1_v2_src'', ''EC_src''), (''E_C_v1_v2_tgt'', ''EC_tgt''), 
      (''E_C_w_win1_src'', ''EC_src''), (''E_C_w_win1_tgt'', ''EC_tgt''), 
      (''E_C_wout1_win2_src'', ''EC_src''), (''E_C_wout1_win2_tgt'', ''EC_tgt''), 
      (''E_C_wout2_win3_src'', ''EC_src''), (''E_C_wout2_win3_tgt'', ''EC_tgt''), 
      (''E_C_v1'', ''EBIports''), (''E_V_v2'', ''EBIports''),   
      (''E_V_w'', ''EBIports''), 
      (''E_WT1_win1'', ''EBIports''),
      (''E_WT1_wout1'', ''EBIports''), 
      (''E_WT2_win2'', ''EBIports''),
      (''E_WT2_wout2'', ''EBIports''), 
      (''E_WT3_win3'', ''EBIports''), 
      (''E_WT3_wout3'', ''EBIports''), (''E_v1_ty'', ''EPortType''), 
      (''E_v2_ty'', ''EPortType''), (''E_w_ty'', ''EPortType''),
      (''E_win1_ty'', ''EPortType''), 
      (''E_wout1_ty'', ''EPortType''),
      (''E_win2_ty'', ''EPortType''), (''E_wout2_ty'', ''EPortType''), 
      (''E_win3_ty'', ''EPortType''), (''E_wout3_ty'', ''EPortType''),
      (''ERPrWaterTank'', ''ERPrBlock3''), (''ERPrValve'', ''ERPrBlock3''), 
      (''ERPrTanksControl1'', ''ERPrBlock3''), 
      (''ERPrTanksControl2'', ''ERPrBlock3''),
      (''ERPrController'', ''ERPrBlock3''), 
      (''ERPrValve_v2'', ''ERPrFlowPort2''),
      (''ERPrValve_w'', ''ERPrFlowPort2''), 
      (''ERPrWaterTank_win'', ''ERPrFlowPort2''),
      (''ERPrWaterTank_wout'', ''ERPrFlowPort2''), 
      (''ERPrController_v1'', ''ERPrFlowPort2'')]\<rparr>"

definition GFG_3WTs :: "GFGr_ls"
where
  "GFG_3WTs \<equiv> 
    \<lparr>NsG = [''F_ASD_3WTs'', ''F_CD_3WTs''], 
      EsG= [''E_F_CD_3WTs_ASD'', ''E_F_ASD_3WTs'', ''E_F_CD_3WTs''], 
      srcG = [(''E_F_CD_3WTs_ASD'', ''F_CD_3WTs''), 
        (''E_F_ASD_3WTs'', ''F_ASD_3WTs''),
        (''E_F_CD_3WTs'', ''F_CD_3WTs'')],
      tgtG = [(''E_F_CD_3WTs_ASD'', ''F_ASD_3WTs''), 
        (''E_F_ASD_3WTs'', ''F_ASD_3WTs''),
        (''E_F_CD_3WTs'', ''F_CD_3WTs'')],
      ext_ty_ls = [(''E_F_CD_3WTs_ASD'', eimp), (''E_F_ASD_3WTs'', eimp),
        (''E_F_CD_3WTs'', eimp)]\<rparr>"

axiomatization
where
  Es_GFG_3WTs: "Es (toGFGr(GFG_3WTs)) \<subseteq> E_A"
  and Ns_GFG_3WTs: "Ns (toGFGr(GFG_3WTs)) \<subseteq> V_A"

lemma is_wf_GFG_3WTs: "is_wf_gfg_ls GFG_3WTs"
  proof -
    have h_wf_g: "is_wf_g (toGFGr GFG_3WTs)"
      using Es_GFG_3WTs Ns_GFG_3WTs
        by (auto simp add: is_wf_g_def GFG_3WTs_def ftotal_on_def toGFGr_def)
    show ?thesis
    proof (simp add: is_wf_gfg_ls_def, rule conjI)
      show "distinct (NsG GFG_3WTs)"
      by (simp add: GFG_3WTs_def)
    next
      apply_end(rule conjI)
      show "distinct (map fst (srcG GFG_3WTs))"
        by (simp add: GFG_3WTs_def)
    next
      apply_end(rule conjI)
      show "distinct (map fst (tgtG GFG_3WTs))"
        by (simp add: GFG_3WTs_def)
    next
      show "is_wf_gfg (toGFGr GFG_3WTs)"
        proof (simp add: is_wf_gfg_def, rule conjI)
          show "is_wf_g (toGFGr GFG_3WTs)"
            using h_wf_g by simp
        next
          apply_end (rule conjI)
          show "ftotal_on (ext_ty (toGFGr GFG_3WTs)) (Es (toGFGr GFG_3WTs)) GFGEdgeTy_set"
            by (simp add: GFG_3WTs_def toGFGr_def GFGEdgeTy_set_def ftotal_on_def)
        next
          apply_end (rule conjI)
          show "NodesWithSelfEdges (toGFGr GFG_3WTs)"
          proof (simp add: NodesWithSelfEdges_def, clarify)
            fix v
            assume "v \<in> Ns (toGFGr GFG_3WTs)"
            then have h1: "v = ''F_CD_3WTs'' \<or> v = ''F_ASD_3WTs''"
              by (auto simp add: GFG_3WTs_def toGFGr_def)
            then show "\<exists>e. e \<in> Es (toGFGr GFG_3WTs) 
              \<and> src (toGFGr GFG_3WTs) e = Some v 
              \<and> tgt (toGFGr GFG_3WTs) e = Some v"
            by (simp add:  GFG_3WTs_def toGFGr_def NodesWithSelfEdges_def)
              (erule disjE, rule exI[where x= "''E_F_CD_3WTs''"], simp_all, 
                rule exI[where x= "''E_F_ASD_3WTs''"], simp)
          qed
        next
          show "acyclicGr
            (restrict (toGFGr GFG_3WTs)
              (Es (toGFGr GFG_3WTs) - EsId (toGFGr GFG_3WTs)))"
          by (auto simp add: GFG_3WTs_def toGFGr_def EsId_def restrict_def acyclicGr_def
            relOfGr_def rst_Ns_def rst_fun_def adjacent_def acyclic_def elim: tranclE)
     qed
   qed
  qed

definition Mdl_3WTs :: "Mdl_ls"
where
  "Mdl_3WTs \<equiv> \<lparr>gfgL = GFG_3WTs, 
    frdL = [(''F_ASD_3WTs'', F_ASD_3WTs), (''F_CD_3WTs'', F_CD_3WTs)]\<rparr>"

lemma is_wf_mdl_3WTs: "is_wf_mdl (toMdl Mdl_3WTs)"
  proof (simp add: is_wf_mdl_def, rule conjI)
    show "\<forall>F. F \<in> ran (frd (toMdl Mdl_3WTs)) \<longrightarrow> is_wf_fr F"
    proof (clarify)
      fix F
      assume "F \<in> ran (frd (toMdl Mdl_3WTs))"
      then have h1: "F = (toFr F_ASD_3WTs) \<or> F = (toFr F_CD_3WTs)"
        by (auto simp add: INTO_SysML_MM_def toMdl_def Mdl_3WTs_def)
      then show "is_wf_fr F"
      proof (case_tac "F = toFr F_ASD_3WTs")
        assume "F = toFr F_ASD_3WTs"
        then show "is_wf_fr F"
          by (simp add: wf_F_ASD_3WTs)
      next
        assume h2: "F \<noteq> toFr F_ASD_3WTs"
        then show "is_wf_fr F"
        proof (case_tac "F = toFr F_CD_3WTs")
          assume "F = toFr F_CD_3WTs"
          then show "is_wf_fr F"
            by (simp add: wf_F_CD_3WTs)
        next
          assume h3: "F \<noteq> toFr F_CD_3WTs"
          then show "is_wf_fr F" using h1 h2 by (simp)
        qed
      qed
    qed
  next
    apply_end(rule conjI)
    show "is_wf_gfg_ls (gfg (toMdl Mdl_3WTs))"
      by (simp add: is_wf_GFG_3WTs Mdl_3WTs_def toMdl_def)
  next
    apply_end(rule conjI)
    show "ftotal_on (frd (toMdl Mdl_3WTs)) (set (NsG (gfg (toMdl Mdl_3WTs)))) fr_set"
      by (simp add: ftotal_on_def Mdl_3WTs_def toMdl_def GFG_3WTs_def F_ASD_3WTs_def
        toFr_def toSGr_def SG_ASD_3WTs_def F_CD_3WTs_def fr_set_def is_fr_def)
  next
    apply_end(rule conjI)
    show "disjMdlFrs (toMdl Mdl_3WTs)"
      by (simp add: disjMdlFrs_def Mdl_3WTs_def disjFs_def disjGsL_def 
        GFG_3WTs_def F_Common_def SG_F_Common_def F_Props_def SG_F_Props_def
        toFr_def toMdl_def toSGr_def SG_ASD_3WTs_def SG_CD_3WTs_def
        F_ASD_3WTs_def F_CD_3WTs_def)
  next
    show "mUM2GFG (toMdl Mdl_3WTs)
      \<in> morphF2GFGr (UMdlFs (toMdl Mdl_3WTs)) (toGFGr (gfg (toMdl Mdl_3WTs)))"
      by (simp add: UGM_eq_ConsUGM)
  qed

definition MdlTy_3WTs :: "MdlTy_ls"
where
  "MdlTy_3WTs \<equiv> \<lparr>tmdlL = INTO_SysML_MM_T, 
    mdlL = Mdl_3WTs,
    mtyL = (consUGM T_F_ASD_3WTs T_F_CD_3WTs)\<rparr>"

lemma is_wf_mdlt_3WTs: "is_wf_mdlty (toMdlTy MdlTy_3WTs)"
  proof (simp add: is_wf_mdlty_def, rule conjI)
    show "is_wf_tmdl (tmdl (toMdlTy MdlTy_3WTs))"
      by (simp add: is_wf_INTO_SysML_MM_T MdlTy_3WTs_def toMdlTy_def)
  next
    apply_end(rule conjI)
    show "is_wf_mdl (mdl (toMdlTy MdlTy_3WTs))"
      by (simp add: is_wf_mdl_3WTs toMdlTy_def MdlTy_3WTs_def)
  next
    show "mty (toMdlTy MdlTy_3WTs)
    \<in> morphFr (UMdlFs (mdl (toMdlTy MdlTy_3WTs))) (fr (UTyMdlFs (tmdl (toMdlTy MdlTy_3WTs))))"
    by (simp add: toMdlTy_def MdlTy_3WTs_def)
  qed

value "consUMdlFs (mdlL MdlTy_3WTs)"
 
value "INTO_SysML_toPDG_Nodes (mdlL MdlTy_3WTs) (toMorph (mtyL MdlTy_3WTs))"

value "INTO_SysML_toPDG (mdlL MdlTy_3WTs) (toMorph (mtyL MdlTy_3WTs))"

fun portNodes :: "Mdl_ls \<Rightarrow> Morph \<Rightarrow> V list"
where
   "portNodes ML m = 
    (filter (\<lambda>v . (fV m) v = Some ''Port'' )((NsG o sg_ls) (consUMdlFs ML)))"

fun edgesOfTy :: "Mdl_ls \<Rightarrow> Morph \<Rightarrow> E \<Rightarrow>E list"
where
   "edgesOfTy ML m e = 
    (filter (\<lambda>v . (fE m) v = Some e )((EsG o sg_ls) (consUMdlFs ML)))"

value "portNodes (mdlL MdlTy_3WTs) (toMorph (mtyL MdlTy_3WTs))"

value "edgesOfTy (mdlL MdlTy_3WTs) (toMorph (mtyL MdlTy_3WTs)) ''EPortType''"

value "edgesOfTy (mdlL MdlTy_3WTs) (toMorph (mtyL MdlTy_3WTs)) ''EFlowPortDepends''"

value "edgesOfTy (mdlL MdlTy_3WTs) (toMorph (mtyL MdlTy_3WTs)) ''EBIports''"

value "the (tgt (sg (toFr (consUMdlFs (mdlL MdlTy_3WTs)))) ''E_WT3_win3'')"

value "the (tgt (sg (toFr (consUMdlFs (mdlL MdlTy_3WTs)))) ''E_v2_ty'')"

value "(set (consSrcStF (consUMdlFs (mdlL MdlTy_3WTs)))) ``{''E_Dep_w_v2''}"

value "the (tgt (sg (toFr (consUMdlFs (mdlL MdlTy_3WTs)))) ''E_Dep_w_v2'')"

(*Get these functions right*)
value "getBlockInstanceOfPort (toMorph (mtyL MdlTy_3WTs)) (consUMdlFs (mdlL MdlTy_3WTs)) ''win3''"
value "getOtherInternalPorts (toMorph (mtyL MdlTy_3WTs)) (consUMdlFs (mdlL MdlTy_3WTs)) ''win3''"
value "getFlowPortTypeOfPort (toMorph (mtyL MdlTy_3WTs)) (consUMdlFs (mdlL MdlTy_3WTs)) ''win3''"

(*
value "getDependentPortOfV (mty_ls MdlTy_3WTs) (consUMdlFs (mdl_ls MdlTy_3WTs)) ''w'' ''PrValve_v2''"
*)
value "(fV (toMorph (mtyL MdlTy_3WTs))) (the (tgt (sg (toFr (consUMdlFs (mdlL MdlTy_3WTs)))) ''E_v2_ty''))"

value "(set(consTgtStF (consUMdlFs (mdlL MdlTy_3WTs)))) ``{''E_v2_ty''}"

value "consClanF ''PrController_v1'' (consUMdlFs (mdlL MdlTy_3WTs))"

fun internalConnectionsOf :: "Mdl_ls \<Rightarrow> Morph \<Rightarrow> V \<Rightarrow> Gr_ls"
where
  "internalConnectionsOf ML m v = buildGrForInternalPortConnections m (consUMdlFs ML) v 
    (getFlowPortTypeOfPort m (consUMdlFs ML) v)"

fun dependsGrOf :: "Mdl_ls \<Rightarrow> Morph \<Rightarrow> V \<Rightarrow> Gr_ls"
where
  "dependsGrOf ML m v = consGLFrDepends m (consUMdlFs ML) v
    (filter (\<lambda> e. (getFlowPortTypeOfPort m (consUMdlFs ML) v) \<in> (set (consSrcStF (consUMdlFs ML))) ``{e})
            (filter (\<lambda> e. (fE m) e = Some ''EFlowPortDepends'') (EsG (sg_ls (consUMdlFs ML)))))"

value "buildGrForConnector (toMorph (mtyL MdlTy_3WTs)) (consUMdlFs (mdlL MdlTy_3WTs)) ''C_w_win1''"
value "dependsGrOf (mdlL MdlTy_3WTs) (toMorph (mtyL MdlTy_3WTs)) ''win3''"
value "internalConnectionsOf (mdlL MdlTy_3WTs) (toMorph (mtyL MdlTy_3WTs)) ''w''"

end