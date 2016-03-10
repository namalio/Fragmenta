
(*  File:      'INTO_SysML_3WTsPilot_ASD' 
    Description: ASD of encoding of INTO-SysML model of pilot case study of 3 Water tanks 
    Author:     Nuno Amálio
*)

theory INTO_SysML_3WTsPilot_loop_ASD
imports INTO_SysML_MM_Gbl
  
begin

(*The ASD corresponding to the ASD of 3WTs*)
definition SG_ASD_3WTsP_loop :: "SGr_ls"
where
  "SG_ASD_3WTsP_loop = \<lparr>NsG=[''3WaterTanksASD'', ''3WaterTanksSys'', ''CompWaterTanksSys1'',
    ''CompWaterTanksSys2'', ''CompWaterTanksSys3'',
    ''WaterTanks1'', ''WaterTanks2'', ''Controller'', 
    ''CompWaterTanks1Inflow'', ''CompWaterTanks1Pipe'', 
    ''CompWaterTanks1TankIO'', ''CompWaterTanks2TankIOV'', 
    ''CompWaterTanks2Drain'',
    ''Inflow'', ''Pipe'', ''TankIO'', ''TankIOV'', ''Drain'', ''FlowRate'', 
    ''WaterLevel'', ''ValveState'', ''WaterTanks1_win'',
    ''WaterTanks1_wout'', ''WaterTanks2_win'', ''WaterTanks2_wlout'', 
    ''WaterTanks2_vi'', ''Controller_wlin'', ''Controller_vo'',
    ''Inflow_wout'', ''Pipe_win'', ''Pipe_wout'', ''TankIO_win'', ''TankIO_wout'', 
    ''TankIOV_win'', ''TankIOV_wout'', ''TankIOV_wlout'', ''TankIOV_vi'',
    ''Drain_win'', ''Drain_wout''], 
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
        ''E_WaterTanks1_win'',
        ''E_WaterTanks1_wout'', ''E_WaterTanks2_win'', ''E_WaterTanks2_wlout'', 
        ''E_WaterTanks2_vi'', ''E_Controller_wlin'', ''E_Controller_vo'',
        ''E_Inflow_wout'', ''E_Pipe_win'', ''E_Pipe_wout'', ''E_TankIO_win'', 
        ''E_TankIO_wout'', 
        ''E_TankIOV_win'', ''E_TankIOV_wout'', ''E_TankIOV_wlout'', ''E_TankIOV_vi'',
        ''E_Drain_win'', ''E_Drain_wout'', 
        ''E_Dep_Pipe_wout_win'', ''E_Dep_TankIO_wout_win'',
        ''E_Dep_WaterTanks2_wlout_win'', 
        ''E_Dep_TankIOV_wout_win'', ''E_Dep_TankIOV_wlout_win'',
        ''E_Dep_TankIOV_wout_vi'', ''E_Dep_Controller_vo_wlin'', ''E_Dep_Drain_wout_win''], 
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
        (''E_WaterTanks1_win'', ''WaterTanks1''),
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
        (''E_Drain_win'', ''Drain''), (''E_Drain_wout'', ''Drain''),
        (''E_Dep_Drain_wout_win'', ''Drain_wout''),
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
        (''E_WaterTanks1_win'', ''WaterTanks1_win''),
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
        (''E_Drain_win'', ''Drain_win''), (''E_Drain_wout'', ''Drain_wout''),
        (''E_Dep_Drain_wout_win'', ''Drain_win''),
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
      (''WaterTanks1_win'',  nnrml),
      (''WaterTanks1_wout'',  nnrml), (''WaterTanks2_win'',  nnrml), 
      (''WaterTanks2_wlout'',  nnrml), (''WaterTanks2_vi'',  nnrml), 
      (''Controller_wlin'',  nnrml), (''Controller_vo'',  nnrml),
      (''Inflow_wout'',  nnrml), (''Pipe_win'',  nnrml), 
      (''Pipe_wout'',  nnrml), (''TankIO_win'',  nnrml),
      (''TankIO_wout'',  nnrml), (''TankIOV_win'',  nnrml),
      (''TankIOV_wout'',  nnrml), (''TankIOV_wlout'',  nnrml), 
      (''TankIOV_vi'',  nnrml), (''Drain_win'',  nnrml),
      (''Drain_wout'',  nnrml)],
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
        (''E_WaterTanks1_win'', elnk),
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
        (''E_Drain_win'', elnk), (''E_Drain_wout'', elnk),
        (''E_Dep_Drain_wout_win'', elnk),
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
  Es_SG_ASD_3WTsP_loop: "Es (toSGr SG_ASD_3WTsP_loop) \<subseteq> E_A"
  and Ns_SG_ASD_3WTsP_loop: "Ns (toSGr SG_ASD_3WTsP_loop) \<subseteq> V_A"

value "consInh SG_ASD_3WTsP_loop"

value "find (\<lambda>e. e \<notin> set(EsG SG_ASD_3WTsP_loop))(map fst (srcG SG_ASD_3WTsP_loop))"

lemma wf_SG_ASD_3WTsP_loop: "is_wf_sgL SG_ASD_3WTsP_loop"
  proof -
    have distinct_srcG: "distinct (map fst (srcG SG_ASD_3WTsP_loop))"
      by (eval)
    have distinct_tgtG: "distinct (map fst (tgtG SG_ASD_3WTsP_loop))"
      by (eval)
    have distinct_etyG: "distinct (map fst (etyG SG_ASD_3WTsP_loop))"
      by (eval)
    have distinct_ntyG: "distinct (map fst (ntyG SG_ASD_3WTsP_loop))"
      by (eval)
    have distinct_tgtmG: "distinct (map fst (tgtmG SG_ASD_3WTsP_loop))"
      by eval
    have h_wf_g: "is_wf_g (toSGr SG_ASD_3WTsP_loop)"
      proof (simp add: is_wf_g_def, rule conjI)
        show "Ns (toSGr SG_ASD_3WTsP_loop) \<subseteq> V_A"
          using Ns_SG_ASD_3WTsP_loop by simp
      next
        apply_end(rule conjI)
        show "Es (toSGr SG_ASD_3WTsP_loop) \<subseteq> E_A"
          using Es_SG_ASD_3WTsP_loop by simp
      next
        apply_end(rule conjI)
        show "ftotal_on (src (toSGr SG_ASD_3WTsP_loop)) (Es (toSGr SG_ASD_3WTsP_loop)) (Ns (toSGr SG_ASD_3WTsP_loop))"
          using distinct_srcG
          by (simp add: ftotal_on_def ran_distinct dom_map_of_conv_image_fst toSGr_def, eval)
      next
        show "ftotal_on (tgt (toSGr SG_ASD_3WTsP_loop)) (Es (toSGr SG_ASD_3WTsP_loop)) (Ns (toSGr SG_ASD_3WTsP_loop))"
          using distinct_tgtG
          by (simp add: ftotal_on_def ran_distinct dom_map_of_conv_image_fst toSGr_def, eval)
      qed
    have ftotal_on_ety: "ftotal_on (ety (toSGr SG_ASD_3WTsP_loop)) (Es (toSGr SG_ASD_3WTsP_loop)) SGETy_set"
      using distinct_etyG
      by (simp add: ftotal_on_def ran_distinct dom_map_of_conv_image_fst toSGr_def, eval)
    show ?thesis
    proof (simp add: is_wf_sgL_def, rule conjI)
      show "is_wf_gL SG_ASD_3WTsP_loop"
        using h_wf_g 
        by (simp add: is_wf_gL_def distinct_srcG distinct_tgtG is_wf_g_toSGr_imp_toGr)(eval)
    next
      apply_end(rule conjI)
      show "distinct (map fst (ntyG SG_ASD_3WTsP_loop))"
        by (eval)
    next
      apply_end(rule conjI) 
      show "distinct (map fst (etyG SG_ASD_3WTsP_loop))"
        by (eval)
    next
      apply_end(rule conjI) 
      show "distinct (map fst (srcmG SG_ASD_3WTsP_loop))"
        by eval
    next
      apply_end(rule conjI) 
      show "distinct (map fst (tgtmG SG_ASD_3WTsP_loop))"
        by (simp only: distinct_tgtmG)
    next
      show "is_wf_sg (toSGr SG_ASD_3WTsP_loop)"
      proof (simp add: is_wf_sg_def, rule conjI)
        show "is_wf_g (toSGr SG_ASD_3WTsP_loop)"
          using h_wf_g by simp
      next
        apply_end(rule conjI)
        show "ftotal_on (nty (toSGr SG_ASD_3WTsP_loop)) (Ns (toSGr SG_ASD_3WTsP_loop)) SGNTy_set"
          using distinct_ntyG
          by (simp add: ftotal_on_def ran_distinct dom_map_of_conv_image_fst toSGr_def, eval)
      next
        apply_end(rule conjI) 
        show "ftotal_on (ety (toSGr SG_ASD_3WTsP_loop)) (Es (toSGr SG_ASD_3WTsP_loop)) SGETy_set"
          by (simp only: ftotal_on_ety)
      next
        apply_end(rule conjI) 
        show "dom (srcm (toSGr SG_ASD_3WTsP_loop)) = EsTy (toSGr SG_ASD_3WTsP_loop) {Some erelbi, Some ecompbi}"
          by (simp add: SG_ASD_3WTsP_loop_def toSGr_def EsTy_def vimage_def)
      next
        apply_end(rule conjI) 
        have "None \<notin> {Some erelbi, Some ereluni, Some ecompbi, Some ecompuni}"
          by auto
        show "dom (tgtm (toSGr SG_ASD_3WTsP_loop)) = EsTy (toSGr SG_ASD_3WTsP_loop) {Some erelbi, Some ereluni, Some ecompbi, Some ecompuni}"
          by (rule equalityI, 
            simp add: SG_ASD_3WTsP_loop_def toSGr_def EsTy_def vimage_def, rule subsetI,
            simp add: SG_ASD_3WTsP_loop_def toSGr_def EsTy_def vimage_def split: if_splits)
      next
        apply_end(rule conjI)
        show "EsR (toSGr SG_ASD_3WTsP_loop) \<subseteq> EsId (toSGr SG_ASD_3WTsP_loop)"
          using h_wf_g ftotal_on_ety by (simp add: EsId_eq_EsIdL EsR_eq_EsRL)(eval)
      next
        apply_end(rule conjI)
        show "srcm (toSGr SG_ASD_3WTsP_loop) ` EsTy (toSGr SG_ASD_3WTsP_loop) {Some ecompbi}
          \<subseteq> {Some (rm 0 (val (Suc 0))), Some (sm (val (Suc 0)))}"
          by (simp add: toSGr_def image_def SG_ASD_3WTsP_loop_def EsTy_def)
      next
        show "acyclicGr (inhG (toSGr SG_ASD_3WTsP_loop))"
          using h_wf_g by (simp add: inh_eq acyclicGr_def rtrancl_in inh_eq_consInh)(eval)
      qed
    qed
  qed

(*'F_CD' Fragment*)
definition F_ASD_3WTsP_loop :: "Fr_ls"
where
   "F_ASD_3WTsP_loop \<equiv> \<lparr>sg_ls = SG_ASD_3WTsP_loop, 
    tr_ls = []\<rparr>"

value "consRefs F_ASD_3WTsP_loop"

value "EsRPL SG_ASD_3WTsP_loop"

(* Well-formedness proof obligation of fragments"*)
lemma wf_F_ASD_3WTsP_loop: "is_wf_fr (toFr F_ASD_3WTsP_loop)"
  proof -
    let ?refs_F_ASD_3WTsP_loop = "{}"
    have EsRP_ASD_3WTsP_loop: "EsRP (sg (toFr F_ASD_3WTsP_loop)) = {}"
      using wf_SG_ASD_3WTsP_loop 
        by (simp add: EsRP_eq_EsRPL toFr_def F_ASD_3WTsP_loop_def is_wf_sgL_def, eval)
    have h_ftotal_tr: "ftotal_on (tr (toFr F_ASD_3WTsP_loop)) (EsRP (sg (toFr F_ASD_3WTsP_loop))) V_A"
      proof (simp add: ftotal_on_def)
        apply_end(rule conjI)
        show "dom (tr (toFr F_ASD_3WTsP_loop)) = EsRP (sg (toFr F_ASD_3WTsP_loop))"
        proof
          show "dom (tr (toFr F_ASD_3WTsP_loop)) \<subseteq> EsRP (sg (toFr F_ASD_3WTsP_loop))"
            by (simp add: F_ASD_3WTsP_loop_def SG_ASD_3WTsP_loop_def toSGr_def toFr_def  
          SG_F_Props_def EsRP_def EsR_def NsP_def EsTy_def NsTy_def) 
        next
          show "EsRP (sg (toFr F_ASD_3WTsP_loop)) \<subseteq> dom (tr (toFr F_ASD_3WTsP_loop))"
            by (simp add: EsRP_ASD_3WTsP_loop)
        qed
      next
        show "ran (tr (toFr F_ASD_3WTsP_loop)) \<subseteq> V_A"
        using Ns_SG_F_ASD Ns_SG_F_Comps Ns_SG_F_Blocks Ns_SG_F_Common Ns_SG_F_VTypes
        by (simp add: F_ASD_3WTsP_loop_def SG_ASD_3WTsP_loop_def toSGr_def toFr_def 
          SG_F_Comps_def 
          SG_F_Blocks_def F_Common_def SG_F_Common_def F_VTypes_def SG_F_VTypes_def)
      qed
      from wf_SG_ASD_3WTsP_loop have hb: "is_wf_sg (sg (toFr F_ASD_3WTsP_loop))"
      by (simp add: toFr_def F_ASD_3WTsP_loop_def is_wf_sgL_def)
    have refs_F_ASD_3WTsP_loop: "refs (toFr F_ASD_3WTsP_loop) = ?refs_F_ASD_3WTsP_loop"
      using h_ftotal_tr hb by (simp add: refs_eq_consRefs, eval)
    show ?thesis
    proof (simp add: is_wf_fr_def)
      apply_end(rule conjI)
      show "is_wf_sg (sg (toFr F_ASD_3WTsP_loop))"  
        by (simp add: hb)
    next
      apply_end(rule conjI) 
      show "ftotal_on (tr (toFr F_ASD_3WTsP_loop)) (EsRP (sg (toFr F_ASD_3WTsP_loop))) V_A"
        by (simp add: h_ftotal_tr)
    next
      apply_end(rule conjI)  
      show "inj_on (src (sg (toFr F_ASD_3WTsP_loop))) (EsRP (sg (toFr F_ASD_3WTsP_loop)))"
        by (simp add: EsRP_ASD_3WTsP_loop)
    next
      apply_end(rule conjI)  
      show "ran (src (sg (toFr F_ASD_3WTsP_loop)) |` EsRP (sg (toFr F_ASD_3WTsP_loop))) 
        = NsP (sg (toFr F_ASD_3WTsP_loop))"
        by (simp add: EsRP_ASD_3WTsP_loop)(simp add: F_ASD_3WTsP_loop_def NsP_def NsTy_def 
          toFr_def SG_ASD_3WTsP_loop_def toSGr_def vimage_def)
    next
      apply_end(rule conjI)
      show "\<forall>v. v \<in> NsP (sg (toFr F_ASD_3WTsP_loop)) \<longrightarrow> nonPRefsOf (toFr F_ASD_3WTsP_loop) v \<noteq> {}"
        by (simp add: NsP_def NsTy_def nonPRefsOf_def refsOf_def refs_F_ASD_3WTsP_loop)
          (simp add: F_ASD_3WTsP_loop_def SG_ASD_3WTsP_loop_def toFr_def toSGr_def)
    next
      apply_end(rule conjI)
      have h_wf_g: "is_wf_g (toSGr SG_ASD_3WTsP_loop)"
        using wf_SG_ASD_3WTsP_loop
        by (simp add: is_wf_sgL_def is_wf_sg_def)
      show "acyclic_fr (toFr F_ASD_3WTsP_loop)"
        using  h_wf_g by (simp add: acyclic_fr_def refs_F_ASD_3WTsP_loop)
          (simp add: inh_eq rtrancl_in inh_eq_consInh F_ASD_3WTsP_loop_def toFr_def, eval)
    next
      show "proxies_dont_inherit (toFr F_ASD_3WTsP_loop)"
        by (simp add: proxies_dont_inherit_def restrict_map_def NsP_def NsTy_def
          F_ASD_3WTsP_loop_def toFr_def vimage_def SG_ASD_3WTsP_loop_def toSGr_def)
    qed
  qed

definition T_F_ASD_3WTsP_loop :: "MorphL"
where
   "T_F_ASD_3WTsP_loop \<equiv> \<lparr>fVL = [(''3WaterTanksASD'', ''ASD''), 
    (''3WaterTanksSys'', ''System''), 
    (''CompWaterTanksSys1'', ''Composition''),
    (''CompWaterTanksSys2'', ''Composition''), 
    (''CompWaterTanksSys3'', ''Composition''),
    (''WaterTanks1'', ''EComponent''), 
    (''WaterTanks2'', ''EComponent''),  
    (''Controller'', ''EComponent''), 
    (''CompWaterTanks1Inflow'', ''Composition''),
    (''CompWaterTanks1Pipe'', ''Composition''),
    (''CompWaterTanks1TankIO'', ''Composition''),
    (''CompWaterTanks2TankIOV'', ''Composition''),
    (''CompWaterTanks2Drain'', ''Composition''),
    (''Inflow'', ''POComponent''), (''Pipe'', ''POComponent''), 
    (''TankIO'', ''POComponent''), (''TankIOV'', ''POComponent''), 
    (''Drain'', ''POComponent''), (''FlowRate'', ''DType''), 
    (''WaterLevel'', ''DType''),  (''ValveState'', ''Enumeration''),
    (''WaterTanks1_win'', ''FlowPort''), (''WaterTanks1_wout'', ''FlowPort''), 
    (''WaterTanks2_win'', ''FlowPort''),  (''WaterTanks2_wlout'', ''FlowPort''), 
    (''WaterTanks2_vi'', ''FlowPort''), (''Controller_wlin'', ''FlowPort''), 
    (''Controller_vo'', ''FlowPort''), (''Inflow_wout'', ''FlowPort''), 
    (''Pipe_win'', ''FlowPort''), (''Pipe_wout'', ''FlowPort''), 
    (''TankIO_win'', ''FlowPort''), (''TankIO_wout'', ''FlowPort''), 
    (''TankIOV_win'', ''FlowPort''), (''TankIOV_wout'', ''FlowPort''), 
    (''TankIOV_wlout'', ''FlowPort''), (''TankIOV_vi'', ''FlowPort''), 
    (''Drain_win'', ''FlowPort''), (''Drain_wout'', ''FlowPort'')], 
    fEL = [
      (''E_3WaterTanksASD_3WaterTanksSys'', ''Eblocks''), 
      (''E_3WaterTanksASD_WaterTanks1'', ''Eblocks''), 
      (''E_3WaterTanksASD_WaterTanks2'', ''Eblocks''), 
      (''E_3WaterTanksASD_Controller'', ''Eblocks''), 
      (''E_3WaterTanksASD_TankIO'', ''Eblocks''), 
      (''E_3WaterTanksASD_TankIOV'', ''Eblocks''), 
      (''E_3WaterTanksASD_Inflow'', ''Eblocks''), 
      (''E_3WaterTanksASD_Pipe'', ''Eblocks''), 
      (''E_3WaterTanksASD_Drain'', ''Eblocks''), 
      (''E_3WaterTanksASD_FlowRate'', ''Etypes''), 
      (''E_3WaterTanksASD_WaterLevel'', ''Etypes''), 
      (''E_3WaterTanksASD_ValveState'', ''Etypes''), 
      (''E_CompWaterTanksSys1_src'', ''Esrc''), 
      (''E_CompWaterTanksSys1_tgt'',  ''Etgt''), 
      (''E_CompWaterTanksSys2_src'', ''Esrc''), 
      (''E_CompWaterTanksSys2_tgt'', ''Etgt''), 
      (''E_CompWaterTanksSys3_src'', ''Esrc''), 
      (''E_CompWaterTanksSys3_tgt'', ''Etgt''), 
      (''E_CompWaterTanks1Inflow_src'', ''Esrc''), 
      (''E_CompWaterTanks1Inflow_tgt'', ''Etgt''),
      (''E_CompWaterTanks1Pipe_src'', ''Esrc''), 
      (''E_CompWaterTanks1Pipe_tgt'', ''Etgt''),
      (''E_CompWaterTanks1TankIO_src'', ''Esrc''), 
      (''E_CompWaterTanks1TankIO_tgt'', ''Etgt''),
      (''E_CompWaterTanks2TankIOV_src'', ''Esrc''), 
      (''E_CompWaterTanks2TankIOV_tgt'', ''Etgt''),
      (''E_CompWaterTanks2Drain_src'', ''Esrc''), 
      (''E_CompWaterTanks2Drain_tgt'', ''Etgt''),
      (''E_WaterTanks1_wout'', ''EBlockProps''),
      (''E_WaterTanks2_win'', ''EBlockProps''),
      (''E_WaterTanks2_wlout'', ''EBlockProps''),
      (''E_WaterTanks2_vi'', ''EBlockProps''),
      (''E_Controller_wlin'', ''EBlockProps''),
      (''E_Controller_vo'', ''EBlockProps''),
      (''E_Inflow_wout'', ''EBlockProps''),
      (''E_Pipe_win'', ''EBlockProps''),
      (''E_Pipe_wout'', ''EBlockProps''),
      (''E_TankIO_win'', ''EBlockProps''),
      (''E_TankIO_wout'', ''EBlockProps''),
      (''E_TankIOV_win'', ''EBlockProps''),
      (''E_TankIOV_wout'', ''EBlockProps''),
      (''E_TankIOV_wlout'', ''EBlockProps''),
      (''E_TankIOV_vi'', ''EBlockProps''),
      (''E_Drain_win'', ''EBlockProps''),
      (''E_Dep_Pipe_wout_win'', ''EFlowPortDepends''),
      (''E_Dep_TankIO_wout_win'', ''EFlowPortDepends''),
      (''E_Dep_WaterTanks2_wlout_win'', ''EFlowPortDepends''),
      (''E_Dep_TankIOV_wlout_win'', ''EFlowPortDepends''),
      (''E_Dep_TankIOV_wout_win'', ''EFlowPortDepends''),
      (''E_Dep_TankIOV_wlout_win'', ''EFlowPortDepends''),
      (''E_Dep_TankIOV_wout_vi'', ''EFlowPortDepends''),
      (''E_Dep_Controller_vo_wlin'', ''EFlowPortDepends''),
      (''E_Dep_Drain_wout_win'', ''EFlowPortDepends'')]\<rparr>"


end