
(*  File:      'INTO_SysML_3WTs' 
    Description: The Three Water Tanks model of INTO-CPS deliverable D2.1a 
    Author:     Nuno Amálio
*)

theory INTO_SysML_3WTs
imports INTO_SysML_MM_Gbl INTO_SysML_ToPDG
  
begin

(*The ASD corresponding to the ASD of 3WTs*)
definition SG_ASD_3WTs :: "SGr_ls"
where
  "SG_ASD_3WTs = \<lparr>NsG=[''WaterTanksASD'', ''WaterTanksSys'', ''CompWaterTanksSys1'',
    ''CompWaterTanksSys2'', ''CompWaterTanksSys3'',
    ''TanksControl1'', 
    ''TanksControl2'', ''CompTanksControl1Valve'', ''CompTanksControl1WaterTank'', 
    ''CompTanksControl2WaterTank'',
    ''Controller'',
    ''Valve'', ''WaterTank'', ''FlowRate'', ''Area'', ''Height'', ''OpenClosed'',
    ''WaterTank_win'', ''WaterTank_wout'', ''Valve_v2'', ''Valve_w'', 
    ''Controller_v1''], 
      EsG = [''EWaterTanksASD_WaterTanksSys'', ''EWaterTanksASD_TanksControl1'', 
        ''EWaterTanksASD_TanksControl2'', ''EWaterTanksASD_Valve'', 
        ''EWaterTanksASD_WaterTank'', ''EWaterTanksASD_FlowRate'', 
        ''EWaterTanksASD_Area'', 
        ''EWaterTanksASD_Height'', 
        ''EWaterTanksASD_OpenClosed'',
        ''ECompWaterTanksSys1_src'', ''ECompWaterTanksSys2_src'', 
        ''ECompWaterTanksSys3_src'', ''ECompWaterTanksSys1_tgt'',   
        ''ECompWaterTanksSys2_tgt'', 
        ''ECompWaterTanksSys3_tgt'', 
        ''ECompTanksControl1Valve_src'', 
        ''ECompTanksControl1WaterTank_src'', 
        ''ECompTanksControl2WaterTank_src'', 
        ''ECompTanksControl1Valve_tgt'',
        ''ECompTanksControl1WaterTank_tgt'', 
        ''ECompTanksControl2WaterTank_tgt'', 
        ''E_WaterTank_win'', ''E_WaterTank_wout'', ''E_Valve_v2'', 
        ''E_Valve_w'', ''E_Controller_v1'', ''E_Dep_w_v2'',
        ''E_Dep_wout_win''], 
      srcG =  [(''EWaterTanksASD_WaterTanksSys'', ''WaterTanksASD''), 
        (''EWaterTanksASD_TanksControl1'', ''WaterTanksASD''),
        (''EWaterTanksASD_TanksControl2'', ''WaterTanksASD''),
        (''EWaterTanksASD_Valve'', ''WaterTanksASD''),
        (''EWaterTanksASD_WaterTank'', ''WaterTanksASD''),
        (''EWaterTanksASD_FlowRate'', ''WaterTanksASD''),
        (''EWaterTanksASD_Area'', ''WaterTanksASD''),
        (''EWaterTanksASD_Height'',  ''WaterTanksASD''),
        (''EWaterTanksASD_OpenClosed'', ''WaterTanksASD''),
        (''ECompWaterTanksSys1_src'', ''CompWaterTanksSys1''), 
        (''ECompWaterTanksSys2_src'', ''CompWaterTanksSys2''), 
        (''ECompWaterTanksSys3_src'', ''CompWaterTanksSys3''),
        (''ECompWaterTanksSys1_tgt'', ''CompWaterTanksSys1''),
        (''ECompWaterTanksSys2_tgt'', ''CompWaterTanksSys2''),
        (''ECompWaterTanksSys3_tgt'', ''CompWaterTanksSys3''),
        (''ECompTanksControl1Valve_src'', ''CompTanksControl1Valve''),
        (''ECompTanksControl1WaterTank_src'', ''CompTanksControl1WaterTank''),
        (''ECompTanksControl2WaterTank_src'', ''CompTanksControl2WaterTank''),
        (''ECompTanksControl1Valve_tgt'', ''CompTanksControl1Valve''),
        (''ECompTanksControl1WaterTank_tgt'', ''CompTanksControl1WaterTank''),
        (''ECompTanksControl2WaterTank_tgt'', ''CompTanksControl2WaterTank''),
        (''E_WaterTank_win'', ''WaterTank''), (''E_WaterTank_wout'', ''WaterTank''),
        (''E_Valve_v2'', ''Valve''), (''E_Valve_w'', ''Valve''), 
        (''E_Controller_v1'', ''Controller''),
        (''E_Dep_w_v2'', ''Valve_w''), 
        (''E_Dep_wout_win'', ''WaterTank_wout'')], 
      tgtG =  [(''EWaterTanksASD_WaterTanksSys'', ''WaterTanksSys''), 
        (''EWaterTanksASD_TanksControl1'', ''TanksControl1''),
        (''EWaterTanksASD_TanksControl2'', ''TanksControl2''),
        (''EWaterTanksASD_Valve'', ''Valve''),
        (''EWaterTanksASD_WaterTank'', ''WaterTank''),
        (''EWaterTanksASD_FlowRate'', ''FlowRate''),
        (''EWaterTanksASD_Area'', ''Area''),
        (''EWaterTanksASD_Height'',  ''Height''),
        (''EWaterTanksASD_OpenClosed'', ''OpenClosed''),
        (''ECompWaterTanksSys1_src'', ''WaterTanksSys''), 
        (''ECompWaterTanksSys2_src'', ''WaterTanksSys''), 
        (''ECompWaterTanksSys3_src'', ''WaterTanksSys''),
        (''ECompWaterTanksSys1_tgt'', ''TanksControl1''),
        (''ECompWaterTanksSys2_tgt'', ''TanksControl2''),
        (''ECompWaterTanksSys3_tgt'', ''Controller''),
        (''ECompTanksControl1Valve_src'', ''TanksControl1''),
        (''ECompTanksControl1WaterTank_src'', ''TanksControl1''),
        (''ECompTanksControl2WaterTank_src'', ''TanksControl2''),
        (''ECompTanksControl1Valve_tgt'', ''Valve''),
        (''ECompTanksControl1WaterTank_tgt'', ''WaterTank''),
        (''ECompTanksControl2WaterTank_tgt'', ''WaterTank''),
        (''E_WaterTank_win'', ''WaterTank_win''), 
        (''E_WaterTank_wout'', ''WaterTank_wout''),
        (''E_Valve_v2'', ''Valve_v2''), (''E_Valve_w'', ''Valve_w''), 
        (''E_Controller_v1'', ''Controller_v1''),
        (''E_Dep_w_v2'', ''Valve_v2''), (''E_Dep_wout_win'', ''WaterTank_win'')],
      ntyG =[(''WaterTanksASD'', nnrml), (''WaterTanksSys'',  nnrml), 
        (''CompWaterTanksSys1'', nnrml), (''CompWaterTanksSys2'', nnrml),
        (''CompWaterTanksSys3'', nnrml), (''CompTanksControl1Valve'', nnrml), 
        (''CompTanksControl1WaterTank'', nnrml), 
        (''CompTanksControl2WaterTank'', nnrml), 
        (''TanksControl1'', nnrml), 
        (''TanksControl2'', nnrml), (''Controller'', nnrml),
        (''Valve'', nnrml), (''WaterTank'', nnrml), (''FlowRate'', nnrml),
        (''Area'', nnrml), (''Height'', nnrml), (''OpenClosed'', nnrml),
        (''WaterTank_win'', nnrml), 
        (''WaterTank_wout'', nnrml),
        (''Valve_v2'', nnrml), 
        (''Valve_w'', nnrml), 
        (''Controller_v1'', nnrml)],
      etyG =[(''EWaterTanksASD_WaterTanksSys'', elnk), 
        (''EWaterTanksASD_TanksControl1'', elnk),
        (''EWaterTanksASD_TanksControl2'', elnk),
        (''EWaterTanksASD_Valve'', elnk),
        (''EWaterTanksASD_WaterTank'', elnk),
        (''EWaterTanksASD_FlowRate'', elnk),
        (''EWaterTanksASD_Area'', elnk),
        (''EWaterTanksASD_Height'',  elnk),
        (''EWaterTanksASD_OpenClosed'', elnk),
        (''ECompWaterTanksSys1_src'', ecompuni), 
        (''ECompWaterTanksSys2_src'', ecompuni), 
        (''ECompWaterTanksSys3_src'', ecompuni),
        (''ECompWaterTanksSys1_tgt'', ecompuni),
        (''ECompWaterTanksSys2_tgt'', ecompuni),
        (''ECompWaterTanksSys3_tgt'', ecompuni), 
        (''ECompTanksControl1Valve_src'', ecompuni),
        (''ECompTanksControl1WaterTank_src'', ecompuni),
        (''ECompTanksControl2WaterTank_src'', ecompuni),
        (''ECompTanksControl1Valve_tgt'', ecompuni),
        (''ECompTanksControl1WaterTank_tgt'', ecompuni),
        (''ECompTanksControl2WaterTank_tgt'', ecompuni),
        (''E_WaterTank_win'', elnk), 
        (''E_WaterTank_wout'', elnk),
        (''E_Valve_v2'', elnk), 
        (''E_Valve_w'', elnk), 
        (''E_Controller_v1'', elnk), (''E_Dep_w_v2'', elnk),
        (''E_Dep_wout_win'', elnk)],
      srcmG = [], 
      tgtmG = [(''ECompWaterTanksSys1_src'', sm (val 1)), 
        (''ECompWaterTanksSys2_src'', sm (val 1)), 
        (''ECompWaterTanksSys3_src'', sm (val 1)), 
        (''ECompWaterTanksSys1_tgt'', sm (val 1)), 
        (''ECompWaterTanksSys2_tgt'', sm (val 1)), 
        (''ECompWaterTanksSys3_tgt'', sm (val 1)), 
        (''ECompTanksControl1Valve_src'', sm (val 1)),
        (''ECompTanksControl1WaterTank_src'', sm (val 1)), 
        (''ECompTanksControl2WaterTank_src'', sm (val 1)),
        (''ECompTanksControl1Valve_tgt'', sm (val 1)),
        (''ECompTanksControl1WaterTank_tgt'', sm (val 1)), 
        (''ECompTanksControl2WaterTank_tgt'', sm (val 2))]\<rparr>"

axiomatization
where
  Es_SG_ASD_3WTs: "Es (toSGr SG_ASD_3WTs) \<subseteq> E_A"
  and Ns_SG_ASD_3WTs: "Ns (toSGr SG_ASD_3WTs) \<subseteq> V_A"

value "consInh SG_ASD_3WTs"

lemma wf_SG_ASD_3WTs: "is_wf_sg (toSGr SG_ASD_3WTs)"
  proof -
    have h_wf_g: "is_wf_g (toSGr SG_ASD_3WTs)"
      proof (simp add: is_wf_g_def, rule conjI)
        show "Ns (toSGr SG_ASD_3WTs) \<subseteq> V_A"
          using Ns_SG_ASD_3WTs by simp
      next
        apply_end(rule conjI)
        show "Es (toSGr SG_ASD_3WTs) \<subseteq> E_A"
          using Es_SG_ASD_3WTs by simp
      next
        apply_end(rule conjI)
        show "ftotal_on (src (toSGr SG_ASD_3WTs)) (Es (toSGr SG_ASD_3WTs)) (Ns (toSGr SG_ASD_3WTs))"
          by (simp add: ftotal_on_def toSGr_def SG_ASD_3WTs_def)
      next
        show "ftotal_on (tgt (toSGr SG_ASD_3WTs)) (Es (toSGr SG_ASD_3WTs)) (Ns (toSGr SG_ASD_3WTs))"
          by (simp add: ftotal_on_def toSGr_def SG_ASD_3WTs_def)
      qed
    have ftotal_on_ety: "ftotal_on (ety (toSGr SG_ASD_3WTs)) (Es (toSGr SG_ASD_3WTs)) SGETy_set"
      by (simp add: ftotal_on_def SGNTy_set_def SG_ASD_3WTs_def toSGr_def SGETy_set_def)
    show ?thesis
    proof (simp add: is_wf_sg_def, rule conjI)
      show "is_wf_g (toSGr SG_ASD_3WTs)"
        using h_wf_g by simp
    next
      apply_end(rule conjI)
      show "ftotal_on (nty (toSGr SG_ASD_3WTs)) (Ns (toSGr SG_ASD_3WTs)) SGNTy_set"
        by (auto simp add: ftotal_on_def SGNTy_set_def SG_ASD_3WTs_def toSGr_def)
    next
      apply_end(rule conjI) 
      show "ftotal_on (ety (toSGr SG_ASD_3WTs)) (Es (toSGr SG_ASD_3WTs)) SGETy_set"
        by (simp add: ftotal_on_ety)
    next
      apply_end(rule conjI) 
      show "dom (srcm (toSGr SG_ASD_3WTs)) = EsTy (toSGr SG_ASD_3WTs) {Some erelbi, Some ecompbi}"
        by (simp add: SG_ASD_3WTs_def toSGr_def EsTy_def vimage_def)
    next
      apply_end(rule conjI) 
      show "dom (tgtm (toSGr SG_ASD_3WTs)) = EsTy (toSGr SG_ASD_3WTs) {Some erelbi, Some ereluni, Some ecompbi, Some ecompuni}"
        by (rule equalityI, rule subsetI, 
          auto simp add: SG_ASD_3WTs_def toSGr_def EsTy_def vimage_def)
    next
      apply_end(rule conjI)
      show "EsR (toSGr SG_ASD_3WTs) \<subseteq> EsId (toSGr SG_ASD_3WTs)"
        using h_wf_g ftotal_on_ety by (simp add: EsId_eq_EsIdL EsR_eq_EsRL)(eval)
    next
      apply_end(rule conjI)
      show "srcm (toSGr SG_ASD_3WTs) ` EsTy (toSGr SG_ASD_3WTs) {Some ecompbi}
        \<subseteq> {Some (rm 0 (val (Suc 0))), Some (sm (val (Suc 0)))}"
        by (simp add: toSGr_def image_def SG_ASD_3WTs_def EsTy_def)
    next
      show "acyclicGr (inhG (toSGr SG_ASD_3WTs))"
        using h_wf_g by (simp add: inh_eq acyclicGr_def rtrancl_in inh_eq_consInh)(eval)
    qed
  qed

(*'F_CD' Fragment*)
definition F_ASD_3WTs :: "Fr_ls"
where
   "F_ASD_3WTs \<equiv> \<lparr>sg_ls = SG_ASD_3WTs, 
    tr_ls = []\<rparr>"

value "consRefs F_ASD_3WTs"

value "EsRPL SG_ASD_3WTs"

(* Well-formedness proof obligation of fragments"*)
lemma wf_F_ASD_3WTs: "is_wf_fr (toFr F_ASD_3WTs)"
  proof -
    let ?refs_F_ASD_3WTs = "{}"
    have EsRP_ASD_3WTs: "EsRP (sg (toFr F_ASD_3WTs)) = {}"
      using wf_SG_ASD_3WTs by (simp add: EsRP_eq_EsRPL toFr_def F_ASD_3WTs_def, eval)
    have h_ftotal_tr: "ftotal_on (tr (toFr F_ASD_3WTs)) (EsRP (sg (toFr F_ASD_3WTs))) V_A"
      proof (simp add: ftotal_on_def)
        apply_end(rule conjI)
        show "dom (tr (toFr F_ASD_3WTs)) = EsRP (sg (toFr F_ASD_3WTs))"
        proof
          show "dom (tr (toFr F_ASD_3WTs)) \<subseteq> EsRP (sg (toFr F_ASD_3WTs))"
            by (simp add: F_ASD_3WTs_def SG_ASD_3WTs_def toSGr_def toFr_def  
          SG_F_Props_def EsRP_def EsR_def NsP_def EsTy_def NsTy_def) 
        next
          show "EsRP (sg (toFr F_ASD_3WTs)) \<subseteq> dom (tr (toFr F_ASD_3WTs))"
            by (simp add: EsRP_ASD_3WTs)
        qed
      next
        show "ran (tr (toFr F_ASD_3WTs)) \<subseteq> V_A"
        using Ns_SG_F_ASD Ns_SG_F_Comps Ns_SG_F_Blocks Ns_SG_F_Common Ns_SG_F_VTypes
        by (simp add: F_ASD_3WTs_def SG_ASD_3WTs_def toSGr_def toFr_def SG_F_Comps_def 
          SG_F_Blocks_def F_Common_def SG_F_Common_def F_VTypes_def SG_F_VTypes_def)
      qed
      from wf_SG_ASD_3WTs have hb: "is_wf_sg (sg (toFr F_ASD_3WTs))"
      by (simp add: toFr_def F_ASD_3WTs_def)
    have refs_F_ASD_3WTs: "refs (toFr F_ASD_3WTs) = ?refs_F_ASD_3WTs"
      using h_ftotal_tr hb by (simp add: refs_eq_consRefs, eval)
    show ?thesis
    proof (simp add: is_wf_fr_def)
      apply_end(rule conjI)
      show "is_wf_sg (sg (toFr F_ASD_3WTs))"  
        by (simp add: wf_SG_ASD_3WTs toFr_def F_ASD_3WTs_def)
    next
      apply_end(rule conjI) 
      show "ftotal_on (tr (toFr F_ASD_3WTs)) (EsRP (sg (toFr F_ASD_3WTs))) V_A"
        by (simp add: h_ftotal_tr)
    next
      apply_end(rule conjI)  
      show "inj_on (src (sg (toFr F_ASD_3WTs))) (EsRP (sg (toFr F_ASD_3WTs)))"
        by (simp add: EsRP_ASD_3WTs) 
    next
      apply_end(rule conjI)  
      show "ran (src (sg (toFr F_ASD_3WTs)) |` EsRP (sg (toFr F_ASD_3WTs))) = NsP (sg (toFr F_ASD_3WTs))"
        by (simp add: EsRP_ASD_3WTs)(simp add: F_ASD_3WTs_def restrict_map_def NsP_def NsTy_def 
          toFr_def SG_ASD_3WTs_def  toSGr_def vimage_def)
    next
      apply_end(rule conjI)
      show "\<forall>v. v \<in> NsP (sg (toFr F_ASD_3WTs)) \<longrightarrow> nonPRefsOf (toFr F_ASD_3WTs) v \<noteq> {}"
        by (simp add: NsP_def NsTy_def nonPRefsOf_def refsOf_def refs_F_ASD_3WTs)
          (simp add: F_ASD_3WTs_def SG_ASD_3WTs_def toFr_def toSGr_def)
    next
      apply_end(rule conjI)
      have h_wf_g: "is_wf_g (toSGr SG_ASD_3WTs)"
        using wf_SG_ASD_3WTs
        by (simp add: is_wf_sg_def)
      show "acyclic_fr (toFr F_ASD_3WTs)"
        using  h_wf_g by (simp add: acyclic_fr_def refs_F_ASD_3WTs)
          (simp add: inh_eq rtrancl_in inh_eq_consInh F_ASD_3WTs_def toFr_def, eval)
    next
      show "proxies_dont_inherit (toFr F_ASD_3WTs)"
        by (simp add: proxies_dont_inherit_def restrict_map_def NsP_def NsTy_def
          F_ASD_3WTs_def toFr_def vimage_def SG_ASD_3WTs_def toSGr_def)
    qed
  qed

(*Define a model*. Update this later to conver connections*)
definition SG_CD_3WTs :: "SGr_ls"
where
  "SG_CD_3WTs = \<lparr>
    NsG=[''PrWaterTank'', ''PrValve'', ''PrTanksControl1'', 
      ''PrTanksControl2'', ''PrController'', ''CD_3WTs'', ''WTSys'',
      ''V'', ''WT1'', ''WT2'', ''WT3'', ''C'',
      ''TC1'', ''TC2'', ''v1'', ''v2'', ''w'', ''win1'', ''wout1'', ''win2'', 
      ''wout2'', ''win3'', ''wout3'', ''C_w_win1'', ''C_wout1_win2'', ''C_wout2_win3'',
      ''C_v1_v2'', ''PrValve_v2'', ''PrValve_w'', ''PrWaterTank_win'', 
      ''PrWaterTank_wout'', ''PrController_v1''], 
    EsG = [''ECD_WTSys'', ''ECD_V'', ''ECD_WT1'', ''ECD_WT2'', ''ECD_WT3'',   
      ''ECD_C'', ''ECD_TC1'', ''ECD_TC2'', ''ECD_C_v1_v2'', ''ECD_C_w_win1'', 
      ''ECD_C_wout1_win2'', ''ECD_C_wout2_win3'', 
      ''E_C_v1'', ''E_V_v2'', ''E_V_w'',  ''E_WT1_win1'', ''E_WT1_wout1'', 
      ''E_WT2_win2'', ''E_WT2_wout2'', ''E_WT3_win3'', ''E_WT3_wout3'',
      ''E_C_v1_v2_src'', ''E_C_v1_v2_tgt'', ''E_C_w_win1_src'', ''E_C_w_win1_tgt'', 
      ''E_C_wout1_win2_src'', ''E_C_wout1_win2_tgt'', 
      ''E_C_wout2_win3_src'', ''E_C_wout2_win3_tgt'', 
      ''ETC1_V'', ''ETC1_WT1'', ''ETC2_WT2'',
      ''ETC2_WT3'', ''EWTSys_TC1'', ''EWTSys_TC2'', ''EWTSys_C'', 
      ''E_v1_ty'', ''E_v2_ty'', ''E_w_ty'', ''E_win1_ty'', ''E_wout1_ty'',
      ''E_win2_ty'', ''E_wout2_ty'', ''E_win3_ty'', ''E_wout3_ty'',
      ''ERPrWaterTank'', ''ERPrValve'', ''ERPrTanksControl1'', ''ERPrTanksControl2'', 
      ''ERPrController'', ''ERPrValve_v2'', ''ERPrValve_w'', ''ERPrWaterTank_win'',
      ''ERPrWaterTank_wout'', ''ERPrController_v1''], 
    srcG =  [
      (''ECD_WTSys'', ''CD_3WTs''), (''ECD_V'', ''CD_3WTs''), 
      (''ECD_WT1'', ''CD_3WTs''), (''ECD_WT2'', ''CD_3WTs''),
      (''ECD_WT3'', ''CD_3WTs''), (''ECD_C'', ''CD_3WTs''),
      (''ECD_TC1'', ''CD_3WTs''), (''ECD_TC2'', ''CD_3WTs''),
      (''ECD_C_v1_v2'', ''CD_3WTs''), (''ECD_C_w_win1'', ''CD_3WTs''),
      (''ECD_C_wout1_win2'', ''CD_3WTs''), (''ECD_C_wout2_win3'', ''CD_3WTs''),
      (''E_C_v1'', ''C''),
      (''E_V_v2'', ''V''), (''E_V_w'', ''V''),  
      (''E_WT1_win1'', ''WT1''), (''E_WT1_wout1'', ''WT1''), 
      (''E_WT2_win2'', ''WT2''), (''E_WT2_wout2'', ''WT2''), 
      (''E_WT3_win3'', ''WT3''), (''E_WT3_wout3'', ''WT3''),
      (''E_C_v1_v2_src'', ''C_v1_v2''), (''E_C_v1_v2_tgt'', ''C_v1_v2''),
      (''E_C_w_win1_src'', ''C_w_win1''), (''E_C_w_win1_tgt'', ''C_w_win1''),
      (''E_C_wout1_win2_src'', ''C_wout1_win2''), (''E_C_wout1_win2_tgt'', ''C_wout1_win2''), 
      (''E_C_wout2_win3_src'', ''C_wout2_win3''), (''E_C_wout2_win3_tgt'', ''C_wout2_win3''),
      (''ETC1_V'', ''TC1''),
      (''ETC1_WT1'', ''TC1''), (''ETC2_WT2'', ''TC2''),
      (''ETC2_WT3'', ''TC2''), (''EWTSys_TC1'', ''WTSys''), 
      (''EWTSys_TC2'', ''WTSys''), (''EWTSys_C'', ''WTSys''),
      (''E_v1_ty'', ''v1''), (''E_v2_ty'', ''v2''), 
      (''E_w_ty'', ''w''), (''E_win1_ty'', ''win1''), 
      (''E_wout1_ty'', ''wout1''),
      (''E_win2_ty'', ''win2''), (''E_wout2_ty'', ''wout2''), 
      (''E_win3_ty'', ''win3''), (''E_wout3_ty'', ''wout3''),
      (''ERPrWaterTank'', ''PrWaterTank''), (''ERPrValve'', ''PrValve''), 
      (''ERPrTanksControl1'', ''PrTanksControl1''), 
      (''ERPrTanksControl2'', ''PrTanksControl2''),
      (''ERPrController'', ''PrController''),
      (''ERPrValve_v2'', ''PrValve_v2''), (''ERPrValve_w'', ''PrValve_w''), 
      (''ERPrWaterTank_win'', ''PrWaterTank_win''),
      (''ERPrWaterTank_wout'', ''PrWaterTank_wout''), 
      (''ERPrController_v1'', ''PrController_v1'')], 
    tgtG =  [
      (''ECD_WTSys'', ''WTSys''), (''ECD_V'', ''V''), 
      (''ECD_WT1'', ''WT1''), (''ECD_WT2'', ''WT2''),
      (''ECD_WT3'', ''WT3''), (''ECD_C'', ''C''),
      (''ECD_TC1'', ''TC1''), (''ECD_TC2'', ''TC2''),
      (''ECD_C_v1_v2'', ''C_v1_v2''), (''ECD_C_w_win1'', ''C_w_win1''),
      (''ECD_C_wout1_win2'', ''C_wout1_win2''), 
      (''ECD_C_wout2_win3'', ''C_wout2_win3''),
      (''E_C_v1'', ''v1''),
      (''E_V_v2'', ''v2''), (''E_V_w'', ''w''),  
      (''E_WT1_win1'', ''win1''), (''E_WT1_wout1'', ''wout1''), 
      (''E_WT2_win2'', ''win2''), (''E_WT2_wout2'', ''wout2''), 
      (''E_WT3_win3'', ''win3''), (''E_WT3_wout3'', ''wout3''),
      (''E_C_v1_v2_src'', ''v1''), (''E_C_v1_v2_tgt'', ''v2''),
      (''E_C_w_win1_src'', ''w''), (''E_C_w_win1_tgt'', ''win1''),
      (''E_C_wout1_win2_src'', ''wout1''), (''E_C_wout1_win2_tgt'', ''win2''), 
      (''E_C_wout2_win3_src'', ''wout2''), (''E_C_wout2_win3_tgt'', ''win3''),
      (''ETC1_V'', ''V''),
      (''ETC1_WT1'', ''WT1''), (''ETC2_WT2'', ''WT2''),
      (''ETC2_WT3'', ''WT3''), (''EWTSys_TC1'', ''TC1''), 
      (''EWTSys_TC2'', ''TC2''), (''EWTSys_C'', ''C''),
      (''E_v1_ty'', ''PrController_v1''), (''E_v2_ty'', ''PrValve_v2''), 
      (''E_w_ty'', ''PrValve_w''), (''E_win1_ty'', ''PrWaterTank_win''), 
      (''E_wout1_ty'', ''PrWaterTank_wout''),
      (''E_win2_ty'', ''PrWaterTank_win''), (''E_wout2_ty'', ''PrWaterTank_wout''), 
      (''E_win3_ty'', ''PrWaterTank_win''), (''E_wout3_ty'', ''PrWaterTank_wout''),
      (''ERPrWaterTank'', ''PrWaterTank''), (''ERPrValve'', ''PrValve''), 
      (''ERPrTanksControl1'', ''PrTanksControl1''), 
      (''ERPrTanksControl2'', ''PrTanksControl2''),
      (''ERPrController'', ''PrController''),
      (''ERPrValve_v2'', ''PrValve_v2''), (''ERPrValve_w'', ''PrValve_w''), 
      (''ERPrWaterTank_win'', ''PrWaterTank_win''),
      (''ERPrWaterTank_wout'', ''PrWaterTank_wout''), 
      (''ERPrController_v1'', ''PrController_v1'')],
   ntyG =[(''PrWaterTank'',  nprxy), (''PrValve'', nprxy), 
        (''PrTanksControl1'', nprxy), (''PrTanksControl2'', nprxy),
        (''PrController'', nprxy), (''CD_3WTs'',  nnrml),
        (''WTSys'', nnrml), (''V'', nnrml),
        (''WT1'', nnrml), (''WT2'', nnrml), (''WT3'', nnrml), 
        (''C'', nnrml), (''TC1'', nnrml), (''TC2'', nnrml), 
        (''v1'', nnrml), (''v2'', nnrml), (''w'', nnrml), (''win1'', nnrml),
        (''wout1'', nnrml), (''win2'', nnrml), (''wout2'', nnrml), 
        (''win3'', nnrml), (''wout3'', nnrml),
        (''C_w_win1'', nnrml), (''C_wout1_win2'', nnrml), 
        (''C_wout2_win3'', nnrml), (''C_v1_v2'', nnrml), 
        (''PrValve_v2'', nprxy), (''PrValve_w'', nprxy), 
        (''PrWaterTank_win'', nprxy),
        (''PrWaterTank_wout'', nprxy), (''PrController_v1'', nprxy)],
      etyG =[
        (''ECD_WTSys'', elnk), (''ECD_V'', elnk), 
        (''ECD_WT1'', elnk), (''ECD_WT2'', elnk),
        (''ECD_WT3'', elnk), (''ECD_C'', elnk),
        (''ECD_TC1'', elnk), (''ECD_TC2'', elnk),
        (''ECD_C_v1_v2'', elnk), (''ECD_C_w_win1'', elnk),
        (''ECD_C_wout1_win2'', elnk), 
        (''ECD_C_wout2_win3'', elnk),
        (''E_C_v1'', elnk),
        (''E_V_v2'', elnk), (''E_V_w'', elnk),  
        (''E_WT1_win1'', elnk), (''E_WT1_wout1'', elnk), 
        (''E_WT2_win2'', elnk), (''E_WT2_wout2'', elnk), 
        (''E_WT3_win3'', elnk), (''E_WT3_wout3'', elnk),
        (''E_C_v1_v2_src'', elnk), (''E_C_v1_v2_tgt'', elnk),
        (''E_C_w_win1_src'', elnk), (''E_C_w_win1_tgt'', elnk),
        (''E_C_wout1_win2_src'', elnk), (''E_C_wout1_win2_tgt'', elnk), 
        (''E_C_wout2_win3_src'', elnk), (''E_C_wout2_win3_tgt'', elnk),
        (''ETC1_V'', elnk),
        (''ETC1_WT1'', elnk), (''ETC2_WT2'', elnk),
        (''ETC2_WT3'', elnk), (''EWTSys_TC1'', elnk), 
        (''EWTSys_TC2'', elnk), 
        (''EWTSys_C'', elnk), 
        (''E_v1_ty'', elnk), (''E_v2_ty'', elnk), 
        (''E_w_ty'', elnk), (''E_win1_ty'', elnk), 
        (''E_wout1_ty'', elnk),
        (''E_win2_ty'', elnk), (''E_wout2_ty'', elnk), 
        (''E_win3_ty'', elnk), (''E_wout3_ty'', elnk),
        (''ERPrWaterTank'', eref), (''ERPrValve'', eref), 
        (''ERPrTanksControl1'', eref), 
        (''ERPrTanksControl2'', eref),
        (''ERPrController'', eref), 
        (''ERPrValve_v2'', eref), (''ERPrValve_w'', eref), 
        (''ERPrWaterTank_win'', eref),
        (''ERPrWaterTank_wout'', eref), 
        (''ERPrController_v1'', eref)],
      srcmG = [], 
      tgtmG = []\<rparr>"

axiomatization
where
  Es_SG_CD_3WTs: "Es (toSGr SG_CD_3WTs) \<subseteq> E_A"
  and Ns_SG_CD_3WTs: "Ns (toSGr SG_CD_3WTs) \<subseteq> V_A"

value "consInh SG_CD_3WTs"

lemma wf_SG_CD_3WTs: "is_wf_sg (toSGr SG_CD_3WTs)"
  proof -
    have h_wf_g: "is_wf_g (toSGr SG_CD_3WTs)"
    proof (simp add: is_wf_g_def, rule conjI)
      show "Ns (toSGr SG_CD_3WTs) \<subseteq> V_A"
      using Ns_SG_CD_3WTs by (simp add: SG_CD_3WTs_def)
    next
      apply_end(rule conjI)
      show "Es (toSGr SG_CD_3WTs) \<subseteq> E_A"
      using Es_SG_CD_3WTs by (simp add: SG_CD_3WTs_def)
    next
      apply_end(rule conjI)
      show "ftotal_on (src (toSGr SG_CD_3WTs)) (Es (toSGr SG_CD_3WTs)) (Ns (toSGr SG_CD_3WTs))"
      by (simp add: SG_CD_3WTs_def ftotal_on_def toSGr_def)
    next
      show "ftotal_on (tgt (toSGr SG_CD_3WTs)) (Es (toSGr SG_CD_3WTs)) (Ns (toSGr SG_CD_3WTs))"
      by (simp add: SG_CD_3WTs_def ftotal_on_def toSGr_def)
    qed   
    have ftotal_ety: "ftotal_on (ety (toSGr SG_CD_3WTs)) (Es (toSGr SG_CD_3WTs)) SGETy_set"
      by (simp add: ftotal_on_def, rule conjI, rule equalityI)
        (simp_all add: SGNTy_set_def SG_CD_3WTs_def toSGr_def SGETy_set_def)
    show ?thesis
    proof (simp add: is_wf_sg_def, rule conjI)
      show "is_wf_g (toSGr SG_CD_3WTs)"
        using h_wf_g by simp
    next
      apply_end(rule conjI)
      show "ftotal_on (nty (toSGr SG_CD_3WTs)) (Ns (toSGr SG_CD_3WTs)) SGNTy_set"
        by (simp add: ftotal_on_def SGNTy_set_def SG_CD_3WTs_def toSGr_def)
    next
      apply_end(rule conjI) 
      show "ftotal_on (ety (toSGr SG_CD_3WTs)) (Es (toSGr SG_CD_3WTs)) SGETy_set"
        by (simp add: ftotal_ety)
    next
      apply_end(rule conjI) 
      show "dom (srcm (toSGr SG_CD_3WTs)) = EsTy (toSGr SG_CD_3WTs) {Some erelbi, Some ecompbi}"
        by (simp add: SG_CD_3WTs_def toSGr_def EsTy_def vimage_def)
    next
      apply_end(rule conjI) 
      show "dom (tgtm (toSGr SG_CD_3WTs)) = EsTy (toSGr SG_CD_3WTs) {Some erelbi, Some ereluni, Some ecompbi, Some ecompuni}"
        by (auto simp add: SG_CD_3WTs_def toSGr_def EsTy_def vimage_def)
    next
      apply_end(rule conjI)
      show "EsR (toSGr SG_CD_3WTs) \<subseteq> EsId (toSGr SG_CD_3WTs)"
        using h_wf_g ftotal_ety by (simp add: EsId_eq_EsIdL EsR_eq_EsRL)(eval)
    next
      apply_end(rule conjI)
      show "srcm (toSGr SG_CD_3WTs) ` EsTy (toSGr SG_CD_3WTs) {Some ecompbi}
        \<subseteq> {Some (rm 0 (val (Suc 0))), Some (sm (val (Suc 0)))}"
        by (simp add: toSGr_def image_def SG_CD_3WTs_def EsTy_def)
    next
      show "acyclicGr (inhG (toSGr SG_CD_3WTs))"
        using h_wf_g by (simp add: inh_eq acyclicGr_def rtrancl_in inh_eq_consInh)(eval)
    qed
  qed

(*'F_CD' Fragment*)
definition F_CD_3WTs :: "Fr_ls"
where
   "F_CD_3WTs \<equiv> \<lparr>sg_ls = SG_CD_3WTs, 
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
      using wf_SG_CD_3WTs by (simp add: EsRP_eq_EsRPL toFr_def F_CD_3WTs_def, eval)
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

value "INTO_SysML_toPDG MdlTy_3WTs"

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

value "consClanF ''PrController_v1'' (consUMdlFs (mdlL MdlTy_3WTs))"

fun internalConnectionsOf :: "Mdl_ls \<Rightarrow> Morph \<Rightarrow> V \<Rightarrow> Gr_ls"
where
  "internalConnectionsOf ML m v = buildGrForInternalPortConnections m (consUMdlFs ML) v"

value "buildGrForConnector (toMorph (mtyL MdlTy_3WTs)) (consUMdlFs (mdlL MdlTy_3WTs)) ''C_w_win1''"
value "internalConnectionsOf (mdlL MdlTy_3WTs) (toMorph (mtyL MdlTy_3WTs)) ''w''"

end