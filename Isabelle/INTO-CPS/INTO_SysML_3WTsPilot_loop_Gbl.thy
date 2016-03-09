
(*  File:      'INTO_SysML_3WTsPilot_Gbl' 
    Description: Global enconding of the INTO-SysML model of pilot case study of 3 Water tanks 
    Author:     Nuno Amálio
*)

theory INTO_SysML_3WTsPilot_loop_Gbl
imports INTO_SysML_3WTsPilot_loop_CD INTO_SysML_ToPDG
  
begin

definition GFG_3WTsP_loop :: "GFGr_ls"
where
  "GFG_3WTsP_loop \<equiv> 
    \<lparr>NsG = [''F_ASD_3WTsP_loop'', ''F_CD_3WTsP_loop''], 
      EsG= [''E_F_CD_3WTsP_loop_ASD'', ''E_F_ASD_3WTsP_loop'', ''E_F_CD_3WTsP_loop''], 
      srcG = [(''E_F_CD_3WTsP_loop_ASD'', ''F_CD_3WTsP_loop''), 
        (''E_F_ASD_3WTsP_loop'', ''F_ASD_3WTsP_loop''),
        (''E_F_CD_3WTsP_loop'', ''F_CD_3WTsP_loop'')],
      tgtG = [(''E_F_CD_3WTsP_loop_ASD'', ''F_ASD_3WTsP_loop''), 
        (''E_F_ASD_3WTsP_loop'', ''F_ASD_3WTsP_loop''),
        (''E_F_CD_3WTsP_loop'', ''F_CD_3WTsP_loop'')],
      ext_ty_ls = [(''E_F_CD_3WTsP_loop_ASD'', eimp), (''E_F_ASD_3WTsP_loop'', eimp),
        (''E_F_CD_3WTsP_loop'', eimp)]\<rparr>"

axiomatization
where
  Es_GFG_3WTsP_loop: "Es (toGFGr(GFG_3WTsP_loop)) \<subseteq> E_A"
  and Ns_GFG_3WTsP_loop: "Ns (toGFGr(GFG_3WTsP_loop)) \<subseteq> V_A"

lemma is_wf_GFG_3WTs_loop: "is_wf_gfg_ls GFG_3WTsP_loop"
  proof -
    have h_wf_g: "is_wf_g (toGFGr GFG_3WTsP_loop)"
      using Es_GFG_3WTsP_loop Ns_GFG_3WTsP_loop
        by (simp add: is_wf_g_def GFG_3WTsP_loop_def ftotal_on_def toGFGr_def)
    show ?thesis
    proof (simp add: is_wf_gfg_ls_def, rule conjI)
      show "distinct (NsG GFG_3WTsP_loop)"
      by (simp add: GFG_3WTsP_loop_def)
    next
      apply_end(rule conjI)
      show "distinct (map fst (srcG GFG_3WTsP_loop))"
        by (simp add: GFG_3WTsP_loop_def)
    next
      apply_end(rule conjI)
      show "distinct (map fst (tgtG GFG_3WTsP_loop))"
        by (simp add: GFG_3WTsP_loop_def)
    next
      show "is_wf_gfg (toGFGr GFG_3WTsP_loop)"
        proof (simp add: is_wf_gfg_def, rule conjI)
          show "is_wf_g (toGFGr GFG_3WTsP_loop)"
            using h_wf_g by simp
        next
          apply_end (rule conjI)
          show "ftotal_on (ext_ty (toGFGr GFG_3WTsP_loop)) (Es (toGFGr GFG_3WTsP_loop)) GFGEdgeTy_set"
            by (simp add: GFG_3WTsP_loop_def toGFGr_def GFGEdgeTy_set_def ftotal_on_def)
        next
          apply_end (rule conjI)
          show "NodesWithSelfEdges (toGFGr GFG_3WTsP_loop)"
          proof (simp add: NodesWithSelfEdges_def, clarify)
            fix v
            assume "v \<in> Ns (toGFGr GFG_3WTsP_loop)"
            then have h1: "v = ''F_CD_3WTsP_loop'' \<or> v = ''F_ASD_3WTsP_loop''"
              by (auto simp add: GFG_3WTsP_loop_def toGFGr_def)
            then show "\<exists>e. e \<in> Es (toGFGr GFG_3WTsP_loop) 
              \<and> src (toGFGr GFG_3WTsP_loop) e = Some v 
              \<and> tgt (toGFGr GFG_3WTsP_loop) e = Some v"
            by (simp add:  GFG_3WTsP_loop_def toGFGr_def NodesWithSelfEdges_def)
              (erule disjE, simp, rule exI[where x="''E_F_ASD_3WTsP_loop''"], simp)
          qed
        next
          show "acyclicGr
            (restrict (toGFGr GFG_3WTsP_loop)
              (Es (toGFGr GFG_3WTsP_loop) - EsId (toGFGr GFG_3WTsP_loop)))"
          by (auto simp add: GFG_3WTsP_loop_def toGFGr_def EsId_def restrict_def acyclicGr_def
            relOfGr_def rst_Ns_def rst_fun_def adjacent_def acyclic_def elim: tranclE)
     qed
   qed
  qed

definition Mdl_3WTsP_loop :: "Mdl_ls"
where
  "Mdl_3WTsP_loop \<equiv> \<lparr>gfgL = GFG_3WTsP_loop, 
    frdL = [(''F_ASD_3WTsP_loop'', F_ASD_3WTsP_loop), (''F_CD_3WTsP_loop'', F_CD_3WTsP_loop)]\<rparr>"

lemma is_wf_mdl_3WTs_loop: "is_wf_mdl (toMdl Mdl_3WTsP_loop)"
  proof (simp add: is_wf_mdl_def, rule conjI)
    show "\<forall>F. F \<in> ran (frd (toMdl Mdl_3WTsP_loop)) \<longrightarrow> is_wf_fr F"
    proof (clarify)
      fix F
      assume "F \<in> ran (frd (toMdl Mdl_3WTsP_loop))"
      then have h1: "F = (toFr F_ASD_3WTsP_loop) \<or> F = (toFr F_CD_3WTsP_loop)"
        by (auto simp add: INTO_SysML_MM_def toMdl_def Mdl_3WTsP_loop_def)
      then show "is_wf_fr F"
      proof (case_tac "F = toFr F_ASD_3WTsP_loop")
        assume "F = toFr F_ASD_3WTsP_loop"
        then show "is_wf_fr F"
          by (simp add: wf_F_ASD_3WTsP_loop)
      next
        assume h2: "F \<noteq> toFr F_ASD_3WTsP_loop"
        then show "is_wf_fr F"
        proof (case_tac "F = toFr F_CD_3WTsP_loop")
          assume "F = toFr F_CD_3WTsP_loop"
          then show "is_wf_fr F"
            by (simp add: wf_F_CD_3WTs_loop)
        next
          assume h3: "F \<noteq> toFr F_CD_3WTsP_loop"
          then show "is_wf_fr F" using h1 h2 by (simp)
        qed
      qed
    qed
  next
    apply_end(rule conjI)
    show "is_wf_gfg_ls (gfg (toMdl Mdl_3WTsP_loop))"
      by (simp add: is_wf_GFG_3WTs_loop Mdl_3WTsP_loop_def toMdl_def)
  next
    apply_end(rule conjI)
    show "ftotal_on (frd (toMdl Mdl_3WTsP_loop)) (set (NsG (gfg (toMdl Mdl_3WTsP_loop)))) fr_set"
      by (simp add: ftotal_on_def Mdl_3WTsP_loop_def toMdl_def GFG_3WTsP_loop_def 
        F_ASD_3WTsP_loop_def
        toFr_def toSGr_def SG_ASD_3WTsP_loop_def F_CD_3WTsP_loop_def fr_set_def is_fr_def)
  next
    apply_end(rule conjI)
    show "disjMdlFrs (toMdl Mdl_3WTsP_loop)"
      by (simp add: disjMdlFrs_def Mdl_3WTsP_loop_def disjFs_def disjGsL_def 
        GFG_3WTsP_loop_def F_Common_def SG_F_Common_def F_Props_def SG_F_Props_def
        toFr_def toMdl_def toSGr_def SG_ASD_3WTsP_loop_def SG_CD_3WTsP_loop_def
        F_ASD_3WTsP_loop_def F_CD_3WTsP_loop_def)
  next
    show "mUM2GFG (toMdl Mdl_3WTsP_loop)
      \<in> morphF2GFGr (UMdlFs (toMdl Mdl_3WTsP_loop)) (toGFGr (gfg (toMdl Mdl_3WTsP_loop)))"
      by (simp add: UGM_eq_ConsUGM)
  qed

definition MdlTy_3WTsP_loop :: "MdlTy_ls"
where
  "MdlTy_3WTsP_loop \<equiv> \<lparr>tmdlL = INTO_SysML_MM_T, 
    mdlL = Mdl_3WTsP_loop,
    mtyL = (consUGM T_F_ASD_3WTsP_loop T_F_CD_3WTsP_loop)\<rparr>"

lemma is_wf_mdlt_3WTsP_loop: "is_wf_mdlty (toMdlTy MdlTy_3WTsP_loop)"
  proof (simp add: is_wf_mdlty_def, rule conjI)
    show "is_wf_tmdl (tmdl (toMdlTy MdlTy_3WTsP_loop))"
      by (simp add: is_wf_INTO_SysML_MM_T MdlTy_3WTsP_loop_def toMdlTy_def)
  next
    apply_end(rule conjI)
    show "is_wf_mdl (mdl (toMdlTy MdlTy_3WTsP_loop))"
      by (simp add: is_wf_mdl_3WTs_loop toMdlTy_def MdlTy_3WTsP_loop_def)
  next
    show "mty (toMdlTy MdlTy_3WTsP_loop)
    \<in> morphFr (UMdlFs (mdl (toMdlTy MdlTy_3WTsP_loop))) (fr (UTyMdlFs (tmdl (toMdlTy MdlTy_3WTsP_loop))))"
    by (simp add: toMdlTy_def MdlTy_3WTsP_loop_def)
  qed

value "consUMdlFs (mdlL MdlTy_3WTsP_loop)"
 
value "INTO_SysML_toPDG_Nodes (mdlL MdlTy_3WTsP_loop) (toMorph (mtyL MdlTy_3WTsP_loop))"

value "INTO_SysML_toPDG MdlTy_3WTsP_loop"

value "nodesOfMMTy (consUMdlFs (mdlL MdlTy_3WTsP_loop)) (toMorph (mtyL MdlTy_3WTsP_loop)) ''Port''"

value "nodesOfMMTy (consUMdlFs (mdlL MdlTy_3WTsP_loop)) (toMorph (mtyL MdlTy_3WTsP_loop)) ''Connector''"

value "edgesOfMMTy (consUMdlFs (mdlL MdlTy_3WTsP_loop)) (toMorph (mtyL MdlTy_3WTsP_loop)) ''EPortType''"

value "edgesOfMMTy (consUMdlFs (mdlL MdlTy_3WTsP_loop)) (toMorph (mtyL MdlTy_3WTsP_loop)) ''EFlowPortDepends''"

value "edgesOfMMTy (consUMdlFs (mdlL MdlTy_3WTsP_loop)) (toMorph (mtyL MdlTy_3WTsP_loop)) ''EBIports''"

value "getSrcPortOfC (toMorph (mtyL MdlTy_3WTsP_loop)) (consUMdlFs (mdlL MdlTy_3WTsP_loop)) ''C_iout_t1in''"

value "getTgtPortOfC (toMorph (mtyL MdlTy_3WTsP_loop)) (consUMdlFs (mdlL MdlTy_3WTsP_loop)) ''C_iout_t1in''"

(*fun getRightDepends:: "Morph \<Rightarrow> Fr_ls \<Rightarrow> V \<Rightarrow> E list"
where
  "getRightDepends m FL v =  map fst ([p\<leftarrow>consSrcStF FL. 
      (fst p) \<in> set (edgesOfMMTy FL m ''EFlowPortDepends'')
      \<and> (snd p) = (getFlowPortTypeOfPort m FL v)])"

value "getRightDepends (toMorph (mtyL MdlTy_3WTsP)) (consUMdlFs (mdlL MdlTy_3WTsP)) ''vo''"*)

(*Get these functions right*)
value "getBlockInstanceOfPort (toMorph (mtyL MdlTy_3WTsP_loop)) (consUMdlFs (mdlL MdlTy_3WTsP_loop)) ''vo''"
value "getOtherInternalPorts (toMorph (mtyL MdlTy_3WTsP_loop)) (consUMdlFs (mdlL MdlTy_3WTsP_loop)) ''vo''"
value "getFlowPortTypeOfPort (toMorph (mtyL MdlTy_3WTsP_loop)) (consUMdlFs (mdlL MdlTy_3WTsP_loop)) ''vo''"

fun internalConnectionsOf :: "Mdl_ls \<Rightarrow> Morph \<Rightarrow> V \<Rightarrow> Gr_ls"
where
  "internalConnectionsOf ML m v = buildGrForInternalPortConnections m (consUMdlFs ML) v"

value "buildGrForConnector (toMorph (mtyL MdlTy_3WTsP_loop)) (consUMdlFs (mdlL MdlTy_3WTsP_loop)) ''C_vi1_vi2''"
value "buildGrForInternalDependenciesOfPorts (toMorph (mtyL MdlTy_3WTsP_loop)) (consUMdlFs (mdlL MdlTy_3WTsP_loop))"
value "internalConnectionsOf (mdlL MdlTy_3WTsP_loop) (toMorph (mtyL MdlTy_3WTsP_loop)) ''vo''"

end