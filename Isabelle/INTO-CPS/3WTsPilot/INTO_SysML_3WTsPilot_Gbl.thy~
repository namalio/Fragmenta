
(*  File:      'INTO_SysML_3WTsPilot_Gbl' 
    Description: Global enconding of the INTO-SysML model of pilot case study of 3 Water tanks 
    Author:     Nuno Amálio
*)

theory INTO_SysML_3WTsPilot_Gbl
imports INTO_SysML_3WTsPilot_CD "../INTO_SysML_ToPDG"
  
begin

definition GFG_3WTsP :: "GFGr_ls"
where
  "GFG_3WTsP \<equiv> 
    \<lparr>NsG = [''F_ASD_3WTsP'', ''F_CD_3WTsP''], 
      EsG= [''E_F_CD_3WTsP_ASD'', ''E_F_ASD_3WTsP'', ''E_F_CD_3WTsP''], 
      srcG = [(''E_F_CD_3WTsP_ASD'', ''F_CD_3WTsP''), 
        (''E_F_ASD_3WTsP'', ''F_ASD_3WTsP''),
        (''E_F_CD_3WTsP'', ''F_CD_3WTsP'')],
      tgtG = [(''E_F_CD_3WTsP_ASD'', ''F_ASD_3WTsP''), 
        (''E_F_ASD_3WTsP'', ''F_ASD_3WTsP''),
        (''E_F_CD_3WTsP'', ''F_CD_3WTsP'')],
      ext_ty_ls = [(''E_F_CD_3WTsP_ASD'', eimp), (''E_F_ASD_3WTsP'', eimp),
        (''E_F_CD_3WTsP'', eimp)]\<rparr>"

axiomatization
where
  Es_GFG_3WTsP: "Es (toGFGr(GFG_3WTsP)) \<subseteq> E_A"
  and Ns_GFG_3WTsP: "Ns (toGFGr(GFG_3WTsP)) \<subseteq> V_A"

lemma is_wf_GFG_3WTs: "is_wf_gfg_ls GFG_3WTsP"
  proof -
    have h_wf_g: "is_wf_g (toGFGr GFG_3WTsP)"
      using Es_GFG_3WTsP Ns_GFG_3WTsP
        by (simp add: is_wf_g_def GFG_3WTsP_def ftotal_on_def toGFGr_def)
    show ?thesis
    proof (simp add: is_wf_gfg_ls_def, rule conjI)
      show "distinct (NsG GFG_3WTsP)"
      by (simp add: GFG_3WTsP_def)
    next
      apply_end(rule conjI)
      show "distinct (map fst (srcG GFG_3WTsP))"
        by (simp add: GFG_3WTsP_def)
    next
      apply_end(rule conjI)
      show "distinct (map fst (tgtG GFG_3WTsP))"
        by (simp add: GFG_3WTsP_def)
    next
      show "is_wf_gfg (toGFGr GFG_3WTsP)"
        proof (simp add: is_wf_gfg_def, rule conjI)
          show "is_wf_g (toGFGr GFG_3WTsP)"
            using h_wf_g by simp
        next
          apply_end (rule conjI)
          show "ftotal_on (ext_ty (toGFGr GFG_3WTsP)) (Es (toGFGr GFG_3WTsP)) GFGEdgeTy_set"
            by (simp add: GFG_3WTsP_def toGFGr_def GFGEdgeTy_set_def ftotal_on_def)
        next
          apply_end (rule conjI)
          show "NodesWithSelfEdges (toGFGr GFG_3WTsP)"
          proof (simp add: NodesWithSelfEdges_def, clarify)
            fix v
            assume "v \<in> Ns (toGFGr GFG_3WTsP)"
            then have h1: "v = ''F_CD_3WTsP'' \<or> v = ''F_ASD_3WTsP''"
              by (auto simp add: GFG_3WTsP_def toGFGr_def)
            then show "\<exists>e. e \<in> Es (toGFGr GFG_3WTsP) 
              \<and> src (toGFGr GFG_3WTsP) e = Some v 
              \<and> tgt (toGFGr GFG_3WTsP) e = Some v"
            by (simp add:  GFG_3WTsP_def toGFGr_def NodesWithSelfEdges_def)
              (erule disjE, simp, rule exI[where x="''E_F_ASD_3WTsP''"], simp)
          qed
        next
          show "acyclicGr
            (restrict (toGFGr GFG_3WTsP)
              (Es (toGFGr GFG_3WTsP) - EsId (toGFGr GFG_3WTsP)))"
          by (auto simp add: GFG_3WTsP_def toGFGr_def EsId_def restrict_def acyclicGr_def
            relOfGr_def rst_Ns_def rst_fun_def adjacent_def acyclic_def elim: tranclE)
     qed
   qed
  qed

definition Mdl_3WTsP :: "Mdl_ls"
where
  "Mdl_3WTsP \<equiv> \<lparr>gfgL = GFG_3WTsP, 
    frdL = [(''F_ASD_3WTsP'', F_ASD_3WTsP), (''F_CD_3WTsP'', F_CD_3WTsP)]\<rparr>"

lemma is_wf_mdl_3WTs: "is_wf_mdl (toMdl Mdl_3WTsP)"
  proof (simp add: is_wf_mdl_def, rule conjI)
    show "\<forall>F. F \<in> ran (frd (toMdl Mdl_3WTsP)) \<longrightarrow> is_wf_fr F"
    proof (clarify)
      fix F
      assume "F \<in> ran (frd (toMdl Mdl_3WTsP))"
      then have h1: "F = (toFr F_ASD_3WTsP) \<or> F = (toFr F_CD_3WTsP)"
        by (auto simp add: INTO_SysML_MM_def toMdl_def Mdl_3WTsP_def)
      then show "is_wf_fr F"
      proof (case_tac "F = toFr F_ASD_3WTsP")
        assume "F = toFr F_ASD_3WTsP"
        then show "is_wf_fr F"
          by (simp add: wf_F_ASD_3WTsP)
      next
        assume h2: "F \<noteq> toFr F_ASD_3WTsP"
        then show "is_wf_fr F"
        proof (case_tac "F = toFr F_CD_3WTsP")
          assume "F = toFr F_CD_3WTsP"
          then show "is_wf_fr F"
            by (simp add: wf_F_CD_3WTs)
        next
          assume h3: "F \<noteq> toFr F_CD_3WTsP"
          then show "is_wf_fr F" using h1 h2 by (simp)
        qed
      qed
    qed
  next
    apply_end(rule conjI)
    show "is_wf_gfg_ls (gfg (toMdl Mdl_3WTsP))"
      by (simp add: is_wf_GFG_3WTs Mdl_3WTsP_def toMdl_def)
  next
    apply_end(rule conjI)
    show "ftotal_on (frd (toMdl Mdl_3WTsP)) (set (NsG (gfg (toMdl Mdl_3WTsP)))) fr_set"
      by (simp add: ftotal_on_def Mdl_3WTsP_def toMdl_def GFG_3WTsP_def F_ASD_3WTsP_def
        toFr_def toSGr_def SG_ASD_3WTsP_def F_CD_3WTsP_def fr_set_def is_fr_def)
  next
    apply_end(rule conjI)
    show "disjMdlFrs (toMdl Mdl_3WTsP)"
      by (simp add: disjMdlFrs_def Mdl_3WTsP_def disjFs_def disjGsL_def 
        GFG_3WTsP_def F_Common_def SG_F_Common_def F_Props_def SG_F_Props_def
        toFr_def toMdl_def toSGr_def SG_ASD_3WTsP_def SG_CD_3WTsP_def
        F_ASD_3WTsP_def F_CD_3WTsP_def)
  next
    show "mUM2GFG (toMdl Mdl_3WTsP)
      \<in> morphF2GFGr (UMdlFs (toMdl Mdl_3WTsP)) (toGFGr (gfg (toMdl Mdl_3WTsP)))"
      by (simp add: UGM_eq_ConsUGM)
  qed

definition MdlTy_3WTsP :: "MdlTy_ls"
where
  "MdlTy_3WTsP \<equiv> \<lparr>tmdlL = INTO_SysML_MM_T, 
    mdlL = Mdl_3WTsP,
    mtyL = (consUGM T_F_ASD_3WTsP T_F_CD_3WTsP)\<rparr>"

lemma is_wf_mdlt_3WTsP: "is_wf_mdlty (toMdlTy MdlTy_3WTsP)"
  proof (simp add: is_wf_mdlty_def, rule conjI)
    show "is_wf_tmdl (tmdl (toMdlTy MdlTy_3WTsP))"
      by (simp add: is_wf_INTO_SysML_MM_T MdlTy_3WTsP_def toMdlTy_def)
  next
    apply_end(rule conjI)
    show "is_wf_mdl (mdl (toMdlTy MdlTy_3WTsP))"
      by (simp add: is_wf_mdl_3WTs toMdlTy_def MdlTy_3WTsP_def)
  next
    show "mty (toMdlTy MdlTy_3WTsP)
    \<in> morphFr (UMdlFs (mdl (toMdlTy MdlTy_3WTsP))) (fr (UTyMdlFs (tmdl (toMdlTy MdlTy_3WTsP))))"
    by (simp add: toMdlTy_def MdlTy_3WTsP_def)
  qed

value "consUMdlFs (mdlL MdlTy_3WTsP)"
 
value "INTO_SysML_toPDG_Nodes (mdlL MdlTy_3WTsP) (toMorph (mtyL MdlTy_3WTsP))"

value "INTO_SysML_toPDG MdlTy_3WTsP"

value "nodesOfMMTy (consUMdlFs (mdlL MdlTy_3WTsP)) (toMorph (mtyL MdlTy_3WTsP)) ''Port''"

value "nodesOfMMTy (consUMdlFs (mdlL MdlTy_3WTsP)) (toMorph (mtyL MdlTy_3WTsP)) ''Connector''"

value "edgesOfMMTy (consUMdlFs (mdlL MdlTy_3WTsP)) (toMorph (mtyL MdlTy_3WTsP)) ''EPortType''"

value "edgesOfMMTy (consUMdlFs (mdlL MdlTy_3WTsP)) (toMorph (mtyL MdlTy_3WTsP)) ''EFlowPortDepends''"

value "edgesOfMMTy (consUMdlFs (mdlL MdlTy_3WTsP)) (toMorph (mtyL MdlTy_3WTsP)) ''EBIports''"

value "getSrcPortOfC (toMorph (mtyL MdlTy_3WTsP)) (consUMdlFs (mdlL MdlTy_3WTsP)) ''C_iout_t1in''"

value "getTgtPortOfC (toMorph (mtyL MdlTy_3WTsP)) (consUMdlFs (mdlL MdlTy_3WTsP)) ''C_iout_t1in''"

(*fun getRightDepends:: "Morph \<Rightarrow> Fr_ls \<Rightarrow> V \<Rightarrow> E list"
where
  "getRightDepends m FL v =  map fst ([p\<leftarrow>consSrcStF FL. 
      (fst p) \<in> set (edgesOfMMTy FL m ''EFlowPortDepends'')
      \<and> (snd p) = (getFlowPortTypeOfPort m FL v)])"

value "getRightDepends (toMorph (mtyL MdlTy_3WTsP)) (consUMdlFs (mdlL MdlTy_3WTsP)) ''vo''"*)

(*Get these functions right*)
value "getBlockInstanceOfPort (toMorph (mtyL MdlTy_3WTsP)) (consUMdlFs (mdlL MdlTy_3WTsP)) ''vo''"
value "getOtherInternalPorts (toMorph (mtyL MdlTy_3WTsP)) (consUMdlFs (mdlL MdlTy_3WTsP)) ''vo''"
value "getFlowPortTypeOfPort (toMorph (mtyL MdlTy_3WTsP)) (consUMdlFs (mdlL MdlTy_3WTsP)) ''vo''"

fun internalConnectionsOf :: "Mdl_ls \<Rightarrow> Morph \<Rightarrow> V \<Rightarrow> Gr_ls"
where
  "internalConnectionsOf ML m v = buildGrForInternalPortConnections m (consUMdlFs ML) v"

value "buildGrForConnector (toMorph (mtyL MdlTy_3WTsP)) (consUMdlFs (mdlL MdlTy_3WTsP)) ''C_vi1_vi2''"
value "buildGrForInternalDependenciesOfPorts (toMorph (mtyL MdlTy_3WTsP)) (consUMdlFs (mdlL MdlTy_3WTsP))"
value "internalConnectionsOf (mdlL MdlTy_3WTsP) (toMorph (mtyL MdlTy_3WTsP)) ''vo''"

end