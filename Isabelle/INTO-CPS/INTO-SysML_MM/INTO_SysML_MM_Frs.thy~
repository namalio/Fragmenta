(*  Title:      Theory of the SysML/INTO-CPS MM, which is defined as fragments
    Author:     Nuno Amálio
*)

theory INTO_SysML_MM_Frs
imports "../Fragmenta/Fragmenta_TFrs" "../Extra/Rel_Extra" 
  "../Extra/Trcl_Extra" 
  
begin

(*Fragment 'F_Common' of the 'SysML/INTO-CPS' MM*)
definition SG_F_Common :: "SGr_ls"
where
  "SG_F_Common = \<lparr>NsG=[''NamedElement'', ''Type''], 
      EsG = [], 
      srcG =  [], 
      tgtG = [],
      ntyG =[(''NamedElement'', nnrml), (''Type'', nnrml)],
      etyG = [],
      srcmG = [], tgtmG = []\<rparr>"

axiomatization
where
  Ns_SG_F_Common: "set (NsG SG_F_Common) \<subseteq> V_A"

(* Well-formedness proof obligation of SG_F_Common"*)
lemma wf_SG_F_Common: "is_wf_sg (toSGr SG_F_Common)"
  proof (simp add: is_wf_sg_def, rule conjI)
    show "is_wf_g (toSGr SG_F_Common)"
      using Ns_SG_F_Common
      by (simp add: is_wf_g_def SG_F_Common_def ftotal_on_def toSGr_def)
  next
    apply_end(rule conjI)
    show "ftotal_on (nty (toSGr SG_F_Common)) (Ns (toSGr SG_F_Common)) SGNTy_set"
      by (auto simp add: SG_F_Common_def ftotal_on_def SGNTy_set_def toSGr_def)
  next
    apply_end(rule conjI)
    show "ftotal_on (ety (toSGr SG_F_Common)) (Es (toSGr SG_F_Common)) SGETy_set"
      by (auto simp add: SG_F_Common_def ftotal_on_def toSGr_def)
  next
    apply_end(rule conjI)
    show "dom (srcm (toSGr SG_F_Common)) = EsTy (toSGr SG_F_Common) {Some erelbi, Some ecompbi}"
      by (auto simp add: SG_F_Common_def EsTy_def toSGr_def)
  next
    apply_end(rule conjI)
    show "dom (tgtm (toSGr SG_F_Common)) = 
      EsTy (toSGr SG_F_Common) {Some erelbi, Some ereluni, Some ecompbi, Some ecompuni}"
      by (auto simp add: SG_F_Common_def EsTy_def toSGr_def)
  next
    apply_end(rule conjI)
    show "EsR (toSGr SG_F_Common) \<subseteq> EsId (toSGr SG_F_Common)"
      by (auto simp add: EsR_def SG_F_Common_def EsTy_def toSGr_def)
  next
    apply_end(rule conjI)
    show "srcm (toSGr SG_F_Common) ` EsTy (toSGr SG_F_Common) {Some ecompbi}
      \<subseteq> {Some (rm 0 (val (Suc 0))), Some (sm (val (Suc 0)))}"
      by (auto simp add: SG_F_Common_def EsTy_def toSGr_def)
  next
    show "acyclicGr (inhG (toSGr SG_F_Common))"
    proof -
      have h1: "EsI (toSGr SG_F_Common) = {}"
        by (auto simp add: SG_F_Common_def EsI_def EsTy_def toSGr_def)
      from h1 show "acyclicGr (inhG (toSGr SG_F_Common))"
        by (rule acyclic_sg_noEI)
    qed
  qed

(*Fragment corresponding to SG_F_Common *)
definition F_Common :: "Fr_ls"
where
   "F_Common = \<lparr>sg_ls = SG_F_Common, tr_ls = []\<rparr>"

lemma refs_F_Common: "refs (toFr F_Common) = {}"
  by (auto simp add: reps_def refs_def relOfGr_def refsG_def withRsG_def 
    EsRP_def NsP_def NsTy_def restrict_def adjacent_def toFr_def toSGr_def F_Common_def 
    SG_F_Common_def EsR_def EsTy_def rst_fun_def tgtr_def converse_def)

(* Well-formedness proof obligation of fragments"*)
lemma wf_F_Common: "is_wf_fr (toFr F_Common)"
  proof (simp add: is_wf_fr_def, rule conjI)
    show "is_wf_sg (sg (toFr F_Common))"
      by (simp add: F_Common_def wf_SG_F_Common toFr_def)
    next 
      apply_end(rule conjI)
      show "ftotal_on (tr (toFr F_Common)) (EsRP (sg (toFr F_Common))) V_A"
        by (simp add: F_Common_def ftotal_on_def SG_F_Common_def EsRP_def toFr_def toSGr_def)
    next
      apply_end(rule conjI)
      show "inj_on (src (sg (toFr F_Common))) (EsRP (sg (toFr F_Common)))"
        by (simp add: F_Common_def SG_F_Common_def inj_on_def EsRP_def toFr_def toSGr_def)
    next
      apply_end(rule conjI)
      show "ran (src (sg (toFr F_Common)) |` EsRP (sg (toFr F_Common))) = NsP (sg (toFr F_Common))"
        by (auto simp add: F_Common_def SG_F_Common_def inj_on_def EsRP_def EsR_def 
          EsTy_def NsP_def NsTy_def vimage_def toFr_def toSGr_def)
    next
      apply_end(rule conjI)
      show "\<forall>v. v \<in> NsP (sg (toFr F_Common)) \<longrightarrow> nonPRefsOf (toFr F_Common) v \<noteq> {}"
        by (simp add: nonPRefsOf_def refsOf_def refs_F_Common)
          (simp add: NsP_def NsTy_def F_Common_def SG_F_Common_def vimage_def toFr_def toSGr_def)
    next
      apply_end(rule conjI)
      show "acyclic_fr (toFr F_Common)"
        using wf_SG_F_Common
        by (simp add: acyclic_fr_def refs_F_Common)
          (simp add: F_Common_def SG_F_Common_def is_wf_sg_def acyclicGr_def inh_def 
            toFr_def toSGr_def)
    next
      show "proxies_dont_inherit (toFr F_Common)"
        by (simp add: proxies_dont_inherit_def F_Common_def SG_F_Common_def toFr_def toSGr_def)
    qed

(*Type Fragment corresponding to F_Common *)
definition TF_Common :: "TFr_ls"
where
   "TF_Common = \<lparr>fr_ls = F_Common, iet_ls = []\<rparr>"

(* Well-formedness proof obligation of 'TF_Common'*)
lemma wf_TF_Common: "is_wf_tfr (toTFr TF_Common)"
  proof (simp add: is_wf_tfr_def, rule conjI)
    show "is_wf_fr (fr (toTFr TF_Common))"
      by (simp add: TF_Common_def wf_F_Common toTFr_def)
  next
    apply_end(rule conjI)
    show "dom (iet (toTFr TF_Common)) \<subseteq> EsA (sg (fr (toTFr TF_Common)))"
      by (simp add: EsA_def TF_Common_def toTFr_def)
  next
    show "ftotal_on (iety (toTFr TF_Common)) (EsA (sg (fr (toTFr TF_Common)))) SGETy_set"
      by (auto simp add: ftotal_on_def TF_Common_def EsA_def EsTy_def vimage_def 
        F_Common_def SG_F_Common_def iety_def toFr_def toSGr_def toTFr_def)
  qed

(*SG of fragment 'F_PTypes'*)
definition SG_F_PTypes :: "SGr_ls"
where
  "SG_F_PTypes = \<lparr>NsG=[''PrType2'', ''PType'', ''Real'', ''Int'',
    ''Nat'', ''Bool'', ''String'', ''Interval''], 
      EsG = [''EISupPType'', ''EISupReal'', ''EISupInt'', ''EISupNat'', 
        ''EISupString'', ''EISupBool'', ''EISupInterval'', ''EInterval_lb'', 
        ''EInterval_ub'', ''ERPrType2''], 
      srcG =  [(''EISupPType'', ''PType''), (''EISupReal'', ''Real''), 
        (''EISupInt'', ''Int''), 
        (''EISupNat'', ''Nat''), (''EISupBool'', ''Bool''), 
        (''EISupString'', ''String''), (''EISupInterval'', ''Interval''), 
        (''EInterval_lb'', ''Interval''), 
        (''EInterval_ub'', ''Interval''), (''ERPrType2'', ''PrType2'')], 
      tgtG =  [(''EISupPType'', ''PrType2''), (''EISupReal'', ''PType''), 
        (''EISupInt'', ''PType''), 
        (''EISupNat'', ''Int''), (''EISupBool'', ''PType''), 
        (''EISupString'', ''PType''), (''EISupInterval'', ''PType''),  
        (''EInterval_lb'', ''Int''), 
        (''EInterval_ub'', ''Int''), (''ERPrType2'', ''PrType2'')],
      ntyG =[(''PrType2'', nprxy), (''PType'', nnrml), (''Real'', nnrml),
        (''Int'', nnrml), (''Nat'', nnrml), (''Bool'', nnrml),
        (''String'', nenum), (''Interval'', nenum)],
      etyG =[(''EISupPType'', einh), (''EISupReal'', einh), (''EISupInt'', einh),
        (''EISupNat'', einh), (''EISupBool'', einh), (''EISupString'', einh), 
        (''EISupInterval'', einh),
        (''EInterval_lb'', ereluni), (''EInterval_ub'', ereluni), 
        (''ERPrType2'', eref)],
      srcmG = [], 
      tgtmG = [(''EInterval_lb'', sm (val 1)), (''EInterval_ub'', sm (val 1))]\<rparr>"

axiomatization
where
  Es_SG_F_PTypes: "Es (toSGr SG_F_PTypes) \<subseteq> E_A"
  and Ns_SG_F_PTypes: "Ns (toSGr SG_F_PTypes) \<subseteq> V_A"

value "consInh SG_F_PTypes"

value "consUSG SG_F_PTypes SG_F_Common"

lemma wf_SG_F_PTypes: "is_wf_sg (toSGr SG_F_PTypes)"
  proof -
    have h_wf_g: "is_wf_g (toSGr SG_F_PTypes)"
      using Ns_SG_F_PTypes Es_SG_F_PTypes 
      by (auto simp add: is_wf_g_def SG_F_PTypes_def ftotal_on_def toSGr_def)
    show "is_wf_sg (toSGr SG_F_PTypes)"
    proof (simp add: is_wf_sg_def, rule conjI)
      show "is_wf_g (toSGr SG_F_PTypes)"
      using h_wf_g by simp
    next
      apply_end(rule conjI)
      show "ftotal_on (nty (toSGr SG_F_PTypes)) (Ns (toSGr SG_F_PTypes)) SGNTy_set"
        by (auto simp add: SG_F_PTypes_def ftotal_on_def SGNTy_set_def toSGr_def)
    next
      apply_end(rule conjI)
      show "ftotal_on (ety (toSGr SG_F_PTypes)) (Es (toSGr SG_F_PTypes)) SGETy_set"
        by (auto simp add: SG_F_PTypes_def ftotal_on_def SGETy_set_def toSGr_def)
    next
      apply_end(rule conjI)
      show "dom (srcm (toSGr SG_F_PTypes)) = EsTy (toSGr SG_F_PTypes) {Some erelbi, Some ecompbi}"
        by (auto simp add: SG_F_PTypes_def EsTy_def vimage_def toSGr_def)
    next
      apply_end(rule conjI)
      show "dom (tgtm (toSGr SG_F_PTypes)) 
        = EsTy (toSGr SG_F_PTypes) {Some erelbi, Some ereluni, Some ecompbi, Some ecompuni}"
        by (auto simp add: SG_F_PTypes_def EsTy_def vimage_def toSGr_def)
    next
      apply_end(rule conjI)
      show "EsR (toSGr SG_F_PTypes) \<subseteq> EsId (toSGr SG_F_PTypes)"
        by (simp add: EsR_def SG_F_PTypes_def EsTy_def EsId_def vimage_def toSGr_def)
    next
      apply_end(rule conjI)
      show "srcm (toSGr SG_F_PTypes) ` EsTy (toSGr SG_F_PTypes) {Some ecompbi}
        \<subseteq> {Some (rm 0 (val (Suc 0))), Some (sm (val (Suc 0)))}"
        by (auto simp add: SG_F_PTypes_def EsTy_def vimage_def toSGr_def)
    next
      show "acyclicGr (inhG (toSGr SG_F_PTypes))"
      using h_wf_g by (simp add: acyclicGr_def inh_eq inh_eq_consInh)(eval)
    qed
  qed

(*'F_Props' Fragment*)
definition F_PTypes :: "Fr_ls"
where
   "F_PTypes = \<lparr>sg_ls = SG_F_PTypes, 
    tr_ls = [(''ERPrType2'', ''Type'')]\<rparr>"


value "consRefs F_PTypes"

(* Well-formedness proof obligation of fragments"*)
lemma wf_F_PTypes: "is_wf_fr (toFr F_PTypes)"
  proof -
    let ?refs_F_PTypes = "{(''PrType2'', ''Type'')}"
    have h_ftotal_tr: "ftotal_on (tr (toFr F_PTypes)) (EsRP (sg (toFr F_PTypes))) V_A"
    proof (simp add: ftotal_on_def, rule conjI)
      show "dom (tr (toFr F_PTypes)) = EsRP (sg (toFr F_PTypes))"
      proof
        show "dom (tr (toFr F_PTypes)) \<subseteq> EsRP (sg (toFr F_PTypes))"
        by (simp add: F_PTypes_def ftotal_on_def SG_F_PTypes_def EsRP_def 
          NsP_def EsR_def EsTy_def NsTy_def SG_F_Common_def toFr_def 
          toSGr_def)
      next
        show "EsRP (sg (toFr F_PTypes)) \<subseteq> dom (tr (toFr F_PTypes))"
          using Ns_SG_F_PTypes Ns_SG_F_Common
          by (auto simp add: F_PTypes_def ftotal_on_def SG_F_PTypes_def EsRP_def 
            NsP_def EsR_def EsTy_def NsTy_def SG_F_Common_def toFr_def 
            toSGr_def)
      qed
    next
      show "ran (tr (toFr F_PTypes)) \<subseteq> V_A"
        using Ns_SG_F_Common
        by (simp add: F_PTypes_def toFr_def SG_F_Common_def)
    qed 
    from wf_SG_F_PTypes have hb: "is_wf_sg (sg (toFr F_PTypes))"
      by (simp add: toFr_def F_PTypes_def)
    have refs_F_PTypes: "refs (toFr F_PTypes) = ?refs_F_PTypes"
      using hb h_ftotal_tr hb by (simp add: refs_eq_consRefs)(eval)
    show ?thesis
    proof (simp add: is_wf_fr_def, rule conjI)
      show "is_wf_sg (sg (toFr F_PTypes))"
        by (simp add: hb)
    next 
      apply_end(rule conjI)
      show "ftotal_on (tr (toFr F_PTypes)) (EsRP (sg (toFr F_PTypes))) V_A"
        using h_ftotal_tr by (simp)
    next
      apply_end(rule conjI)
      show "inj_on (src (sg (toFr F_PTypes))) (EsRP (sg (toFr F_PTypes)))"
        by (simp add: F_PTypes_def inj_on_def EsRP_def EsR_def NsP_def EsTy_def NsTy_def 
          SG_F_PTypes_def toFr_def toSGr_def) 
    next
      apply_end(rule conjI)
      show "ran (src (sg (toFr F_PTypes)) |` EsRP (sg (toFr F_PTypes))) = NsP (sg (toFr F_PTypes))"
        by (auto simp add: F_PTypes_def SG_F_PTypes_def inj_on_def EsRP_def EsR_def 
          EsTy_def NsP_def NsTy_def vimage_def toFr_def toSGr_def)
    next
      apply_end(rule conjI)
      show "\<forall>v. v \<in> NsP (sg (toFr F_PTypes)) \<longrightarrow> nonPRefsOf (toFr F_PTypes) v \<noteq> {}"
      proof (rule allI, rule impI)
        fix v
        assume "v \<in> NsP (sg (toFr F_PTypes))"
        then have h1: "v = ''PrType2''"
          by (simp add: NsP_def F_PTypes_def NsTy_def SG_F_PTypes_def toFr_def toSGr_def 
            split: if_splits)
        then show " nonPRefsOf (toFr F_PTypes) v \<noteq> {}"
          by (simp add: nonPRefsOf_def refsOf_def refs_F_PTypes NsP_def NsTy_def)
            (simp add: F_PTypes_def SG_F_PTypes_def toFr_def toSGr_def)
      qed
    next
      apply_end(rule conjI)
      show "acyclic_fr (toFr F_PTypes)"
        proof -
          from wf_SG_F_PTypes have "acyclic (inh (sg (toFr F_PTypes)))"
            by (simp add: is_wf_sg_def acyclicGr_def inh_def F_PTypes_def toFr_def)
          then show "acyclic_fr (toFr F_PTypes)"
          proof (simp add: acyclic_fr_def)
            assume h1: "acyclic (inh (sg (toFr F_PTypes)))"
            have h2: "Domain (inh (sg (toFr F_PTypes))) \<inter> Domain (refs (toFr F_PTypes)) = {}"
              using wf_SG_F_PTypes inh_eq_consInh[of "SG_F_PTypes"] 
              by (simp add: refs_F_PTypes)(simp add: is_wf_sg_def toFr_def F_PTypes_def, eval)
            have h3: "Range (refs (toFr F_PTypes)) \<inter> Domain (inh (sg (toFr F_PTypes))) = {}"
              using wf_SG_F_PTypes inh_eq_consInh[of "SG_F_PTypes"] 
              by (simp add: refs_F_PTypes)(simp add: is_wf_sg_def toFr_def F_PTypes_def, eval)
            have h4: "acyclic(refs (toFr F_PTypes))"
              by (simp add: refs_F_PTypes)(auto simp add: rtrancl_in acyclic_def)
            from h1 h2 h3 h4 show "acyclic (inh (sg (toFr F_PTypes)) \<union> refs (toFr F_PTypes))"
              by (simp add: acyclic_Un)
          qed
        qed
      next
      show "proxies_dont_inherit (toFr F_PTypes)"
        by (simp add: proxies_dont_inherit_def  EsI_def NsP_def NsTy_def EsTy_def vimage_def
          F_PTypes_def SG_F_PTypes_def toFr_def toSGr_def)
    qed
  qed

(*Type Fragment corresponding to 'F_PTypes' *)
definition TF_PTypes :: "TFr_ls"
where
   "TF_PTypes = \<lparr>fr_ls = F_PTypes, 
      iet_ls = []\<rparr>"

(* Well-formedness proof obligation of 'TF_PTypes'*)
lemma wf_TF_PTypes: "is_wf_tfr (toTFr TF_PTypes)"
  proof (simp add: is_wf_tfr_def, rule conjI)
    show "is_wf_fr (fr (toTFr TF_PTypes))"
      by (simp add: TF_PTypes_def wf_F_PTypes toTFr_def)
  next
    apply_end(rule conjI)
    show "dom (iet (toTFr TF_PTypes)) \<subseteq> EsA (sg (fr (toTFr TF_PTypes)))"
      by (simp add: EsA_def TF_PTypes_def toTFr_def)
  next
    show "ftotal_on (iety (toTFr TF_PTypes)) (EsA (sg (fr (toTFr TF_PTypes)))) SGETy_set"
      by (auto simp add: ftotal_on_def TF_PTypes_def EsA_def EsTy_def vimage_def F_PTypes_def
        SG_F_PTypes_def toFr_def toSGr_def SGETy_set_def iety_def toTFr_def)
  qed

(*Fragment 'F_Props' of the 'SysML/INTO-CPS' MM*)

(*SG of fragment 'F_Props'*)
definition SG_F_Props :: "SGr_ls"
where
  "SG_F_Props = \<lparr>NsG=[''PrNamedElement'', ''PrType'', ''PrString2'', ''Property'', 
    ''Variable'', ''FlowPort'', ''VariableKind'', ''Direction''], 
      EsG = [''EISupProperty'', ''EISupVariable'', ''EISupFlowPort'', ''EPropInit'', 
        ''EPropType'', ''EVarKind'', ''EFlowPortDirection'', ''EFlowPortDepends'',
        ''ERPrNamedElement'', ''ERPrType'', ''ERPrString2''], 
      srcG =  [(''EISupProperty'', ''Property''), (''EISupVariable'', ''Variable''), 
        (''EISupFlowPort'', ''FlowPort''), (''EPropInit'', ''Property''), 
        (''EPropType'', ''Property''), (''EVarKind'', ''Variable''), 
        (''EFlowPortDirection'', ''FlowPort''), (''EFlowPortDepends'', ''FlowPort''),
        (''ERPrNamedElement'', ''PrNamedElement''), (''ERPrType'', ''PrType''),
        (''ERPrString2'', ''PrString2'')], 
      tgtG= [(''EISupProperty'', ''PrNamedElement''), 
        (''EISupVariable'', ''Property''), 
        (''EISupFlowPort'', ''Property''),
        (''EPropInit'', ''PrString2''),  
        (''EPropType'', ''PrType''), 
        (''EVarKind'', ''VariableKind''), 
        (''EFlowPortDirection'', ''Direction''), 
        (''EFlowPortDepends'', ''PrString2''), 
        (''ERPrNamedElement'', ''PrNamedElement''), 
        (''ERPrType'', ''PrType''),
        (''ERPrString2'', ''PrString2'')],
      ntyG =[(''PrNamedElement'', nprxy), (''PrType'', nprxy), (''PrString2'', nprxy),
        (''Property'', nnrml),
        (''Property'', nnrml), (''Variable'', nnrml), (''FlowPort'', nnrml),
        (''VariableKind'', nenum), (''Direction'', nenum)],
      etyG =[(''EISupProperty'', einh), (''EISupVariable'', einh), 
        (''EISupFlowPort'', einh),
        (''EPropInit'', ereluni), (''EPropType'', ereluni), (''EVarKind'', ereluni), 
        (''EFlowPortDirection'', ereluni), (''EFlowPortDepends'', ereluni),
        (''ERPrNamedElement'', eref), 
        (''ERPrType'', eref), (''ERPrString2'', eref)],
      srcmG = [], 
      tgtmG = [(''EPropType'', sm (val 1)), (''EPropInit'', sm (val 1)), 
        (''EVarKind'', sm (val 1)), (''EFlowPortDirection'', sm (val 1)),
        (''EFlowPortDepends'', sm *)]\<rparr>"

axiomatization
where
  Es_SG_F_Props: "Es (toSGr SG_F_Props) \<subseteq> E_A"
  and Ns_SG_F_Props: "Ns (toSGr SG_F_Props) \<subseteq> V_A"

lemma wf_SG_F_Props: "is_wf_sg (toSGr SG_F_Props)"
  proof -
    have h_wf_g: "is_wf_g (toSGr SG_F_Props)"
      using Ns_SG_F_Props Es_SG_F_Props
      by (auto simp add: is_wf_g_def SG_F_Props_def ftotal_on_def toSGr_def)
    show ?thesis
    proof (simp add: is_wf_sg_def, rule conjI)
      show "is_wf_g (toSGr SG_F_Props)"
        by (simp add: h_wf_g)
    next
      apply_end(rule conjI)
      show "ftotal_on (nty (toSGr SG_F_Props)) (Ns (toSGr SG_F_Props)) SGNTy_set"
        by (auto simp add: SG_F_Props_def ftotal_on_def SGNTy_set_def toSGr_def)
    next
      apply_end(rule conjI)
      show "ftotal_on (ety (toSGr SG_F_Props)) (Es (toSGr SG_F_Props)) SGETy_set"
        by (auto simp add: SG_F_Props_def ftotal_on_def SGETy_set_def toSGr_def)
    next
      apply_end(rule conjI)
      show "dom (srcm (toSGr SG_F_Props)) = EsTy (toSGr SG_F_Props) {Some erelbi, Some ecompbi}"
        by (auto simp add: SG_F_Props_def EsTy_def vimage_def toSGr_def)
    next
      apply_end(rule conjI)
      show "dom (tgtm (toSGr SG_F_Props)) = 
        EsTy (toSGr SG_F_Props) {Some erelbi, Some ereluni, Some ecompbi, Some ecompuni}"
        by (auto simp add: SG_F_Props_def EsTy_def vimage_def toSGr_def)
    next
      apply_end(rule conjI)
      show "EsR (toSGr SG_F_Props) \<subseteq> EsId (toSGr SG_F_Props)"
        by (auto simp add: EsR_def SG_F_Props_def EsTy_def EsId_def vimage_def toSGr_def)
    next
      apply_end(rule conjI)
      show "srcm (toSGr SG_F_Props) ` EsTy (toSGr SG_F_Props) {Some ecompbi}
        \<subseteq> {Some (rm 0 (val (Suc 0))), Some (sm (val (Suc 0)))}"
        by (auto simp add: SG_F_Props_def EsTy_def vimage_def toSGr_def)
    next
      show "acyclicGr (inhG (toSGr SG_F_Props))"
        using h_wf_g by (simp add: acyclicGr_def inh_eq inh_eq_consInh)(eval)
    qed
  qed

(*'F_Props' Fragment*)
definition F_Props :: "Fr_ls"
where
   "F_Props = \<lparr>sg_ls = SG_F_Props, 
    tr_ls = [(''ERPrNamedElement'', ''NamedElement''), 
      (''ERPrType'', ''Type''), (''ERPrString2'', ''String'')]\<rparr>"


value "consRefs F_Props"

(* Well-formedness proof obligation of fragments"*)
lemma wf_F_Props: "is_wf_fr (toFr F_Props)"
  proof -
    let ?refs_F_Props = "{(''PrNamedElement'', ''NamedElement''), 
      (''PrType'', ''Type''), (''PrString2'', ''String'')}"
    have h_ftotal_tr: "ftotal_on (tr (toFr F_Props)) (EsRP (sg (toFr F_Props))) V_A"
      using Ns_SG_F_Common Ns_SG_F_PTypes
      by (auto simp add: F_Common_def ftotal_on_def SG_F_Props_def EsRP_def 
        F_Props_def NsP_def EsR_def EsTy_def NsTy_def SG_F_Common_def toFr_def 
        toSGr_def SG_F_PTypes_def)
    from wf_SG_F_Props have hb: "is_wf_sg (sg (toFr F_Props))"
      by (simp add: toFr_def F_Props_def)
    have refs_F_Props: "refs (toFr F_Props) = ?refs_F_Props"
      using hb h_ftotal_tr by (simp add: refs_eq_consRefs)(eval)
    show ?thesis
    proof (simp add: is_wf_fr_def, rule conjI)
      show "is_wf_sg (sg (toFr F_Props))"
        by (simp add: hb)
    next 
      apply_end(rule conjI)
      show "ftotal_on (tr (toFr F_Props)) (EsRP (sg (toFr F_Props))) V_A"
        using h_ftotal_tr by (simp)
    next
      apply_end(rule conjI)
      show "inj_on (src (sg (toFr F_Props))) (EsRP (sg (toFr F_Props)))"
        by (simp add: F_Props_def inj_on_def EsRP_def EsR_def NsP_def EsTy_def NsTy_def 
          SG_F_Props_def toFr_def toSGr_def) 
    next
      apply_end(rule conjI)
      show "ran (src (sg (toFr F_Props)) |` EsRP (sg (toFr F_Props))) = NsP (sg (toFr F_Props))"
        by (auto simp add: F_Props_def SG_F_Props_def inj_on_def EsRP_def EsR_def 
          EsTy_def NsP_def NsTy_def vimage_def toFr_def toSGr_def)
    next
      apply_end(rule conjI)
      show "\<forall>v. v \<in> NsP (sg (toFr F_Props)) \<longrightarrow> nonPRefsOf (toFr F_Props) v \<noteq> {}"
      proof (clarify)
        fix v
        assume "v \<in> NsP (sg (toFr F_Props))"
        then have h1: "v = ''PrNamedElement'' \<or> v = ''PrType'' \<or> v = ''PrString2''"
          by (simp add: NsP_def F_Props_def NsTy_def SG_F_Props_def toFr_def toSGr_def 
            split: if_splits)
        assume h2: "nonPRefsOf (toFr F_Props) v = {}"
        from h1 h2 show "False"
        proof (case_tac "v = ''PrNamedElement''")
          assume h3: "v = ''PrNamedElement''"
          from h2 h3 show "False"
            by (simp add: nonPRefsOf_def refsOf_def refs_F_Props)
              (simp add: NsP_def NsTy_def F_Props_def SG_F_Props_def toFr_def toSGr_def)
        next
          assume h3: "v \<noteq> ''PrNamedElement''" 
          show "False"
          proof (case_tac "v = ''PrType''")  
            assume h4: "v = ''PrType''" 
            from h2 h4 show "False"
              by (simp add: nonPRefsOf_def refsOf_def refs_F_Props)
                (simp add: NsP_def NsTy_def F_Props_def SG_F_Props_def toFr_def toSGr_def)
          next
            assume "v \<noteq> ''PrType''" 
            then have h4: "v = ''PrString2''"
              using h1 h3 by (auto) 
            from h2 h4 show "False"
              by (simp add: nonPRefsOf_def refsOf_def refs_F_Props)
                (simp add: NsP_def NsTy_def F_Props_def SG_F_Props_def toFr_def toSGr_def)
          qed
        qed
      qed
    next
      apply_end(rule conjI)
      show "acyclic_fr (toFr F_Props)"
        proof -
          from wf_SG_F_Props have "acyclic (inh (sg (toFr F_Props)))"
            by (simp add: is_wf_sg_def acyclicGr_def inh_def F_Props_def toFr_def)
          then show "acyclic_fr (toFr F_Props)"
          proof (simp add: acyclic_fr_def)
            assume h1: "acyclic (inh (sg (toFr F_Props)))"
            have h2: "Domain (inh (sg (toFr F_Props))) \<inter> Domain (refs (toFr F_Props)) = {}"
              using wf_SG_F_Props inh_eq_consInh[of "SG_F_Props"] 
              by (simp add: refs_F_Props)(simp add: is_wf_sg_def toFr_def F_Props_def, eval)
            have h3: "Range (refs (toFr F_Props)) \<inter> Domain (inh (sg (toFr F_Props))) = {}"
              using wf_SG_F_Props inh_eq_consInh[of "SG_F_Props"]
              by (simp add: refs_F_Props)(simp add: is_wf_sg_def toFr_def F_Props_def, eval)
            have h4: "acyclic(refs (toFr F_Props))"
              by (simp add: refs_F_Props)(auto simp add: rtrancl_in acyclic_def)
            from h1 h2 h3 h4 show "acyclic (inh (sg (toFr F_Props)) \<union> refs (toFr F_Props))"
              by (simp add: acyclic_Un)
          qed
        qed
      next
      show "proxies_dont_inherit (toFr F_Props)"
        by (simp add: proxies_dont_inherit_def  EsI_def NsP_def NsTy_def EsTy_def vimage_def
          F_Props_def SG_F_Props_def toFr_def toSGr_def)
    qed
  qed


(*Type Fragment corresponding to 'F_Props' *)
definition TF_Props :: "TFr_ls"
where
   "TF_Props = \<lparr>fr_ls = F_Props, iet_ls =[]\<rparr>"


(* Well-formedness proof obligation of 'TF_Props'*)
lemma wf_TF_Props: "is_wf_tfr (toTFr TF_Props)"
  proof (simp add: is_wf_tfr_def, rule conjI)
    show "is_wf_fr (fr (toTFr TF_Props))"
      by (simp add: TF_Props_def wf_F_Props toTFr_def)
  next
    apply_end (rule conjI)
    show "dom (iet (toTFr TF_Props)) \<subseteq> EsA (sg (fr (toTFr TF_Props)))"
      by (simp add: TF_Props_def toTFr_def)
  next
    show "ftotal_on (iety (toTFr TF_Props)) (EsA (sg (fr (toTFr TF_Props)))) SGETy_set"
      by (auto simp add: ftotal_on_def TF_Props_def EsA_def EsTy_def vimage_def 
        F_Props_def
        SG_F_Props_def toFr_def toSGr_def SGETy_set_def iety_def toTFr_def)
  qed

(*SG of fragment 'F_Blocks'*)
definition SG_F_Blocks :: "SGr_ls"
where
  "SG_F_Blocks = \<lparr>NsG=[''PrNamedElement2'', ''PrFlowPort'', ''Block'', ''ComponentKind'',
    ''System'', ''Component'', ''ModelKind'', ''Platform'', ''EComponent'', ''POComponent'',
    ''PrVariable''], 
      EsG = [''EISupBlock'', ''EISupSystem'', ''EISupComponent'', ''EISupEComponent'', 
        ''EISupPOComponent'', ''EBlockProps'', ''EComponentVars'', ''EComponentKind'',
        ''EEComponentModelTy'', ''EEComponentPlatform'', ''ERPrNamedElement2'',
        ''ERPrFlowPort'', ''ERPrVariable''], 
      srcG =  [(''EISupBlock'', ''Block''), (''EISupSystem'', ''System''), 
        (''EISupComponent'', ''Component''), 
        (''EISupEComponent'', ''EComponent''), 
        (''EISupPOComponent'', ''POComponent''),
        (''EBlockProps'', ''Block''), (''EComponentVars'', ''Component''), 
        (''EComponentKind'', ''Component''), 
        (''EEComponentModelTy'', ''EComponent''),
        (''EEComponentPlatform'', ''EComponent''), 
        (''ERPrNamedElement2'', ''PrNamedElement2''), 
        (''ERPrFlowPort'', ''PrFlowPort''), (''ERPrVariable'', ''PrVariable'')], 
      tgtG =  [(''EISupBlock'', ''PrNamedElement2''), 
        (''EISupSystem'', ''Block''), 
        (''EISupComponent'', ''Block''), 
        (''EISupEComponent'', ''Component''), 
        (''EISupPOComponent'', ''Component''),
        (''EBlockProps'', ''PrFlowPort''), (''EComponentVars'', ''PrVariable''), 
        (''EComponentKind'', ''ComponentKind''), (''EEComponentModelTy'', ''ModelKind''),
        (''EEComponentPlatform'', ''Platform''), 
        (''ERPrNamedElement2'', ''PrNamedElement2''),
        (''ERPrFlowPort'', ''PrFlowPort''), (''ERPrVariable'', ''PrVariable'')],
      ntyG =[(''PrNamedElement2'', nprxy), (''PrFlowPort'', nprxy), (''Block'', nnrml), 
      (''ComponentKind'', nenum), (''System'', nnrml), (''Component'', nnrml), 
      (''ModelKind'', nenum), (''Platform'', nenum), (''EComponent'', nnrml), 
      (''POComponent'', nnrml),
      (''PrVariable'', nprxy)],
      etyG =[(''EISupBlock'', einh), (''EISupSystem'', einh), 
        (''EISupComponent'', einh), 
        (''EISupEComponent'', einh), (''EISupPOComponent'', einh), 
        (''EBlockProps'', ecompuni), (''EComponentVars'', ecompuni), 
        (''EComponentKind'', ereluni),
        (''EEComponentModelTy'', ereluni), 
        (''EEComponentPlatform'', ereluni),
        (''ERPrNamedElement2'', eref), (''ERPrFlowPort'', eref), 
        (''ERPrVariable'', eref)],
      srcmG = [], 
      tgtmG = [(''EBlockProps'', sm *), (''EComponentVars'', sm *),
        (''EComponentKind'', sm (val 1)), (''EEComponentModelTy'', sm (val 1)),
        (''EEComponentPlatform'', sm (val 1))]\<rparr>"

axiomatization
where
  Es_SG_F_Blocks: "Es (toSGr SG_F_Blocks) \<subseteq> E_A"
  and Ns_SG_F_Blocks: "Ns (toSGr SG_F_Blocks) \<subseteq> V_A"

value "consInh SG_F_Blocks"

lemma wf_SG_F_Blocks: "is_wf_sg (toSGr SG_F_Blocks)"
  proof -
    have h_wf_g: "is_wf_g (toSGr SG_F_Blocks)"
      using Ns_SG_F_Blocks Es_SG_F_Blocks 
      by (auto simp add: is_wf_g_def SG_F_Blocks_def ftotal_on_def toSGr_def)
    show "is_wf_sg (toSGr SG_F_Blocks)"
    proof (simp add: is_wf_sg_def, rule conjI)
      show "is_wf_g (toSGr SG_F_Blocks)"
      using h_wf_g by simp
    next
      apply_end(rule conjI)
      show "ftotal_on (nty (toSGr SG_F_Blocks)) (Ns (toSGr SG_F_Blocks)) SGNTy_set"
        by (auto simp add: SG_F_Blocks_def ftotal_on_def SGNTy_set_def toSGr_def)
    next
      apply_end(rule conjI)
      show "ftotal_on (ety (toSGr SG_F_Blocks)) (Es (toSGr SG_F_Blocks)) SGETy_set"
        by (auto simp add: SG_F_Blocks_def ftotal_on_def SGETy_set_def toSGr_def)
    next
      apply_end(rule conjI)
      show "dom (srcm (toSGr SG_F_Blocks)) = EsTy (toSGr SG_F_Blocks) {Some erelbi, Some ecompbi}"
        by (auto simp add: SG_F_Blocks_def EsTy_def vimage_def toSGr_def)
    next
      apply_end(rule conjI)
      show "dom (tgtm (toSGr SG_F_Blocks)) 
        = EsTy (toSGr SG_F_Blocks) {Some erelbi, Some ereluni, Some ecompbi, Some ecompuni}"
        by (auto simp add: SG_F_Blocks_def EsTy_def vimage_def toSGr_def)
    next
      apply_end(rule conjI)
      show "EsR (toSGr SG_F_Blocks) \<subseteq> EsId (toSGr SG_F_Blocks)"
      proof
        fix x
        assume " x \<in> EsR (toSGr SG_F_Blocks)"
        then show "x \<in> EsId (toSGr SG_F_Blocks)"
        by (auto simp add: EsR_def SG_F_Blocks_def EsTy_def EsId_def vimage_def toSGr_def
          split: if_splits)
      qed
    next
      apply_end(rule conjI)
      show "srcm (toSGr SG_F_Blocks) ` EsTy (toSGr SG_F_Blocks) {Some ecompbi}
        \<subseteq> {Some (rm 0 (val (Suc 0))), Some (sm (val (Suc 0)))}"
        by (auto simp add: SG_F_Blocks_def EsTy_def vimage_def toSGr_def)
    next
      show "acyclicGr (inhG (toSGr SG_F_Blocks))"
        using h_wf_g by (simp add: inh_eq acyclicGr_def rtrancl_in inh_eq_consInh)(eval)
    qed
  qed

(*'F_Blocks' Fragment*)
definition F_Blocks :: "Fr_ls"
where
   "F_Blocks \<equiv> \<lparr>sg_ls = SG_F_Blocks, 
    tr_ls = [(''ERPrNamedElement2'', ''PrNamedElement''), 
      (''ERPrFlowPort'', ''FlowPort''), (''ERPrVariable'', ''Variable'')]\<rparr>"


value "consRefs F_Blocks"

(* Well-formedness proof obligation of fragments"*)
lemma wf_F_Blocks: "is_wf_fr (toFr F_Blocks)"
  proof -
    let ?refs_F_Blocks = "{(''PrNamedElement2'', ''PrNamedElement''), 
      (''PrFlowPort'', ''FlowPort''),
      (''PrVariable'', ''Variable'')}"
    have h_ftotal_tr: "ftotal_on (tr (toFr F_Blocks)) (EsRP (sg (toFr F_Blocks))) V_A"
      proof (simp add: ftotal_on_def)
        apply_end(rule conjI)
        show "dom (tr (toFr F_Blocks)) = EsRP (sg (toFr F_Blocks))"
        proof
          show "dom (tr (toFr F_Blocks)) \<subseteq> EsRP (sg (toFr F_Blocks))"
            by (simp add: F_Blocks_def SG_F_Blocks_def toSGr_def toFr_def SG_F_Common_def 
          SG_F_Props_def EsRP_def EsR_def NsP_def EsTy_def NsTy_def) 
        next
          show "EsRP (sg (toFr F_Blocks)) \<subseteq> dom (tr (toFr F_Blocks))"
            by (auto simp add: F_Blocks_def SG_F_Blocks_def toSGr_def toFr_def SG_F_Common_def 
          SG_F_Props_def EsRP_def EsR_def NsP_def EsTy_def NsTy_def)
        qed
      next
        show "ran (tr (toFr F_Blocks)) \<subseteq> V_A"
        using Ns_SG_F_Blocks Ns_SG_F_Props
        by (simp add: F_Blocks_def SG_F_Blocks_def toSGr_def toFr_def SG_F_Common_def 
          SG_F_Props_def)
      qed
    from wf_SG_F_Blocks have hb: "is_wf_sg (sg (toFr F_Blocks))"
      by (simp add: toFr_def F_Blocks_def)
    have refs_F_Blocks: "refs (toFr F_Blocks) = ?refs_F_Blocks"
      using h_ftotal_tr hb by (simp add: refs_eq_consRefs, eval)
    show ?thesis
    proof (simp add: is_wf_fr_def, rule conjI)
      show "is_wf_sg (sg (toFr F_Blocks))"
        by (simp add: hb)
    next 
      apply_end(rule conjI)
      show "ftotal_on (tr (toFr F_Blocks)) (EsRP (sg (toFr F_Blocks))) V_A"
        using h_ftotal_tr by (simp)
    next
      apply_end(rule conjI)
      show "inj_on (src (sg (toFr F_Blocks))) (EsRP (sg (toFr F_Blocks)))"
        by (simp add: F_Blocks_def inj_on_def EsRP_def EsR_def NsP_def EsTy_def NsTy_def 
          SG_F_Blocks_def toFr_def toSGr_def) 
    next
      apply_end(rule conjI)
      show "ran (src (sg (toFr F_Blocks)) |` EsRP (sg (toFr F_Blocks))) = NsP (sg (toFr F_Blocks))"
      proof
        show "ran (src (sg (toFr F_Blocks)) |` EsRP (sg (toFr F_Blocks))) \<subseteq> NsP (sg (toFr F_Blocks))"
        by (simp add: F_Blocks_def SG_F_Blocks_def inj_on_def EsRP_def EsR_def 
          EsTy_def NsP_def NsTy_def vimage_def toFr_def toSGr_def)
      next
        show "NsP (sg (toFr F_Blocks)) \<subseteq> ran (src (sg (toFr F_Blocks)) |` EsRP (sg (toFr F_Blocks)))"
          by (auto simp add: F_Blocks_def SG_F_Blocks_def inj_on_def EsRP_def EsR_def 
            EsTy_def NsP_def NsTy_def vimage_def toFr_def toSGr_def)
      qed
    next
      apply_end(rule conjI)
      show "\<forall>v. v \<in> NsP (sg (toFr F_Blocks)) \<longrightarrow> nonPRefsOf (toFr F_Blocks) v \<noteq> {}"
      proof (rule allI, rule impI)
        fix v
        assume "v \<in> NsP (sg (toFr F_Blocks))"
        then have h1: "v = ''PrVariable'' \<or> v = ''PrFlowPort'' \<or> v = ''PrNamedElement2''"
          by (simp add: NsP_def F_Blocks_def NsTy_def SG_F_Blocks_def toFr_def toSGr_def 
            split: if_splits)
        then show "nonPRefsOf (toFr F_Blocks) v \<noteq> {}"
        proof
          assume "v = ''PrVariable''"
          then show "nonPRefsOf (toFr F_Blocks) v \<noteq> {}"
          by (simp add: nonPRefsOf_def refsOf_def refs_F_Blocks NsP_def NsTy_def)
            (simp add: F_Blocks_def SG_F_Blocks_def toFr_def toSGr_def)
        next
          assume "v = ''PrFlowPort'' \<or> v = ''PrNamedElement2''"
          then show "nonPRefsOf (toFr F_Blocks) v \<noteq> {}"
          proof
            assume "v = ''PrFlowPort''"
            then show "nonPRefsOf (toFr F_Blocks) v \<noteq> {}"
            by (simp add: nonPRefsOf_def refsOf_def refs_F_Blocks NsP_def NsTy_def)
              (simp add: F_Blocks_def SG_F_Blocks_def toFr_def toSGr_def)
          next
            assume "v = ''PrNamedElement2''"
            then show "nonPRefsOf (toFr F_Blocks) v \<noteq> {}"
            by (simp add: nonPRefsOf_def refsOf_def refs_F_Blocks NsP_def NsTy_def)
              (simp add: F_Blocks_def SG_F_Blocks_def toFr_def toSGr_def)
          qed
        qed
      qed
    next
      apply_end(rule conjI)
      show "acyclic_fr (toFr F_Blocks)"
        proof -
          from wf_SG_F_Blocks have "acyclic (inh (sg (toFr F_Blocks)))"
            by (simp add: is_wf_sg_def acyclicGr_def inh_def F_Blocks_def toFr_def)
          then show "acyclic_fr (toFr F_Blocks)"
          proof (simp add: acyclic_fr_def)
            assume h1: "acyclic (inh (sg (toFr F_Blocks)))"
            have h2: "is_wf_g (toSGr (sg_ls (F_Blocks)))"
              using wf_SG_F_Blocks by (simp add: F_Blocks_def is_wf_sg_def)
            have h3: "Domain (inh (sg (toFr F_Blocks))) \<inter> Domain (refs (toFr F_Blocks)) = {}"
              using h2 
                by (simp add: refs_F_Blocks)(simp add: toFr_def inh_eq_consInh, eval)
            have h4: "Range (refs (toFr F_Blocks)) \<inter> Domain (inh (sg (toFr F_Blocks))) = {}"
              using h2 by (simp add: refs_F_Blocks)(simp add: toFr_def inh_eq_consInh, eval)
            have h5: "acyclic(refs (toFr F_Blocks))"
              by (simp add: refs_F_Blocks)(auto simp add: rtrancl_in acyclic_def)
            from h1 h3 h4 h5 show "acyclic (inh (sg (toFr F_Blocks)) \<union> refs (toFr F_Blocks))"
              by (simp add: acyclic_Un)
          qed
        qed
      next
      show "proxies_dont_inherit (toFr F_Blocks)"
        by (simp add: proxies_dont_inherit_def  EsI_def NsP_def NsTy_def EsTy_def vimage_def
          F_Blocks_def SG_F_Blocks_def toFr_def toSGr_def)
    qed
  qed

(*Type Fragment corresponding to 'F_Blocks' *)
definition TF_Blocks :: "TFr_ls"
where
   "TF_Blocks = \<lparr>fr_ls = F_Blocks, iet_ls = []\<rparr>"

(* Well-formedness proof obligation of 'TF_Blocks'*)
lemma wf_TF_Blocks: "is_wf_tfr (toTFr TF_Blocks)"
  proof (simp add: is_wf_tfr_def, rule conjI)
    show "is_wf_fr (fr (toTFr TF_Blocks))"
      by (simp add: TF_Blocks_def wf_F_Blocks toTFr_def)
  next
    apply_end (rule conjI)
    show "dom (iet (toTFr TF_Blocks)) \<subseteq> EsA (sg (fr (toTFr TF_Blocks)))"
      by (simp add: TF_Blocks_def toTFr_def)
  next
    show "ftotal_on (iety (toTFr TF_Blocks)) (EsA (sg (fr (toTFr  TF_Blocks)))) SGETy_set"
    proof (simp add: ftotal_on_def, rule conjI)
      show "dom (iety (toTFr TF_Blocks)) = EsA (sg (fr (toTFr TF_Blocks)))"
      proof
        show "dom (iety (toTFr TF_Blocks)) \<subseteq> EsA (sg (fr (toTFr TF_Blocks)))"
          by (simp add: TF_Blocks_def EsA_def EsTy_def vimage_def F_Blocks_def
            SG_F_Blocks_def toFr_def toSGr_def iety_def toTFr_def)
      next
        show "EsA (sg (fr (toTFr TF_Blocks))) \<subseteq> dom (iety (toTFr TF_Blocks))"
          by (auto simp add: TF_Blocks_def EsA_def EsTy_def vimage_def F_Blocks_def
            SG_F_Blocks_def toFr_def toSGr_def iety_def)
      qed
    next
      show "ran (iety (toTFr TF_Blocks)) \<subseteq> SGETy_set"
      proof
        fix x
        assume "x \<in> ran (iety (toTFr TF_Blocks))"
        then show "x \<in> SGETy_set"
        by (simp add: TF_Blocks_def F_Blocks_def EsA_def EsTy_def vimage_def
          SG_F_Blocks_def toFr_def toSGr_def SGETy_set_def iety_def toTFr_def)
        (erule disjE, simp_all)
      qed
    qed
  qed

(*SG of fragment 'F_VTypes'*)
definition SG_F_VTypes :: "SGr_ls"
where
  "SG_F_VTypes = \<lparr>NsG=[''PrNamedElement3'', ''PrProperty'', ''PrPType'', ''PrString'', 
    ''Literal'', ''ValueType'', ''Enumeration'', ''DType'', 
    ''StrtType'', ''UnitType''], 
      EsG = [''EISupLiteral'', ''EISupValueType'', ''EISupEnumeration'', ''EISupDType'', 
        ''EISupStrtType'', ''EISupUnitType'', ''EProps'', ''ELiterals'', ''ESuper'', 
        ''EUnit'', ''ERPrNamedElement3'',
        ''ERPrProperty'', ''ERPrPType'', ''ERPrString''], 
      srcG =  [(''EISupLiteral'', ''Literal''), (''EISupValueType'', ''ValueType''), 
        (''EISupEnumeration'', ''Enumeration''), 
        (''EISupDType'', ''DType''), (''EISupStrtType'', ''StrtType''),
        (''EISupUnitType'', ''UnitType''), (''EProps'', ''StrtType''), 
        (''ELiterals'', ''Enumeration''), (''ESuper'', ''DType''), 
        (''EUnit'', ''UnitType''),
        (''ERPrNamedElement3'', ''PrNamedElement3''), 
        (''ERPrProperty'', ''PrProperty''), (''ERPrPType'', ''PrPType''), 
        (''ERPrString'', ''PrString'')], 
      tgtG =  [(''EISupLiteral'', ''PrNamedElement3''), 
        (''EISupValueType'', ''PrNamedElement3''), 
        (''EISupEnumeration'', ''ValueType''), 
        (''EISupDType'', ''ValueType''), (''EISupStrtType'', ''ValueType''),
        (''EISupUnitType'', ''DType''), (''EProps'', ''PrProperty''), 
        (''ELiterals'', ''Literal''), (''ESuper'', ''PrPType''),
        (''EUnit'', ''PrString''),
        (''ERPrNamedElement3'', ''PrNamedElement3''), 
        (''ERPrProperty'', ''PrProperty''), (''ERPrPType'', ''PrPType''), 
        (''ERPrString'', ''PrString'')],
      ntyG =[(''PrNamedElement3'', nprxy), (''PrProperty'', nprxy), 
        (''PrPType'', nprxy), 
        (''Literal'', nnrml), (''ValueType'', nabst), 
        (''Enumeration'', nnrml), (''DType'', nnrml), (''StrtType'', nnrml), 
        (''UnitType'', nnrml), (''PrString'', nprxy)],
      etyG =[(''EISupLiteral'', einh), (''EISupValueType'', einh), 
        (''EISupEnumeration'', einh), 
        (''EISupDType'', einh), (''EISupStrtType'', einh), 
        (''EISupUnitType'', einh), (''EProps'', ecompuni), (''ELiterals'', ecompuni),
        (''ESuper'', ereluni), (''EUnit'', ereluni), (''ERPrNamedElement3'', eref),
        (''ERPrProperty'', eref), (''ERPrPType'', eref), (''ERPrString'', eref)],
      srcmG = [], 
      tgtmG = [(''EProps'', sm *), (''ELiterals'', sm *),
        (''ESuper'', sm *), (''EUnit'', sm (val 1))]\<rparr>"

axiomatization
where
  Es_SG_F_VTypes: "Es (toSGr SG_F_VTypes) \<subseteq> E_A"
  and Ns_SG_F_VTypes: "Ns (toSGr SG_F_VTypes) \<subseteq> V_A"

value "consInh SG_F_VTypes"

lemma wf_SG_F_VTypes: "is_wf_sg (toSGr SG_F_VTypes)"
  proof -
    have h_wf_g: "is_wf_g (toSGr SG_F_VTypes)"
      using Ns_SG_F_VTypes Es_SG_F_VTypes
      by (auto simp add: is_wf_g_def SG_F_VTypes_def ftotal_on_def toSGr_def)
    show "is_wf_sg (toSGr SG_F_VTypes)"
    proof (simp add: is_wf_sg_def, rule conjI)
      show "is_wf_g (toSGr SG_F_VTypes)"
      using h_wf_g by simp
    next
      apply_end(rule conjI)
      show "ftotal_on (nty (toSGr SG_F_VTypes)) (Ns (toSGr SG_F_VTypes)) SGNTy_set"
        by (auto simp add: SG_F_VTypes_def ftotal_on_def SGNTy_set_def toSGr_def)
    next
      apply_end(rule conjI)
      show "ftotal_on (ety (toSGr SG_F_VTypes)) (Es (toSGr SG_F_VTypes)) SGETy_set"
        by (auto simp add: SG_F_VTypes_def ftotal_on_def SGETy_set_def toSGr_def)
    next
      apply_end(rule conjI)
      show "dom (srcm (toSGr SG_F_VTypes)) = EsTy (toSGr SG_F_VTypes) {Some erelbi, Some ecompbi}"
        by (auto simp add: SG_F_VTypes_def EsTy_def vimage_def toSGr_def)
    next
      apply_end(rule conjI)
      show "dom (tgtm (toSGr SG_F_VTypes)) 
        = EsTy (toSGr SG_F_VTypes) {Some erelbi, Some ereluni, Some ecompbi, Some ecompuni}"
        by (auto simp add: SG_F_VTypes_def EsTy_def vimage_def toSGr_def)
    next
      apply_end(rule conjI)
      show "EsR (toSGr SG_F_VTypes) \<subseteq> EsId (toSGr SG_F_VTypes)"
      proof
        fix x
        assume " x \<in> EsR (toSGr SG_F_VTypes)"
        then show "x \<in> EsId (toSGr SG_F_VTypes)"
        by (auto simp add: EsR_def SG_F_VTypes_def EsTy_def EsId_def vimage_def toSGr_def
          split: if_splits)
      qed
    next
      apply_end(rule conjI)
      show "srcm (toSGr SG_F_VTypes) ` EsTy (toSGr SG_F_VTypes) {Some ecompbi}
        \<subseteq> {Some (rm 0 (val (Suc 0))), Some (sm (val (Suc 0)))}"
        by (auto simp add: SG_F_VTypes_def EsTy_def vimage_def toSGr_def)
    next
      show "acyclicGr (inhG (toSGr SG_F_VTypes))"
        using h_wf_g by (simp add: inh_eq acyclicGr_def rtrancl_in inh_eq_consInh)(eval)
    qed
  qed

(*'F_VTypes' Fragment*)
definition F_VTypes :: "Fr_ls"
where
   "F_VTypes \<equiv> \<lparr>sg_ls = SG_F_VTypes, 
    tr_ls = [(''ERPrNamedElement3'', ''PrNamedElement''), 
      (''ERPrProperty'', ''Property''), 
      (''ERPrPType'', ''PType''), (''ERPrString'', ''String'')]\<rparr>"

value "consRefs F_VTypes"

(* Well-formedness proof obligation of fragments"*)
lemma wf_F_VTypes: "is_wf_fr (toFr F_VTypes)"
  proof -
    let ?refs_F_VTypes = "{(''PrNamedElement3'', ''PrNamedElement''), 
      (''PrProperty'', ''Property''),
      (''PrPType'', ''PType''), (''PrString'', ''String'')}"
    have h_ftotal_tr: "ftotal_on (tr (toFr F_VTypes)) (EsRP (sg (toFr F_VTypes))) V_A"
      proof (simp add: ftotal_on_def)
        apply_end(rule conjI)
        show "dom (tr (toFr F_VTypes)) = EsRP (sg (toFr F_VTypes))"
        proof
          show "dom (tr (toFr F_VTypes)) \<subseteq> EsRP (sg (toFr F_VTypes))"
            by (simp add: F_VTypes_def SG_F_VTypes_def toSGr_def toFr_def SG_F_Common_def 
          SG_F_Props_def EsRP_def EsR_def NsP_def EsTy_def NsTy_def) 
        next
          show "EsRP (sg (toFr F_VTypes)) \<subseteq> dom (tr (toFr F_VTypes))"
            by (auto simp add: F_VTypes_def SG_F_VTypes_def toSGr_def toFr_def SG_F_Common_def 
          SG_F_Props_def EsRP_def EsR_def NsP_def EsTy_def NsTy_def)
        qed
      next
        show "ran (tr (toFr F_VTypes)) \<subseteq> V_A"
        using Ns_SG_F_VTypes Ns_SG_F_Props Ns_SG_F_PTypes
        by (simp add: F_VTypes_def SG_F_Props_def toSGr_def toFr_def SG_F_VTypes_def
          SG_F_PTypes_def)
      qed
    from wf_SG_F_VTypes have hb: "is_wf_sg (sg (toFr F_VTypes))"
      by (simp add: toFr_def F_VTypes_def)
    have refs_F_VTypes: "refs (toFr F_VTypes) = ?refs_F_VTypes"
      using h_ftotal_tr hb by (simp add: refs_eq_consRefs, eval)
    show ?thesis
    proof (simp add: is_wf_fr_def, rule conjI)
      show "is_wf_sg (sg (toFr F_VTypes))"
        by (simp add: hb)
    next 
      apply_end(rule conjI)
      show "ftotal_on (tr (toFr F_VTypes)) (EsRP (sg (toFr F_VTypes))) V_A"
        using h_ftotal_tr by (simp)
    next
      apply_end(rule conjI)
      show "inj_on (src (sg (toFr F_VTypes))) (EsRP (sg (toFr F_VTypes)))"
        by (simp add: F_VTypes_def inj_on_def EsRP_def EsR_def NsP_def EsTy_def NsTy_def 
          SG_F_VTypes_def toFr_def toSGr_def) 
    next
      apply_end(rule conjI)
      show "ran (src (sg (toFr F_VTypes)) |` EsRP (sg (toFr F_VTypes))) = NsP (sg (toFr F_VTypes))"
      proof
        show "ran (src (sg (toFr F_VTypes)) |` EsRP (sg (toFr F_VTypes))) \<subseteq> NsP (sg (toFr F_VTypes))"
        by (simp add: F_VTypes_def SG_F_VTypes_def inj_on_def EsRP_def EsR_def 
          EsTy_def NsP_def NsTy_def vimage_def toFr_def toSGr_def)
      next
        show "NsP (sg (toFr F_VTypes)) \<subseteq> ran (src (sg (toFr F_VTypes)) |` EsRP (sg (toFr F_VTypes)))"
          by (auto simp add: F_VTypes_def SG_F_VTypes_def inj_on_def EsRP_def EsR_def 
            EsTy_def NsP_def NsTy_def vimage_def toFr_def toSGr_def)
      qed
    next
      apply_end(rule conjI)
      show "\<forall>v. v \<in> NsP (sg (toFr F_VTypes)) \<longrightarrow> nonPRefsOf (toFr F_VTypes) v \<noteq> {}"
      proof (rule allI, rule impI)
        fix v
        assume "v \<in> NsP (sg (toFr F_VTypes))"
        then have h1: "v = ''PrString'' \<or> v = ''PrProperty'' \<or> v = ''PrPType''
          \<or> v = ''PrNamedElement3''"
          by (simp add: NsP_def F_VTypes_def NsTy_def SG_F_VTypes_def toFr_def toSGr_def 
            split: if_splits)
        then show "nonPRefsOf (toFr F_VTypes) v \<noteq> {}"
        proof 
          assume "v = ''PrString''"
          then show "nonPRefsOf (toFr F_VTypes) v \<noteq> {}"
          by (simp add: nonPRefsOf_def refsOf_def refs_F_VTypes NsP_def NsTy_def)
            (simp add: F_VTypes_def SG_F_VTypes_def toFr_def toSGr_def)
        next
          assume "v = ''PrProperty'' \<or> v = ''PrPType'' \<or> v = ''PrNamedElement3''"
          then show "nonPRefsOf (toFr F_VTypes) v \<noteq> {}"
          proof
            assume "v = ''PrProperty''"
            then show "nonPRefsOf (toFr F_VTypes) v \<noteq> {}"
            by (simp add: nonPRefsOf_def refsOf_def refs_F_VTypes NsP_def NsTy_def)
              (simp add: F_VTypes_def SG_F_VTypes_def toFr_def toSGr_def)
          next
            assume "v = ''PrPType'' \<or> v = ''PrNamedElement3''"
            then show "nonPRefsOf (toFr F_VTypes) v \<noteq> {}"
            proof
              assume "v = ''PrPType''"
              then show "nonPRefsOf (toFr F_VTypes) v \<noteq> {}"
              by (simp add: nonPRefsOf_def refsOf_def refs_F_VTypes NsP_def NsTy_def)
              (simp add: F_VTypes_def SG_F_VTypes_def toFr_def toSGr_def)
            next
              assume "v = ''PrNamedElement3''"
              then show "nonPRefsOf (toFr F_VTypes) v \<noteq> {}"
              by (simp add: nonPRefsOf_def refsOf_def refs_F_VTypes NsP_def NsTy_def)
                (simp add: F_VTypes_def SG_F_VTypes_def toFr_def toSGr_def)
            qed
          qed
        qed
      qed
    next
      apply_end(rule conjI)
      show "acyclic_fr (toFr F_VTypes)"
        proof -
          from wf_SG_F_VTypes have "acyclic (inh (sg (toFr F_VTypes)))"
            by (simp add: is_wf_sg_def acyclicGr_def inh_def F_VTypes_def toFr_def)
          then show "acyclic_fr (toFr F_VTypes)"
          proof (simp add: acyclic_fr_def)
            assume h1: "acyclic (inh (sg (toFr F_VTypes)))"
            have h2: "is_wf_g (toSGr (sg_ls (F_VTypes)))"
              using wf_SG_F_VTypes by (simp add: F_VTypes_def is_wf_sg_def)
            have h3: "Domain (inh (sg (toFr F_VTypes))) \<inter> Domain (refs (toFr F_VTypes)) = {}"
              using h2 
                by (simp add: refs_F_VTypes)(simp add: toFr_def inh_eq_consInh, eval)
            have h4: "Range (refs (toFr F_VTypes)) \<inter> Domain (inh (sg (toFr F_VTypes))) = {}"
              using h2 by (simp add: refs_F_VTypes)(simp add: toFr_def inh_eq_consInh, eval)
            have h5: "acyclic(refs (toFr F_VTypes))"
              by (simp add: refs_F_VTypes)(auto simp add: rtrancl_in acyclic_def)
            from h1 h3 h4 h5 show "acyclic (inh (sg (toFr F_VTypes)) \<union> refs (toFr F_VTypes))"
              by (simp add: acyclic_Un)
          qed
        qed
      next
      show "proxies_dont_inherit (toFr F_VTypes)"
        by (simp add: proxies_dont_inherit_def  EsI_def NsP_def NsTy_def EsTy_def vimage_def
          F_VTypes_def SG_F_VTypes_def toFr_def toSGr_def)
    qed
  qed

(*Type Fragment corresponding to 'F_VTypes' *)
definition TF_VTypes :: "TFr_ls"
where
   "TF_VTypes = \<lparr>fr_ls = F_VTypes, iet_ls = []\<rparr>"

(* Well-formedness proof obligation of 'TF_VTypes'*)
lemma wf_TF_VTypes: "is_wf_tfr (toTFr TF_VTypes)"
  proof (simp add: is_wf_tfr_def, rule conjI)
    show "is_wf_fr (fr (toTFr TF_VTypes))"
      by (simp add: TF_VTypes_def wf_F_VTypes toTFr_def)
  next
    apply_end (rule conjI)
    show "dom (iet (toTFr TF_VTypes)) \<subseteq> EsA (sg (fr (toTFr TF_VTypes)))"
      by (simp add: TF_VTypes_def toTFr_def)
  next
    show "ftotal_on (iety (toTFr TF_VTypes)) (EsA (sg (fr (toTFr TF_VTypes)))) SGETy_set"
    proof (simp add: ftotal_on_def, rule conjI)
      show "dom (iety (toTFr TF_VTypes)) = EsA (sg (fr (toTFr TF_VTypes)))"
      proof
        show "dom (iety (toTFr TF_VTypes)) \<subseteq> EsA (sg (fr (toTFr TF_VTypes)))"
          by (simp add: TF_VTypes_def EsA_def EsTy_def vimage_def F_VTypes_def
            SG_F_Blocks_def toFr_def toSGr_def iety_def toTFr_def)
      next
        show "EsA (sg (fr (toTFr TF_VTypes))) \<subseteq> dom (iety (toTFr TF_VTypes))"
          by (auto simp add: TF_VTypes_def EsA_def EsTy_def vimage_def F_VTypes_def
            SG_F_Blocks_def toFr_def toSGr_def iety_def toTFr_def)
      qed
    next
      show "ran (iety (toTFr TF_VTypes)) \<subseteq> SGETy_set"
      proof
        fix x
        assume "x \<in> ran (iety (toTFr TF_VTypes))"
        then show "x \<in> SGETy_set"
        by (simp add: TF_VTypes_def F_VTypes_def EsA_def EsTy_def vimage_def
          SG_F_VTypes_def toFr_def toSGr_def SGETy_set_def iety_def toTFr_def)
          (erule disjE, simp_all)
      qed
    qed
  qed

(*SG of fragment 'F_Comps'*)
definition SG_F_Comps :: "SGr_ls"
where
  "SG_F_Comps = \<lparr>NsG=[''PrBlock'', ''PrNat'', ''Composition'', ''Mult'', ''MultRange'', 
    ''MultSingle'', ''MultVal'', ''MultValNum'', ''MultValMany''], 
      EsG = [''EISupMultSingle'', ''EISupMultRange'', ''EISupMultValNum'', 
        ''EISupMultValMany'', ''Eval'', ''Elb'', ''Eub'', ''En'', ''ERPrBlock'', ''ERPrNat''], 
      srcG =  [(''EISupMultSingle'', ''MultSingle''), (''EISupMultRange'', ''MultRange''), 
        (''EISupMultValNum'', ''MultValNum''), (''EISupMultValMany'', ''MultValMany''),
        (''Eval'', ''MultSingle''), (''Elb'', ''MultRange''), (''Eub'', ''MultRange''),
        (''En'', ''MultValNum''), (''ERPrBlock'', ''PrBlock''), 
        (''ERPrNat'', ''PrNat'')], 
      tgtG =  [(''EISupMultSingle'', ''Mult''), (''EISupMultRange'', ''Mult''), 
        (''EISupMultValNum'', ''MultVal''), (''EISupMultValMany'', ''MultVal''),
        (''Eval'', ''MultVal''), (''Elb'', ''PrNat''), (''Eub'', ''MultVal''),
        (''En'', ''PrNat''), (''ERPrBlock'', ''PrBlock''), 
        (''ERPrNat'', ''PrNat'')],
      ntyG =[(''PrBlock'', nprxy), (''PrNat'', nprxy),  
        (''Composition'', nnrml), (''Mult'', nnrml), 
        (''MultRange'', nnrml), (''MultSingle'', nnrml), (''MultVal'', nnrml), 
        (''MultValNum'', nnrml),
        (''MultValMany'', nnrml)],
      etyG =[(''EISupMultSingle'', einh), (''EISupMultRange'', einh), 
        (''EISupMultValNum'', einh), 
        (''EISupMultValMany'', einh), (''Eval'', ereluni), (''Elb'', ereluni), 
        (''Eub'', ereluni),
        (''En'', ereluni),  (''ERPrBlock'', eref), (''ERPrNat'', eref)],
      srcmG = [], tgtmG = [(''Eval'', sm (val 1)), (''Elb'', sm (val 1)), (''Eub'', sm (val 1)),
        (''En'', sm (val 1))]\<rparr>"

axiomatization
where
  Es_SG_F_Comps: "Es (toSGr SG_F_Comps) \<subseteq> E_A"
  and Ns_SG_F_Comps: "Ns (toSGr SG_F_Comps) \<subseteq> V_A"

value "consInh SG_F_Comps"

lemma wf_SG_F_Comps: "is_wf_sg (toSGr SG_F_Comps)"
  proof -
    have h_wf_g: "is_wf_g (toSGr SG_F_Comps)"
      using Ns_SG_F_Comps Es_SG_F_Comps
      by (auto simp add: is_wf_g_def SG_F_Comps_def ftotal_on_def toSGr_def)
    show "is_wf_sg (toSGr SG_F_Comps)"
    proof (simp add: is_wf_sg_def, rule conjI)
      show "is_wf_g (toSGr SG_F_Comps)"
      using h_wf_g by simp
    next
      apply_end(rule conjI)
      show "ftotal_on (nty (toSGr SG_F_Comps)) (Ns (toSGr SG_F_Comps)) SGNTy_set"
        by (auto simp add: SG_F_Comps_def ftotal_on_def SGNTy_set_def toSGr_def)
    next
      apply_end(rule conjI)
      show "ftotal_on (ety (toSGr SG_F_Comps)) (Es (toSGr SG_F_Comps)) SGETy_set"
        by (auto simp add: SG_F_Comps_def ftotal_on_def SGETy_set_def toSGr_def)
    next
      apply_end(rule conjI)
      show "dom (srcm (toSGr SG_F_Comps)) = EsTy (toSGr SG_F_Comps) {Some erelbi, Some ecompbi}"
        by (auto simp add: SG_F_Comps_def EsTy_def vimage_def toSGr_def)
    next
      apply_end(rule conjI)
      show "dom (tgtm (toSGr SG_F_Comps)) 
        = EsTy (toSGr SG_F_Comps) {Some erelbi, Some ereluni, Some ecompbi, Some ecompuni}"
        by (auto simp add: SG_F_Comps_def EsTy_def vimage_def toSGr_def)
    next
      apply_end(rule conjI)
      show "EsR (toSGr SG_F_Comps) \<subseteq> EsId (toSGr SG_F_Comps)"
        by (auto simp add: EsR_def SG_F_Comps_def EsTy_def EsId_def vimage_def toSGr_def)
    next
      apply_end(rule conjI)
      show "srcm (toSGr SG_F_Comps) ` EsTy (toSGr SG_F_Comps) {Some ecompbi}
        \<subseteq> {Some (rm 0 (val (Suc 0))), Some (sm (val (Suc 0)))}"
        by (auto simp add: SG_F_Comps_def EsTy_def vimage_def toSGr_def)
    next
      show "acyclicGr (inhG (toSGr SG_F_Comps))"
        using h_wf_g by (simp add: inh_eq acyclicGr_def rtrancl_in inh_eq_consInh)(eval)
    qed
  qed

(*'F_Comps' Fragment*)
definition F_Comps :: "Fr_ls"
where
   "F_Comps \<equiv> \<lparr>sg_ls = SG_F_Comps, 
    tr_ls = [(''ERPrBlock'', ''Block''), (''ERPrNat'', ''Nat'')]\<rparr>"

value "consRefs F_Comps"

(* Well-formedness proof obligation of fragments"*)
lemma wf_F_Comps: "is_wf_fr (toFr F_Comps)"
  proof -
    let ?refs_F_Comps = "{(''PrBlock'', ''Block''), (''PrNat'', ''Nat'')}"
    have h_ftotal_tr: "ftotal_on (tr (toFr F_Comps)) (EsRP (sg (toFr F_Comps))) V_A"
      proof (simp add: ftotal_on_def)
        apply_end(rule conjI)
        show "dom (tr (toFr F_Comps)) = EsRP (sg (toFr F_Comps))"
        proof
          show "dom (tr (toFr F_Comps)) \<subseteq> EsRP (sg (toFr F_Comps))"
            by (simp add: F_Comps_def SG_F_Comps_def toSGr_def toFr_def SG_F_Common_def 
          SG_F_Props_def EsRP_def EsR_def NsP_def EsTy_def NsTy_def) 
        next
          show "EsRP (sg (toFr F_Comps)) \<subseteq> dom (tr (toFr F_Comps))"
            by (auto simp add: F_Comps_def SG_F_Comps_def toSGr_def toFr_def SG_F_Common_def 
              SG_F_Props_def EsRP_def EsR_def NsP_def EsTy_def NsTy_def)
        qed
      next
        show "ran (tr (toFr F_Comps)) \<subseteq> V_A"
        using Ns_SG_F_Blocks Ns_SG_F_PTypes
        by (simp add: F_Comps_def SG_F_Blocks_def toSGr_def toFr_def SG_F_PTypes_def)
      qed
    from wf_SG_F_Comps have hb: "is_wf_sg (sg (toFr F_Comps))"
      by (simp add: toFr_def F_Comps_def)
    have refs_F_Comps: "refs (toFr F_Comps) = ?refs_F_Comps"
      using h_ftotal_tr hb by (simp add: refs_eq_consRefs, eval)
    show ?thesis
    proof (simp add: is_wf_fr_def, rule conjI)
      show "is_wf_sg (sg (toFr F_Comps))"
        by (simp add: hb)
    next 
      apply_end(rule conjI)
      show "ftotal_on (tr (toFr F_Comps)) (EsRP (sg (toFr F_Comps))) V_A"
        using h_ftotal_tr by (simp)
    next
      apply_end(rule conjI)
      show "inj_on (src (sg (toFr F_Comps))) (EsRP (sg (toFr F_Comps)))"
        by (simp add: F_Comps_def inj_on_def EsRP_def EsR_def NsP_def EsTy_def NsTy_def 
          SG_F_Comps_def toFr_def toSGr_def) 
    next
      apply_end(rule conjI)
      show "ran (src (sg (toFr F_Comps)) |` EsRP (sg (toFr F_Comps))) = NsP (sg (toFr F_Comps))"
      proof
        show "ran (src (sg (toFr F_Comps)) |` EsRP (sg (toFr F_Comps))) \<subseteq> NsP (sg (toFr F_Comps))"
        by (simp add: F_Comps_def SG_F_Comps_def inj_on_def EsRP_def EsR_def 
          EsTy_def NsP_def NsTy_def vimage_def toFr_def toSGr_def)
      next
        show "NsP (sg (toFr F_Comps)) \<subseteq> ran (src (sg (toFr F_Comps)) |` EsRP (sg (toFr F_Comps)))"
          by (auto simp add: F_Comps_def SG_F_Comps_def inj_on_def EsRP_def EsR_def 
            EsTy_def NsP_def NsTy_def vimage_def toFr_def toSGr_def)
      qed
    next
      apply_end(rule conjI)
      show "\<forall>v. v \<in> NsP (sg (toFr F_Comps)) \<longrightarrow> nonPRefsOf (toFr F_Comps) v \<noteq> {}"
      proof (rule allI, rule impI)
        fix v
        assume "v \<in> NsP (sg (toFr F_Comps))"
        then have h1: "v = ''PrNat'' \<or> v = ''PrBlock''"
          by (simp add: NsP_def F_Comps_def NsTy_def SG_F_Comps_def toFr_def toSGr_def 
            split: if_splits)
        then show "nonPRefsOf (toFr F_Comps) v \<noteq> {}"
        proof 
          assume "v = ''PrNat''"
          then show "nonPRefsOf (toFr F_Comps) v \<noteq> {}"
          by (simp add: nonPRefsOf_def refsOf_def refs_F_Comps NsP_def NsTy_def)
            (simp add: F_Comps_def SG_F_Comps_def toFr_def toSGr_def)
        next
          assume "v = ''PrBlock''"
          then show "nonPRefsOf (toFr F_Comps) v \<noteq> {}"
            by (simp add: nonPRefsOf_def refsOf_def refs_F_Comps NsP_def NsTy_def)
            (simp add: F_Comps_def SG_F_Comps_def toFr_def toSGr_def)
        qed
      qed
    next
      apply_end(rule conjI)
      show "acyclic_fr (toFr F_Comps)"
        proof -
          from wf_SG_F_Comps have "acyclic (inh (sg (toFr F_Comps)))"
            by (simp add: is_wf_sg_def acyclicGr_def inh_def F_Comps_def toFr_def)
          then show "acyclic_fr (toFr F_Comps)"
          proof (simp add: acyclic_fr_def)
            assume h1: "acyclic (inh (sg (toFr F_Comps)))"
            have h2: "is_wf_g (toSGr (sg_ls (F_Comps)))"
              using wf_SG_F_Comps by (simp add: F_Comps_def is_wf_sg_def)
            have h3: "Domain (inh (sg (toFr F_Comps))) \<inter> Domain (refs (toFr F_Comps)) = {}"
              using h2 
                by (simp add: refs_F_Comps)(simp add: toFr_def inh_eq_consInh, eval)
            have h4: "Range (refs (toFr F_Comps)) \<inter> Domain (inh (sg (toFr F_Comps))) = {}"
              using h2 by (simp add: refs_F_Comps)(simp add: toFr_def inh_eq_consInh, eval)
            have h5: "acyclic(refs (toFr F_Comps))"
              by (simp add: refs_F_Comps)(auto simp add: rtrancl_in acyclic_def)
            from h1 h3 h4 h5 show "acyclic (inh (sg (toFr F_Comps)) \<union> refs (toFr F_Comps))"
              by (simp add: acyclic_Un)
          qed
        qed
      next
      show "proxies_dont_inherit (toFr F_Comps)"
        by (simp add: proxies_dont_inherit_def  EsI_def NsP_def NsTy_def EsTy_def vimage_def
          F_Comps_def SG_F_Comps_def toFr_def toSGr_def)
    qed
  qed

(*Type Fragment corresponding to 'F_Comps' *)
definition TF_Comps :: "TFr_ls"
where
   "TF_Comps = \<lparr>fr_ls = F_Comps, iet_ls = []\<rparr>"

(* Well-formedness proof obligation of 'TF_VTypes'*)
lemma wf_TF_Comps: "is_wf_tfr (toTFr TF_Comps)"
  proof (simp add: is_wf_tfr_def, rule conjI)
    show "is_wf_fr (fr (toTFr TF_Comps))"
      by (simp add: TF_Comps_def wf_F_Comps toTFr_def)
  next
    apply_end (rule conjI)
    show "dom (iet (toTFr TF_Comps)) \<subseteq> EsA (sg (fr (toTFr TF_Comps)))"
      by (simp add: TF_Comps_def toTFr_def)
  next
    show "ftotal_on (iety (toTFr TF_Comps)) (EsA (sg (fr (toTFr TF_Comps)))) SGETy_set"
    proof (simp add: ftotal_on_def, rule conjI)
      show "dom (iety (toTFr TF_Comps)) = EsA (sg (fr (toTFr TF_Comps)))"
      proof
        show "dom (iety (toTFr TF_Comps)) \<subseteq> EsA (sg (fr (toTFr TF_Comps)))"
          by (simp add: TF_Comps_def EsA_def EsTy_def vimage_def F_VTypes_def
            SG_F_Comps_def toFr_def toSGr_def iety_def toTFr_def)
      next
        show "EsA (sg (fr (toTFr TF_Comps))) \<subseteq> dom (iety (toTFr TF_Comps))"
          by (auto simp add: TF_Comps_def EsA_def EsTy_def vimage_def  
            toFr_def toSGr_def iety_def)
      qed
    next
      show "ran (iety (toTFr TF_Comps)) \<subseteq> SGETy_set"
      proof
        fix x
        assume "x \<in> ran (iety (toTFr TF_Comps))"
        then show "x \<in> SGETy_set"
        by (simp add: TF_Comps_def F_Comps_def EsA_def EsTy_def vimage_def
          SG_F_Comps_def toFr_def toSGr_def SGETy_set_def iety_def toTFr_def)
      qed
    qed
  qed

(*SG of fragment 'F_ASD'*)
definition SG_F_ASD :: "SGr_ls"
where
  "SG_F_ASD = \<lparr>NsG=[''PrBlock2'', ''PrNamedElement4'', ''PrComposition'', ''PrValueType'', 
    ''ASD''], 
      EsG = [''EISupASD'', ''Eblocks'', ''Ecompositions'', ''Etypes'', 
        ''ERPrBlock2'', ''ERPrNamedElement4'', ''ERPrComposition'', ''ERPrValueType''], 
      srcG =  [(''EISupASD'', ''ASD''), (''Eblocks'', ''ASD''), 
        (''Ecompositions'', ''ASD''), (''Etypes'', ''ASD''),
        (''ERPrBlock2'', ''PrBlock2''), (''ERPrNamedElement4'', ''PrNamedElement4''), 
        (''ERPrComposition'', ''PrComposition''), (''ERPrValueType'', ''PrValueType'')], 
      tgtG =  [(''EISupASD'', ''PrNamedElement4''), 
        (''Eblocks'', ''PrBlock2''), 
        (''Ecompositions'', ''PrComposition''), (''Etypes'', ''PrValueType''),
        (''ERPrBlock2'', ''PrBlock2''), (''ERPrNamedElement4'', ''PrNamedElement4''), 
        (''ERPrComposition'', ''PrComposition''), 
        (''ERPrValueType'', ''PrValueType'')],
      ntyG =[(''PrBlock2'', nprxy), (''PrNamedElement4'', nprxy), 
        (''PrComposition'', nprxy),
        (''PrValueType'', nprxy), (''ASD'', nnrml)],
      etyG =[(''EISupASD'', einh), (''Eblocks'', ecompuni), (''Ecompositions'', ecompuni), 
        (''Etypes'', ecompuni), (''ERPrBlock2'', eref), (''ERPrNamedElement4'', eref),
        (''ERPrComposition'', eref), (''ERPrValueType'', eref)],
      srcmG = [], 
      tgtmG = [(''Eblocks'', sm *), (''Ecompositions'', sm *), (''Etypes'', sm *)]\<rparr>"

axiomatization
where
  Es_SG_F_ASD: "Es (toSGr SG_F_ASD) \<subseteq> E_A"
  and Ns_SG_F_ASD: "Ns (toSGr SG_F_ASD) \<subseteq> V_A"

value "consInh SG_F_ASD"

lemma wf_SG_F_ASD: "is_wf_sg (toSGr SG_F_ASD)"
  proof -
    have h_wf_g: "is_wf_g (toSGr SG_F_ASD)"
      using Ns_SG_F_ASD Es_SG_F_ASD
      by (auto simp add: is_wf_g_def SG_F_ASD_def ftotal_on_def toSGr_def)
    show "is_wf_sg (toSGr SG_F_ASD)"
    proof (simp add: is_wf_sg_def, rule conjI)
      show "is_wf_g (toSGr SG_F_ASD)"
      using h_wf_g by simp
    next
      apply_end(rule conjI)
      show "ftotal_on (nty (toSGr SG_F_ASD)) (Ns (toSGr SG_F_ASD)) SGNTy_set"
        by (auto simp add: SG_F_ASD_def ftotal_on_def SGNTy_set_def toSGr_def)
    next
      apply_end(rule conjI)
      show "ftotal_on (ety (toSGr SG_F_ASD)) (Es (toSGr SG_F_ASD)) SGETy_set"
        by (auto simp add: SG_F_ASD_def ftotal_on_def SGETy_set_def toSGr_def)
    next
      apply_end(rule conjI)
      show "dom (srcm (toSGr SG_F_ASD)) = EsTy (toSGr SG_F_ASD) {Some erelbi, Some ecompbi}"
        by (auto simp add: SG_F_ASD_def EsTy_def vimage_def toSGr_def)
    next
      apply_end(rule conjI)
      show "dom (tgtm (toSGr SG_F_ASD)) 
        = EsTy (toSGr SG_F_ASD) {Some erelbi, Some ereluni, Some ecompbi, Some ecompuni}"
        by (auto simp add: SG_F_ASD_def EsTy_def vimage_def toSGr_def)
    next
      apply_end(rule conjI)
      show "EsR (toSGr SG_F_ASD) \<subseteq> EsId (toSGr SG_F_ASD)"
        by (auto simp add: EsR_def SG_F_ASD_def EsTy_def EsId_def vimage_def toSGr_def)
    next
      apply_end(rule conjI)
      show "srcm (toSGr SG_F_ASD) ` EsTy (toSGr SG_F_ASD) {Some ecompbi}
        \<subseteq> {Some (rm 0 (val (Suc 0))), Some (sm (val (Suc 0)))}"
        by (auto simp add: SG_F_ASD_def EsTy_def vimage_def toSGr_def)
    next
      show "acyclicGr (inhG (toSGr SG_F_ASD))"
        using h_wf_g by (simp add: inh_eq acyclicGr_def rtrancl_in inh_eq_consInh)(eval)
    qed
  qed

(*'F_ASD' Fragment*)
definition F_ASD :: "Fr_ls"
where
   "F_ASD \<equiv> \<lparr>sg_ls = SG_F_ASD, 
    tr_ls = [(''ERPrBlock2'', ''Block''), (''ERPrNamedElement4'', ''NamedElement''),
        (''ERPrComposition'', ''Composition''), (''ERPrValueType'', ''ValueType'')]\<rparr>"

value "consRefs F_ASD"

(* Well-formedness proof obligation of fragments"*)
lemma wf_F_ASD: "is_wf_fr (toFr F_ASD)"
  proof -
    let ?refs_F_ASD = "{(''PrBlock2'', ''Block''), (''PrNamedElement4'', ''NamedElement''),
  (''PrComposition'', ''Composition''), (''PrValueType'', ''ValueType'')}"
    have h_ftotal_tr: "ftotal_on (tr (toFr F_ASD)) (EsRP (sg (toFr F_ASD))) V_A"
      proof (simp add: ftotal_on_def)
        apply_end(rule conjI)
        show "dom (tr (toFr F_ASD)) = EsRP (sg (toFr F_ASD))"
        proof
          show "dom (tr (toFr F_ASD)) \<subseteq> EsRP (sg (toFr F_ASD))"
            by (simp add: F_ASD_def SG_F_ASD_def toSGr_def toFr_def SG_F_Common_def 
          SG_F_Props_def EsRP_def EsR_def NsP_def EsTy_def NsTy_def) 
        next
          show "EsRP (sg (toFr F_ASD)) \<subseteq> dom (tr (toFr F_ASD))"
            by (auto simp add: F_ASD_def SG_F_ASD_def toSGr_def toFr_def SG_F_Common_def 
              SG_F_Props_def EsRP_def EsR_def NsP_def EsTy_def NsTy_def)
        qed
      next
        show "ran (tr (toFr F_ASD)) \<subseteq> V_A"
        using Ns_SG_F_ASD Ns_SG_F_Comps Ns_SG_F_Blocks Ns_SG_F_Common Ns_SG_F_VTypes
        by (simp add: F_ASD_def SG_F_ASD_def toSGr_def toFr_def SG_F_Comps_def 
          SG_F_Blocks_def F_Common_def SG_F_Common_def F_VTypes_def SG_F_VTypes_def)
      qed
    from wf_SG_F_ASD have hb: "is_wf_sg (sg (toFr F_ASD))"
      by (simp add: toFr_def F_ASD_def)
    have refs_F_ASD: "refs (toFr F_ASD) = ?refs_F_ASD"
      using h_ftotal_tr hb by (simp add: refs_eq_consRefs, eval)
    show ?thesis
    proof (simp add: is_wf_fr_def, rule conjI)
      show "is_wf_sg (sg (toFr F_ASD))"
        by (simp add: hb)
    next 
      apply_end(rule conjI)
      show "ftotal_on (tr (toFr F_ASD)) (EsRP (sg (toFr F_ASD))) V_A"
        using h_ftotal_tr by (simp)
    next
      apply_end(rule conjI)
      show "inj_on (src (sg (toFr F_ASD))) (EsRP (sg (toFr F_ASD)))"
        by (simp add: F_ASD_def inj_on_def EsRP_def EsR_def NsP_def EsTy_def NsTy_def 
          SG_F_ASD_def toFr_def toSGr_def) 
    next
      apply_end(rule conjI)
      show "ran (src (sg (toFr F_ASD)) |` EsRP (sg (toFr F_ASD))) = NsP (sg (toFr F_ASD))"
      proof
        show "ran (src (sg (toFr F_ASD)) |` EsRP (sg (toFr F_ASD))) \<subseteq> NsP (sg (toFr F_ASD))"
        by (simp add: F_ASD_def SG_F_ASD_def inj_on_def EsRP_def EsR_def 
          EsTy_def NsP_def NsTy_def vimage_def toFr_def toSGr_def)
      next
        show "NsP (sg (toFr F_ASD)) \<subseteq> ran (src (sg (toFr F_ASD)) |` EsRP (sg (toFr F_ASD)))"
          by (auto simp add: F_ASD_def SG_F_ASD_def inj_on_def EsRP_def EsR_def 
            EsTy_def NsP_def NsTy_def vimage_def toFr_def toSGr_def)
      qed
    next
      apply_end(rule conjI)
      show "\<forall>v. v \<in> NsP (sg (toFr F_ASD)) \<longrightarrow> nonPRefsOf (toFr F_ASD) v \<noteq> {}"
      proof (rule allI, rule impI)
        fix v
        assume "v \<in> NsP (sg (toFr F_ASD))"
        then have h1: "v = ''PrValueType'' \<or> v = ''PrNamedElement4'' 
          \<or> v = ''PrComposition'' \<or> v = ''PrBlock2''"
          by (simp add: NsP_def F_ASD_def NsTy_def SG_F_ASD_def toFr_def toSGr_def 
            split: if_splits)
        then show "nonPRefsOf (toFr F_ASD) v \<noteq> {}"
        proof 
          assume "v = ''PrValueType''"
          then show "nonPRefsOf (toFr F_ASD) v \<noteq> {}"
          by (simp add: nonPRefsOf_def refsOf_def refs_F_ASD NsP_def NsTy_def)
            (simp add: F_ASD_def SG_F_ASD_def toFr_def toSGr_def)
        next
          assume "v = ''PrNamedElement4'' \<or> v = ''PrComposition'' \<or> v = ''PrBlock2''"
          then show "nonPRefsOf (toFr F_ASD) v \<noteq> {}"
          proof
            assume "v = ''PrNamedElement4''"
            then show "nonPRefsOf (toFr F_ASD) v \<noteq> {}"
              by (simp add: nonPRefsOf_def refsOf_def refs_F_ASD NsP_def NsTy_def)
              (simp add: F_ASD_def SG_F_ASD_def toFr_def toSGr_def)
          next
            assume "v = ''PrComposition'' \<or> v = ''PrBlock2''"
            then show "nonPRefsOf (toFr F_ASD) v \<noteq> {}"
            proof
              assume "v = ''PrComposition''"
              then show "nonPRefsOf (toFr F_ASD) v \<noteq> {}"
                by (simp add: nonPRefsOf_def refsOf_def refs_F_ASD NsP_def NsTy_def)
                (simp add: F_ASD_def SG_F_ASD_def toFr_def toSGr_def)
            next
              assume "v = ''PrBlock2''"
              then show "nonPRefsOf (toFr F_ASD) v \<noteq> {}"
                by (simp add: nonPRefsOf_def refsOf_def refs_F_ASD NsP_def NsTy_def)
                (simp add: F_ASD_def SG_F_ASD_def toFr_def toSGr_def)
            qed
          qed
        qed
      qed
    next
      apply_end(rule conjI)
      show "acyclic_fr (toFr F_ASD)"
        proof -
          from wf_SG_F_ASD have "acyclic (inh (sg (toFr F_ASD)))"
            by (simp add: is_wf_sg_def acyclicGr_def inh_def F_ASD_def toFr_def)
          then show "acyclic_fr (toFr F_ASD)"
          proof (simp add: acyclic_fr_def)
            assume h1: "acyclic (inh (sg (toFr F_ASD)))"
            have h2: "is_wf_g (toSGr (sg_ls (F_ASD)))"
              using wf_SG_F_ASD by (simp add: F_ASD_def is_wf_sg_def)
            have h3: "Domain (inh (sg (toFr F_ASD))) \<inter> Domain (refs (toFr F_ASD)) = {}"
              using h2 
                by (simp add: refs_F_ASD)(simp add: toFr_def inh_eq_consInh, eval)
            have h4: "Range (refs (toFr F_ASD)) \<inter> Domain (inh (sg (toFr F_ASD))) = {}"
              using h2 by (simp add: refs_F_ASD)(simp add: toFr_def inh_eq_consInh, eval)
            have h5: "acyclic(refs (toFr F_ASD))"
              by (simp add: refs_F_ASD)(auto simp add: rtrancl_in acyclic_def)
            from h1 h3 h4 h5 show "acyclic (inh (sg (toFr F_ASD)) \<union> refs (toFr F_ASD))"
              by (simp add: acyclic_Un)
          qed
        qed
      next
      show "proxies_dont_inherit (toFr F_ASD)"
        by (simp add: proxies_dont_inherit_def  EsI_def NsP_def NsTy_def EsTy_def vimage_def
          F_ASD_def SG_F_ASD_def toFr_def toSGr_def)
    qed
  qed

(*Type Fragment corresponding to 'F_ASD' *)
definition TF_ASD :: "TFr_ls"
where
   "TF_ASD = \<lparr>fr_ls = F_ASD, iet_ls = []\<rparr>"

(* Well-formedness proof obligation of 'TF_ASD'*)
lemma wf_TF_ASD: "is_wf_tfr (toTFr TF_ASD)"
  proof (simp add: is_wf_tfr_def, rule conjI)
    show "is_wf_fr (fr (toTFr TF_ASD))"
      by (simp add: TF_ASD_def wf_F_ASD toTFr_def)
  next
    apply_end (rule conjI)
    show "dom (iet (toTFr TF_ASD)) \<subseteq> EsA (sg (fr (toTFr TF_ASD)))"
      by (simp add: TF_ASD_def toTFr_def)
  next
    show "ftotal_on (iety (toTFr TF_ASD)) (EsA (sg (fr (toTFr TF_ASD)))) SGETy_set"
    proof (simp add: ftotal_on_def, rule conjI)
      show "dom (iety (toTFr TF_ASD)) = EsA (sg (fr (toTFr TF_ASD)))"
      proof
        show "dom (iety (toTFr TF_ASD)) \<subseteq> EsA (sg (fr (toTFr TF_ASD)))"
          by (simp add: TF_ASD_def EsA_def EsTy_def vimage_def F_VTypes_def
            SG_F_Comps_def toFr_def toSGr_def iety_def toTFr_def)
      next
        show "EsA (sg (fr (toTFr TF_ASD))) \<subseteq> dom (iety (toTFr TF_ASD))"
          by (auto simp add: TF_Comps_def EsA_def EsTy_def vimage_def  
            toFr_def toSGr_def iety_def)
      qed
    next
      show "ran (iety (toTFr TF_ASD)) \<subseteq> SGETy_set"
      proof
        fix x
        assume "x \<in> ran (iety (toTFr TF_ASD))"
        then show "x \<in> SGETy_set"
        by (simp add: TF_ASD_def F_ASD_def EsA_def EsTy_def vimage_def
          SG_F_ASD_def toFr_def toSGr_def SGETy_set_def iety_def toTFr_def)
      qed
    qed
  qed

(*SG of fragment 'F_CD'*) 
definition SG_F_CD :: "SGr_ls"
where
  "SG_F_CD = \<lparr>NsG=[''PrBlock3'', ''PrNamedElement5'', ''PrValueType2'', ''PrFlowPort2'',
    ''ConnectionsDiagram'', ''Connector'', ''Port'', ''BlockInstance''], 
      EsG = [''EISupConnectionsDiagram'', ''EISupBlockInstance'', 
        ''ECDblocks'', ''ECDconnectors'', ''EC_src'', ''EC_tgt'', ''EC_flowType'', 
        ''EPortType'', ''EBIports'', ''EBItype'', ''EBIInside'',
        ''ERPrBlock3'', ''ERPrNamedElement5'', ''ERPrValueType2'', ''ERPrFlowPort2''], 
      srcG =  [(''EISupConnectionsDiagram'', ''ConnectionsDiagram''), 
        (''EISupBlockInstance'', ''BlockInstance''), 
        (''ECDblocks'', ''ConnectionsDiagram''), 
        (''ECDconnectors'', ''ConnectionsDiagram''),
        (''EC_src'', ''Connector''), (''EC_tgt'', ''Connector''), 
        (''EC_flowType'', ''Connector''), (''EPortType'', ''Port''), 
        (''EBIports'', ''BlockInstance''), (''EBItype'', ''BlockInstance''),
        (''EBIInside'', ''BlockInstance''),
        (''ERPrBlock3'', ''PrBlock3''),
        (''ERPrNamedElement5'', ''PrNamedElement5''), 
        (''ERPrValueType2'', ''PrValueType2''), (''ERPrFlowPort2'', ''PrFlowPort2'')], 
      tgtG =  [(''EISupConnectionsDiagram'', ''PrNamedElement5''), 
        (''EISupBlockInstance'', ''PrNamedElement5''), 
        (''ECDblocks'', ''BlockInstance''), 
        (''ECDconnectors'', ''Connector''),
        (''EC_src'', ''Port''), (''EC_tgt'', ''Port''), 
        (''EC_flowType'', ''PrValueType2''), (''EPortType'', ''PrFlowPort2''), 
        (''EBIports'', ''Port''), (''EBItype'', ''PrBlock3''),
        (''EBIInside'', ''BlockInstance''),
        (''ERPrBlock3'', ''PrBlock3''),
        (''ERPrNamedElement5'', ''PrNamedElement5''), 
        (''ERPrValueType2'', ''PrValueType2''), (''ERPrFlowPort2'', ''PrFlowPort2'')],
      ntyG =[(''PrBlock3'', nprxy), (''PrNamedElement5'', nprxy), 
        (''PrFlowPort2'', nprxy),
        (''PrValueType2'', nprxy), (''ConnectionsDiagram'', nnrml), 
        (''Connector'', nnrml), (''Port'', nnrml), (''BlockInstance'', nnrml)],
      etyG =[(''EISupConnectionsDiagram'', einh), (''EISupBlockInstance'', einh), 
        (''ECDblocks'', ecompuni), (''ECDconnectors'', ecompuni),
        (''EC_src'', ereluni), (''EC_tgt'', ereluni), (''EC_flowType'', ereluni), 
        (''EPortType'', ereluni), (''EBIports'', ecompuni), (''EBItype'', ereluni),
        (''EBIInside'', ecompuni),
        (''ERPrBlock3'', eref), (''ERPrNamedElement5'', eref), 
        (''ERPrValueType2'', eref), (''ERPrFlowPort2'', eref)],
      srcmG = [], 
      tgtmG = [(''ECDblocks'', sm *), (''ECDconnectors'', sm *), 
        (''EC_src'', sm (val 1)), (''EC_tgt'', sm (val 1)), 
        (''EC_flowType'', sm (val 1)), (''EPortType'', sm (val 1)),
        (''EBIports'', sm *), (''EBItype'', sm (val 1)), (''EBIInside'', sm *)]\<rparr>"

axiomatization
where
  Es_SG_F_CD: "Es (toSGr SG_F_CD) \<subseteq> E_A"
  and Ns_SG_F_CD: "Ns (toSGr SG_F_CD) \<subseteq> V_A"

value "consInh SG_F_CD"

lemma wf_SG_F_CD: "is_wf_sg (toSGr SG_F_CD)"
  proof -
    have h_wf_g: "is_wf_g (toSGr SG_F_CD)"
      using Ns_SG_F_CD Es_SG_F_CD
      by (auto simp add: is_wf_g_def SG_F_CD_def ftotal_on_def toSGr_def)
    show "is_wf_sg (toSGr SG_F_CD)"
    proof (simp add: is_wf_sg_def, rule conjI)
      show "is_wf_g (toSGr SG_F_CD)"
      using h_wf_g by simp
    next
      apply_end(rule conjI)
      show "ftotal_on (nty (toSGr SG_F_CD)) (Ns (toSGr SG_F_CD)) SGNTy_set"
        by (auto simp add: SG_F_CD_def ftotal_on_def SGNTy_set_def toSGr_def)
    next
      apply_end(rule conjI)
      show "ftotal_on (ety (toSGr SG_F_CD)) (Es (toSGr SG_F_CD)) SGETy_set"
        by (auto simp add: SG_F_CD_def ftotal_on_def SGETy_set_def toSGr_def)
    next
      apply_end(rule conjI)
      show "dom (srcm (toSGr SG_F_CD)) = EsTy (toSGr SG_F_CD) {Some erelbi, Some ecompbi}"
        by (auto simp add: SG_F_CD_def EsTy_def vimage_def toSGr_def)
    next
      apply_end(rule conjI)
      show "dom (tgtm (toSGr SG_F_CD)) 
        = EsTy (toSGr SG_F_CD) {Some erelbi, Some ereluni, Some ecompbi, Some ecompuni}"
        by (auto simp add: SG_F_CD_def EsTy_def vimage_def toSGr_def)
    next
      apply_end(rule conjI)
      show "EsR (toSGr SG_F_CD) \<subseteq> EsId (toSGr SG_F_CD)"
      proof
        fix x
        assume "x \<in> EsR (toSGr SG_F_CD)"
        then show "x \<in> EsId (toSGr SG_F_CD)"
          by (auto simp add: EsR_def SG_F_CD_def EsTy_def EsId_def vimage_def toSGr_def 
            split: if_splits)
      qed
    next
      apply_end(rule conjI)
      show "srcm (toSGr SG_F_CD) ` EsTy (toSGr SG_F_CD) {Some ecompbi}
        \<subseteq> {Some (rm 0 (val (Suc 0))), Some (sm (val (Suc 0)))}"
        by (auto simp add: SG_F_CD_def EsTy_def vimage_def toSGr_def)
    next
      show "acyclicGr (inhG (toSGr SG_F_CD))"
        using h_wf_g by (simp add: inh_eq acyclicGr_def rtrancl_in inh_eq_consInh)(eval)
    qed
  qed

(*'F_CD' Fragment*)
definition F_CD :: "Fr_ls"
where
   "F_CD \<equiv> \<lparr>sg_ls = SG_F_CD, 
    tr_ls = [(''ERPrBlock3'', ''Block''), (''ERPrNamedElement5'', ''PrNamedElement2''),
        (''ERPrFlowPort2'', ''PrFlowPort''), (''ERPrValueType2'', ''ValueType'')]\<rparr>"

value "consRefs F_CD"

(* Well-formedness proof obligation of fragments"*)
lemma wf_F_CD: "is_wf_fr (toFr F_CD)"
  proof -
    let ?refs_F_CD = "{(''PrBlock3'', ''Block''), 
      (''PrNamedElement5'', ''PrNamedElement2''),
      (''PrValueType2'', ''ValueType''), 
      (''PrFlowPort2'', ''PrFlowPort'')}"
    have h_ftotal_tr: "ftotal_on (tr (toFr F_CD)) (EsRP (sg (toFr F_CD))) V_A"
      proof (simp add: ftotal_on_def)
        apply_end(rule conjI)
        show "dom (tr (toFr F_CD)) = EsRP (sg (toFr F_CD))"
        proof
          show "dom (tr (toFr F_CD)) \<subseteq> EsRP (sg (toFr F_CD))"
            by (simp add: F_CD_def SG_F_CD_def toSGr_def toFr_def  
          SG_F_Props_def EsRP_def EsR_def NsP_def EsTy_def NsTy_def) 
        next
          show "EsRP (sg (toFr F_CD)) \<subseteq> dom (tr (toFr F_CD))"
            by (auto simp add: F_CD_def SG_F_CD_def toSGr_def toFr_def SG_F_Common_def 
              SG_F_Props_def EsRP_def EsR_def NsP_def EsTy_def NsTy_def)
        qed
      next
        show "ran (tr (toFr F_CD)) \<subseteq> V_A"
        using Ns_SG_F_ASD Ns_SG_F_Comps Ns_SG_F_Blocks Ns_SG_F_Common Ns_SG_F_VTypes
        by (simp add: F_CD_def SG_F_ASD_def toSGr_def toFr_def SG_F_Comps_def 
          SG_F_Blocks_def F_Common_def SG_F_Common_def F_VTypes_def SG_F_VTypes_def)
      qed
    from wf_SG_F_CD have hb: "is_wf_sg (sg (toFr F_CD))"
      by (simp add: toFr_def F_CD_def)
    have refs_F_CD: "refs (toFr F_CD) = ?refs_F_CD"
      using h_ftotal_tr hb by (simp add: refs_eq_consRefs, eval)
    show ?thesis
    proof (simp add: is_wf_fr_def, rule conjI)
      show "is_wf_sg (sg (toFr F_CD))"
        by (simp add: hb)
    next 
      apply_end(rule conjI)
      show "ftotal_on (tr (toFr F_CD)) (EsRP (sg (toFr F_CD))) V_A"
        using h_ftotal_tr by (simp)
    next
      apply_end(rule conjI)
      show "inj_on (src (sg (toFr F_CD))) (EsRP (sg (toFr F_CD)))"
        by (simp add: F_CD_def inj_on_def EsRP_def EsR_def NsP_def EsTy_def NsTy_def 
          SG_F_CD_def toFr_def toSGr_def) 
    next
      apply_end(rule conjI)
      show "ran (src (sg (toFr F_CD)) |` EsRP (sg (toFr F_CD))) = NsP (sg (toFr F_CD))"
      proof
        show "ran (src (sg (toFr F_CD)) |` EsRP (sg (toFr F_CD))) \<subseteq> NsP (sg (toFr F_CD))"
        by (simp add: F_CD_def SG_F_CD_def inj_on_def EsRP_def EsR_def 
          EsTy_def NsP_def NsTy_def vimage_def toFr_def toSGr_def)
      next
        show "NsP (sg (toFr F_CD)) \<subseteq> ran (src (sg (toFr F_CD)) |` EsRP (sg (toFr F_CD)))"
          by (auto simp add: F_CD_def SG_F_CD_def inj_on_def EsRP_def EsR_def 
            EsTy_def NsP_def NsTy_def vimage_def toFr_def toSGr_def)
      qed
    next
      apply_end(rule conjI)
      show "\<forall>v. v \<in> NsP (sg (toFr F_CD)) \<longrightarrow> nonPRefsOf (toFr F_CD) v \<noteq> {}"
      proof (rule allI, rule impI)
        fix v
        assume "v \<in> NsP (sg (toFr F_CD))"
        then have h1: "v = ''PrValueType2'' \<or> v = ''PrNamedElement5'' 
          \<or> v = ''PrFlowPort2'' \<or> v = ''PrBlock3''"
          by (simp add: NsP_def F_CD_def NsTy_def SG_F_CD_def toFr_def toSGr_def 
            split: if_splits)
        then show "nonPRefsOf (toFr F_CD) v \<noteq> {}"
        proof 
          assume "v = ''PrValueType2''"
          then show "nonPRefsOf (toFr F_CD) v \<noteq> {}"
          by (simp add: nonPRefsOf_def refs_F_CD refsOf_def NsP_def NsTy_def)
            (simp add: F_CD_def SG_F_CD_def toFr_def toSGr_def)
        next
          assume "v = ''PrNamedElement5'' \<or> v = ''PrFlowPort2'' \<or> v = ''PrBlock3''"
          then show "nonPRefsOf (toFr F_CD) v \<noteq> {}"
          proof
            assume "v = ''PrNamedElement5''"
            then show "nonPRefsOf (toFr F_CD) v \<noteq> {}"
              by (simp add: nonPRefsOf_def refsOf_def refs_F_CD NsP_def NsTy_def)
              (simp add: F_CD_def SG_F_CD_def toFr_def toSGr_def)
          next
            assume "v = ''PrFlowPort2'' \<or> v = ''PrBlock3''"
            then show "nonPRefsOf (toFr F_CD) v \<noteq> {}"
            proof
              assume "v = ''PrFlowPort2''"
              then show "nonPRefsOf (toFr F_CD) v \<noteq> {}"
                by (simp add: nonPRefsOf_def refsOf_def refs_F_CD NsP_def NsTy_def)
                (simp add: F_CD_def SG_F_CD_def toFr_def toSGr_def)
            next
              assume "v = ''PrBlock3''"
              then show "nonPRefsOf (toFr F_CD) v \<noteq> {}"
                by (simp add: nonPRefsOf_def refsOf_def refs_F_CD NsP_def NsTy_def)
                (simp add: F_CD_def SG_F_CD_def toFr_def toSGr_def)
            qed
          qed
        qed
      qed
    next
      apply_end(rule conjI)
      show "acyclic_fr (toFr F_CD)"
        proof -
          from wf_SG_F_CD have "acyclic (inh (sg (toFr F_CD)))"
            by (simp add: is_wf_sg_def acyclicGr_def inh_def F_CD_def toFr_def)
          then show "acyclic_fr (toFr F_CD)"
          proof (simp add: acyclic_fr_def)
            assume h1: "acyclic (inh (sg (toFr F_CD)))"
            have h2: "is_wf_g (toSGr (sg_ls (F_CD)))"
              using wf_SG_F_CD by (simp add: F_CD_def is_wf_sg_def)
            have h3: "Domain (inh (sg (toFr F_CD))) \<inter> Domain (refs (toFr F_CD)) = {}"
              using h2 
                by (simp add: refs_F_CD)(simp add: toFr_def inh_eq_consInh, eval)
            have h4: "Range (refs (toFr F_CD)) \<inter> Domain (inh (sg (toFr F_CD))) = {}"
              using h2 by (simp add: refs_F_CD)(simp add: toFr_def inh_eq_consInh, eval)
            have h5: "acyclic(refs (toFr F_CD))"
              by (simp add: refs_F_CD)(auto simp add: rtrancl_in acyclic_def)
            from h1 h3 h4 h5 show "acyclic (inh (sg (toFr F_CD)) \<union> refs (toFr F_CD))"
              by (simp add: acyclic_Un)
          qed
        qed
      next
      show "proxies_dont_inherit (toFr F_CD)"
        by (simp add: proxies_dont_inherit_def  EsI_def NsP_def NsTy_def EsTy_def vimage_def
          F_CD_def SG_F_CD_def toFr_def toSGr_def)
    qed
  qed

(*Type Fragment corresponding to 'F_CD' *)
definition TF_CD :: "TFr_ls"
where
   "TF_CD = \<lparr>fr_ls = F_CD, iet_ls = []\<rparr>"

(* Well-formedness proof obligation of 'TF_ASD'*)
lemma wf_TF_CD: "is_wf_tfr (toTFr TF_CD)"
  proof (simp add: is_wf_tfr_def, rule conjI)
    show "is_wf_fr (fr (toTFr TF_CD))"
      by (simp add: TF_CD_def wf_F_CD toTFr_def)
  next
    apply_end (rule conjI)
    show "dom (iet (toTFr TF_CD)) \<subseteq> EsA (sg (fr (toTFr TF_CD)))"
      by (simp add: TF_CD_def toTFr_def)
  next
    show "ftotal_on (iety (toTFr TF_CD)) (EsA (sg (fr (toTFr TF_CD)))) SGETy_set"
    proof (simp add: ftotal_on_def, rule conjI)
      show "dom (iety (toTFr TF_CD)) = EsA (sg (fr (toTFr TF_CD)))"
      proof
        show "dom (iety (toTFr TF_CD)) \<subseteq> EsA (sg (fr (toTFr TF_CD)))"
          by (simp add: TF_CD_def EsA_def EsTy_def vimage_def F_VTypes_def
            SG_F_Comps_def toFr_def toSGr_def iety_def toTFr_def)
      next
        show "EsA (sg (fr (toTFr TF_CD))) \<subseteq> dom (iety (toTFr TF_CD))"
          by (auto simp add: TF_Comps_def EsA_def EsTy_def vimage_def  
            toFr_def toSGr_def iety_def)
      qed
    next
      show "ran (iety (toTFr TF_CD)) \<subseteq> SGETy_set"
      proof
        fix x
        assume "x \<in> ran (iety (toTFr TF_CD))"
        then have "x = ecompuni \<or> x = ereluni \<or> x = erelbi"
        by (simp add: ran_def, clarify)
          (auto simp add: iety_def restrict_map_def TF_CD_def toTFr_def fun_app_def EsA_def
            EsTy_def ran_def F_CD_def SG_F_CD_def toFr_def toSGr_def split: if_splits)
        then show "x \<in> SGETy_set"
          by (simp add:  SGETy_set_def)(erule disjE, auto)
      qed
    qed
  qed

end