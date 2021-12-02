(*  Title:      Structural graphs (SGs)
    Description: 'Fragmenta' theory of SGs
    Author:     Nuno Amálio
*)
theory Fragmenta_SGs
  imports Fragmenta_Graphs Fragmenta_SGElemTys 
    Fragmenta_Mult  "../Extra/Trcl_Extra" 
    "../Extra/Map_Extra"

begin

(*Type of SGs*)
record SGr = Gr +
   nty :: "V \<rightharpoonup> SGNT"
   ety :: "E \<rightharpoonup> SGET" 
   srcm  :: "E \<rightharpoonup> MultC"
   tgtm  :: "E \<rightharpoonup> MultC"
   db :: "E \<rightharpoonup> E"

(* Defines the empty SG*)
definition emptySG :: "SGr"
where
  "emptySG \<equiv> \<lparr>Ns = {}, Es = {}, src = Map.empty, tgt = Map.empty, 
    nty = Map.empty, ety = Map.empty,
    srcm = Map.empty, tgtm = Map.empty, db = Map.empty\<rparr>"

lemma SGr_eq: 
  shows "(SG1 = SG2) \<longleftrightarrow> Ns SG1 = Ns SG2 \<and> Es SG1 = Es SG2 \<and> src SG1 = src SG2 
    \<and> tgt SG1 = tgt SG2 \<and> nty SG1 = nty SG2 \<and> ety SG1 = ety SG2 
    \<and> srcm SG1 = srcm SG2 \<and> tgtm SG1 = tgtm SG2 \<and> db SG1 = db SG2 
    \<and> SGr.more SG1 = SGr.more SG2"
    by (auto)

definition gr_sg :: "SGr \<Rightarrow> Gr"
where
  "gr_sg SG = \<lparr>Ns = Ns SG, Es = Es SG, src = src SG, tgt = tgt SG\<rparr>"

(*Nodes of some type*)
definition NsTy ::"SGr \<Rightarrow> SGNT set \<Rightarrow> E set"
where
  "NsTy SG nts = (nty SG)-` (Some ` nts)"

(*Edges of some type*)
definition EsTy ::"SGr \<Rightarrow> SGET set \<Rightarrow> E set"
where
  "EsTy SG ets = (ety SG)-` (Some ` ets)"

lemma EsTy_emptySG[simp]:
  "EsTy emptySG ets = {}"
  by (simp add: EsTy_def emptySG_def)

(*Association edges*)
definition EsA ::"SGr \<Rightarrow> E set"
where
  "EsA SG \<equiv> EsTy SG (ecomps \<union> erels)"

lemma EsA_emptySG[simp]:
  "EsA emptySG = {}"
  by (simp add: EsA_def)

(*Wander edges*)
definition EsW ::"SGr \<Rightarrow> E set"
where
  "EsW SG \<equiv> EsTy SG {ewander}"

lemma EsW_emptySG[simp]:
  "EsW emptySG = {}"
  by (simp add: EsW_def)

(*Inheritance edges*)
definition EsI ::"SGr \<Rightarrow> E set"
where
  "EsI SG \<equiv> EsTy SG {einh}"

(*Derived edges*)
definition EsD ::"SGr \<Rightarrow> E set"
where
  "EsD SG \<equiv> EsTy SG {eder}"

lemma EsD_emptySG[simp]:
  "EsD emptySG = {}"
  by (simp add: EsD_def)

(*Reference edges*)
definition EsC ::"SGr \<Rightarrow> E set"
where
  "EsC SG \<equiv> EsA SG \<union> EsW SG \<union> EsD SG"

lemma EsC_emptySG[simp]:
  "EsC emptySG = {}"
  by (simp add: EsC_def)

(*Proxy nodes*)
definition NsP ::"SGr \<Rightarrow> V set"
where
  "NsP SG \<equiv> NsTy SG {nprxy}"

(*Ethereal nodes*)
definition NsEther ::"SGr \<Rightarrow> V set"
where
  "NsEther SG \<equiv> NsTy SG {nabst, nvirt, nenum}"

(*Optional nodes*)
definition NsO ::"SGr \<Rightarrow> V set"
where
  "NsO SG \<equiv> NsTy SG {nopt}"

(*Virtual nodes*)
definition NsV ::"SGr \<Rightarrow> V set"
where
  "NsV SG \<equiv> NsTy SG {nvirt}"

(*Reference edges attached to proxies*)
(*definition EsRP ::"SGr \<Rightarrow> E set"
where
  "EsRP SG \<equiv> {e. e \<in> EsR SG \<and> (\<exists> v. (src SG e) = Some v \<and> v \<in> (NsP SG))}"
*)

definition inhG ::"SGr \<Rightarrow> Gr"
where
  "inhG SG \<equiv> restrict SG (EsI SG)"

lemma Ns_inhG[simp]: "Ns (inhG SG) = rst_Ns SG (EsI SG)"
  by (simp add: inhG_def)

lemma Es_inhG[simp]: "Es (inhG SG) = Es SG \<inter> (EsI SG)"
  by (simp add: inhG_def)

lemma src_inhG[simp]: "src (inhG SG) = rst_fun (EsI SG) (src SG)"
  by (simp add: inhG_def)

lemma tgt_inhG[simp]: "tgt (inhG SG) = rst_fun (EsI SG) (tgt SG)"
  by (simp add: inhG_def)

definition inh ::"SGr \<Rightarrow> V rel"
where
  "inh SG \<equiv> (inhG SG)\<^sup>\<Leftrightarrow>"

lemma inh_noedgesI: "EsI SG = {} \<Longrightarrow> inh SG = {}"
  by (simp add: EsI_def inh_def relG_def adjacent_def restrict_def inhG_def)

lemma acyclic_sg_noEI:"EsI SG = {} \<Longrightarrow> acyclicGr (inhG SG)"
  by (simp add: acyclicGr_def inh_noedgesI wf_acyclic inh_def 
      inhG_def emptyG_def relG_def adjacent_def)

definition srcma_ecomp_uni:: "SGr \<Rightarrow> E \<rightharpoonup> MultC"
  where
  "srcma_ecomp_uni SG \<equiv> (\<lambda> x. if x \<in> EsTy SG {ecomp duni} then Some (sm (val 1)) else None)"

definition srcma_erel_uni:: "SGr \<Rightarrow> E \<rightharpoonup> MultC"
  where
  "srcma_erel_uni SG \<equiv> (\<lambda> x. if x \<in> EsTy SG {erel duni} then Some (sm many) else None)"

definition srcma ::"SGr \<Rightarrow> E \<rightharpoonup> MultC"
where
  "srcma SG \<equiv> (srcm SG) ++ srcma_ecomp_uni SG ++ srcma_erel_uni SG"

definition multsOk::"SGr \<Rightarrow>bool"
  where
  "multsOk SG \<equiv> \<forall> e \<in> EsC SG. the (ety SG e) \<propto> (the (srcma SG e), the (tgtm SG e))"

definition inhst ::"SGr \<Rightarrow> (V\<times>V) set"
where
  "inhst SG \<equiv> (inh SG)\<^sup>*"

lemma inhst_noinh: "inh SG = {} \<Longrightarrow> inhst SG = Id"
  by (simp add: inhst_def)

definition srcr::"SGr \<Rightarrow> (E\<times>V) set"
  where
  "srcr SG \<equiv> pfunToRel (src SG) \<union> (EsW SG) \<lhd> pfunToRel(tgt SG)"

definition srcst ::"SGr \<Rightarrow> (E\<times>V) set"
where
  "srcst SG \<equiv> (EsC (SG) \<lhd> srcr SG) O (inhst SG)\<inverse>"

lemma srcst_emptySG[simp]:
  "srcst emptySG = {}"
  by (simp add: srcst_def)

definition tgtr::"SGr \<Rightarrow> (E\<times>V) set"
  where
  "tgtr SG \<equiv> pfunToRel (tgt SG) \<union> (EsW SG) \<lhd> pfunToRel(src SG)"

definition tgtst ::"SGr \<Rightarrow> (E\<times>V) set"
where
  "tgtst SG \<equiv> (EsC (SG) \<lhd> tgtr SG) O (inhst SG)\<inverse>"

lemma tgtst_emptySG[simp]:
  "tgtst emptySG = {}"
  by (simp add: tgtst_def)

definition esIncidentst::"SGr \<Rightarrow>V set \<Rightarrow> E set" (infixl "\<circ>\<rightarrow>\<circ>\<^sup>*" 100)
  where
    "SG \<circ>\<rightarrow>\<circ>\<^sup>* vs = ((srcst SG)\<inverse> `` vs) \<union> ((tgtst SG)\<inverse> `` vs)"

lemma esIncidentst_emptySG:
  "emptySG \<circ>\<rightarrow>\<circ>\<^sup>* vs = {}"
  by (simp add: esIncidentst_def )

lemma esIncidentst_empty_vs:
  "SG \<circ>\<rightarrow>\<circ>\<^sup>* {} = {}"
  by (simp add: esIncidentst_def )

definition optsVoluntary::"SGr \<Rightarrow>bool"
  where
  "optsVoluntary SG \<equiv> pfunToRel (ety SG) ``((SG \<circ>\<rightarrow>\<circ>\<^sup>* (NsO SG)) - (EsI SG)) \<subseteq> {ewander}"

definition inhOk::"SGr \<Rightarrow>bool"
  where
  "inhOk SG \<equiv> (\<forall> v v'. (v, v') \<in> inh SG \<longrightarrow> the (nty SG v) <\<^sub>N\<^sub>T the (nty SG v'))
    \<and> acyclicGr (inhG SG) \<and> tree (((inhG SG) \<ominus>\<^sub>N\<^sub>S (NsV SG))\<^sup>\<Leftrightarrow>)"

definition wf_sg :: "SGr \<Rightarrow> bool"
where
  "wf_sg SG \<equiv> wf_g SG 
      \<and> ftotal_on (nty SG) (Ns SG) SGNT_set 
      \<and> ftotal_on (ety SG) (Es SG) SGET_set 
      \<and> ftotal_on (srcma SG) (EsC SG) MultC_set
      \<and> ftotal_on (tgtm SG) (EsC SG) MultC_set
      \<and> dom (db SG) = EsD SG
      \<and> multsOk SG"

lemma wf_sg_wf_g:
  assumes "wf_sg SG"
  shows "wf_g SG"
  using assms by (simp add: wf_sg_def)

lemma wf_sg_ftotal_on_srcG:
  assumes "wf_sg SG"
  shows "ftotal_on (src SG) (Es SG) (Ns SG)"
  using assms by (simp add: wf_sg_def wf_g_def)

lemma wf_sg_ftotal_on_tgtG:
  assumes "wf_sg SG"
  shows "ftotal_on (tgt SG) (Es SG) (Ns SG)"
  using assms by (simp add: wf_sg_def wf_g_def)

lemma wf_sg_ftotal_on_nty:
  assumes "wf_sg SG"
  shows "ftotal_on (nty SG) (Ns SG) SGNT_set"
  using assms by (simp add: wf_sg_def)

lemma wf_sg_ftotal_on_ety:
  assumes "wf_sg SG"
  shows "ftotal_on (ety SG) (Es SG) SGET_set"
  using assms by (simp add: wf_sg_def)

lemma wf_sg_ftotal_on_srcma:
  assumes "wf_sg SG"
  shows "ftotal_on (srcma SG) (EsC SG) MultC_set"
  using assms by (simp add: wf_sg_def)

lemma srcm_sub_srcma:
  shows "dom (srcm SG) \<subseteq> dom (srcma SG)"
  by (simp add: subsetI srcma_def)

lemma wf_sg_ftotal_on_tgtm:
  assumes "wf_sg SG"
  shows "ftotal_on (tgtm SG) (EsC SG) MultC_set"
  using assms by (simp add: wf_sg_def)

lemma wf_sg_dom_db:
  assumes "wf_sg SG"
  shows "dom (db SG) = EsD SG"
  using assms by (simp add: wf_sg_def)

lemma NsP_sub_Ns: 
  assumes "wf_sg SG"
  shows "NsP SG \<subseteq> Ns SG"
  using assms wf_sg_ftotal_on_nty [of SG]
  by (auto simp add: NsP_def NsTy_def ftotal_on_def)

lemma wf_g_inhG:
  assumes "wf_g SG"
  shows "wf_g (inhG SG)"
  using assms by (simp add: inhG_def wf_restrict)

lemma EsTy_sub_Es: 
  assumes "wf_sg SG"
  shows "EsTy SG ets \<subseteq> Es SG"
  using assms wf_sg_ftotal_on_ety[of SG]
  by (auto simp add: EsTy_def ftotal_on_def)
  
lemma EsI_sub_Es: 
  assumes "wf_sg SG"
  shows "EsI SG \<subseteq> Es SG"
using assms wf_sg_ftotal_on_ety[of SG]
  by (auto simp add: EsI_def EsTy_sub_Es)

lemma EsC_sub_ES: 
  assumes "wf_sg SG"
  shows "EsC SG \<subseteq> Es SG"
  using assms wf_sg_ftotal_on_ety[of SG]
  by (auto simp add: EsC_def EsTy_def ftotal_on_def 
      EsA_def EsW_def EsD_def)

lemma EsD_sub_ES: 
  assumes "wf_sg SG"
  shows "EsD SG \<subseteq> Es SG"
  using assms wf_sg_ftotal_on_ety[of SG]
  by (auto simp add: EsD_def EsTy_def ftotal_on_def)

lemma EsA_sub_ES: 
  assumes "wf_sg SG"
  shows "EsA SG \<subseteq> Es SG"
  using assms wf_sg_ftotal_on_ety[of SG]
  by (auto simp add: EsA_def EsTy_def ftotal_on_def)

lemma Domain_inh:
  assumes "wf_sg SG"
  shows "Domain (inh SG) \<subseteq> Ns SG"
  using assms wf_sg_ftotal_on_srcG[of SG]
  by (auto simp add: inh_def relG_def adjacent_def ftotal_on_def 
      rst_fun_def EsI_def EsTy_def
      restrict_map_def inhG_def intro!: ranI)

lemma Range_inh:
  assumes h1: "wf_sg SG"
  shows "Range (inh SG) \<subseteq> Ns SG"
  using assms wf_sg_ftotal_on_tgtG[of SG]
  by (auto simp add: inh_def relG_def adjacent_def ftotal_on_def 
      rst_fun_def EsI_def EsTy_def
      restrict_map_def inhG_def intro!: ranI)

lemma inh_sub_inhst: "inh SG \<subseteq>  inhst SG"
  by (auto simp add: inhst_def)

lemma src_restrict_EsA_sub_srcst:
  shows "pfunToRel(src SG |` (EsA SG)) \<subseteq> srcst SG"
  by (auto simp add: srcst_def restrict_map_def 
          pfunToRel_def inhst_def dres_def EsC_def 
          srcr_def
          split: if_splits)

lemma tgt_restrict_EsA_sub_tgtst: 
  shows "pfunToRel(tgt SG |` (EsA SG)) \<subseteq> tgtst SG"
  by (auto simp add: tgtst_def restrict_map_def 
          pfunToRel_def inhst_def dres_def EsC_def 
          tgtr_def
          split: if_splits)


(*
lemma in_Es_removeNsNotAdjP_inhG:
  assumes h1: "is_wf_sg SG" and h2: "e \<in> Es (removeNs (inhG SG) (NsNotAdjP SG))" 
  shows "\<exists> p. p \<in> NsP SG \<and> (src SG e = Some p \<or> tgt SG e = Some p)"
  proof -
    from h1 have h1a: "is_wf_g SG"
      by (simp add: is_wf_sg_def)
    from h1a have h1b: "dom (src SG) = Es SG" 
      by (simp add: is_wf_g_def ftotal_on_def)
    from h1a have h1c: "dom (tgt SG) = Es SG" 
      by (simp add: is_wf_g_def ftotal_on_def)
    from h1a have h1d: "ran (src SG) \<subseteq> Ns SG" 
      by (simp add: is_wf_g_def ftotal_on_def)
    from h1a have h1e: "ran (tgt SG) \<subseteq> Ns SG" 
      by (simp add: is_wf_g_def ftotal_on_def)
    from h1 have h1f: "is_wf_g (inhG SG)"
      by (simp add: is_wf_g_inhG)
    from h1f have h1g: "is_wf_g (removeNs (inhG SG) (NsNotAdjP SG))"
      using is_wf_remove[where G="inhG SG" and ns="NsNotAdjP SG"]
      by (simp)
    from h2 h1g have h2a: "e \<in> dom (src (removeNs (inhG SG) (NsNotAdjP SG)))"
      by (simp add: is_wf_g_def ftotal_on_def)
    from h2 h1g have h2b: "e \<in> dom (tgt (removeNs (inhG SG) (NsNotAdjP SG)))"
      by (simp add: is_wf_g_def ftotal_on_def)
    from h1b h1c h2 show ?thesis
    proof (simp add: rst_fun_def restrict_map_def split: if_splits)
      apply_end(erule conjE, erule conjE, erule conjE, erule conjE)
      assume h3a: "e \<in> Es SG"
      from h3a h1b have h3b: "e \<in> dom (src SG)" by simp
      from h3a h1c have h3c: "e \<in> dom (tgt SG)" by simp
      assume h3d: "e \<in> EsI SG"
      assume h3e: "e \<notin> EsId SG" 
      assume h3f: "src SG e \<notin> Some ` NsNotAdjP SG"
      hence h3g: "src SG e \<notin> Some ` NsNotAdjP SG \<longrightarrow> src SG e \<in> Some ` NsAdjP SG"
        using h3b h1d
        by (simp add: image_def dom_def NsNotAdjP_def)(erule exE, auto intro: ranI)
      assume h3h: "tgt SG e \<notin> Some ` NsNotAdjP SG"
      hence h3i: "tgt SG e \<in> Some ` NsAdjP SG"
        using h3c h1e
        by (simp add: image_def dom_def NsNotAdjP_def)(erule exE, auto intro: ranI)
      have h2c: "\<exists>v1 v2. src (removeNs (inhG SG) (NsNotAdjP SG)) e = Some v1
        \<and> tgt (removeNs (inhG SG) (NsNotAdjP SG)) e = Some v2 \<and> (v1 \<in> NsP SG \<or> v2 \<in> NsP SG)"
      proof (simp)
      qed
        by (auto simp add: rst_fun_def rmv_EsOfNs_def restrict_map_def image_def NsNotAdjP_def 
          NsAdjP_def dom_def split: if_splits intro!: ranI)
      from h2a h2b h3a h3d h1d h1e 
        by (simp add: image_def dom_def NsNotAdjP_def)(erule exE, auto intro: ranI)
      have h3j: "\<exists> v1 v2 . src SG e \<in> Some ` NsP SG \<or> tgt SG e \<in> Some ` NsP SG"
        using h3b h3c  
        proof (simp add: image_def dom_def NsAdjP_def)
          apply_end(erule exE, erule exE)
          fix v1 v2
          assume ha: "src SG e = Some v1"
          assume hb: "tgt SG e = Some v2"
          show "(\<exists>x\<in>NsP SG. src SG e = Some x) \<or> (\<exists>x\<in>NsP SG. tgt SG e = Some x)"
          proof (case_tac "v1 \<in> NsP SG")
            assume hc: "v1 \<in> NsP SG"
            from ha hc show "(\<exists>x\<in>NsP SG. src SG e = Some x) \<or> (\<exists>x\<in>NsP SG. tgt SG e = Some x)"
              by auto
          next
            assume hc: "v1 \<notin> NsP SG"
            show "(\<exists>x\<in>NsP SG. src SG e = Some x) \<or> (\<exists>x\<in>NsP SG. tgt SG e = Some x)"
            proof (case_tac "v2 \<in> NsP SG")
              assume hd: "v2 \<in> NsP SG"
              from hb hd show "(\<exists>x\<in>NsP SG. src SG e = Some x) \<or> (\<exists>x\<in>NsP SG. tgt SG e = Some x)"
                by auto
            next
              assume hd: "v2 \<notin> NsP SG"
              from hc hd ha hb h3g h3i show "(\<exists>x\<in>NsP SG. src SG e = Some x) \<or> (\<exists>x\<in>NsP SG. tgt SG e = Some x)"
                by (auto simp add: NsAdjP_def adjacent_def)
            qed
          qed
        qed
      assume h3h: "tgt SG e \<notin> Some ` NsNotAdjP SG"
      hence h3i: "\<exists> v. tgt SG e = Some v \<and> v \<in> NsAdjP SG"
         using h3c h1d by (simp add: image_def dom_def NsNotAdjP_def)
          (erule exE, auto intro: ranI)
      show "\<exists>p. p \<in> NsP SG \<and> (src SG e = Some p \<or> tgt SG e = Some p)"
      proof (rule ccontr)
        apply_end(simp)
        assume h4: "\<forall>p. p \<in> NsP SG \<longrightarrow> src SG e \<noteq> Some p \<and> tgt SG e \<noteq> Some p"
        from h3g show "False"
        proof
          apply_end(erule conjE)
          fix v1
          assume h5a: "src SG e = Some v1"
          assume h5b: "v1 \<in> NsAdjP SG"
          from h5a h5b h1c have h4c: "v1 \<in> NsP SG 
            \<or> (\<exists>p. p \<in> NsP SG \<and> (adjacent v1 p SG \<or> adjacent p v1 SG))"
            by (auto simp add: NsNotAdjP_def NsAdjP_def intro: ranI)
          show "False"
          proof (case_tac "v1 \<in> NsP SG")
            assume h6a: "v1 \<in> NsP SG"
            from h4 h6a have h6b: "src SG e \<noteq> Some v1 \<and> tgt SG e \<noteq> Some v1"
              by auto
            from h6b h5a show "False" by auto
          next
            assume h6: "v1 \<notin> NsP SG"
            from h3i show "False"
            proof
              apply_end(erule conjE)
              fix v2
              assume h7a: "tgt SG e = Some v2"
              assume h7b: "v2 \<notin> NsNotAdjP SG"
              from h7a h7b h1d have h7c: "v2 \<in> NsP SG 
                \<or> (\<exists>p. p \<in> NsP SG \<and> (adjacent v2 p SG \<or> adjacent p v2 SG))"
                by (auto simp add: NsNotAdjP_def NsAdjP_def intro: ranI)
                show "False"
                proof (case_tac "v2 \<in> NsP SG")
                  assume h8a: "v2 \<in> NsP SG"
                  from h4 h8a have h8b: "src SG e \<noteq> Some v2 \<and> tgt SG e \<noteq> Some v2"
                  by auto
                  from h8b h7a show "False" by auto
                next
                  assume h8a: "v2 \<notin> NsP SG"
                  from h6 h4c have h8b: "(\<exists>p. p \<in> NsP SG 
                    \<and> (adjacent v1 p SG \<or> adjacent p v1 SG))" by auto
                  from h8b show "False"
                  proof
                    apply_end(erule conjE)
                    fix p
                    assume h9a: "p \<in> NsP SG"
                    from h1 h9a have h9b: "p \<in> Ns SG" 
                      by (auto simp add: in_NsP_Ns)
                    assume h9c: "adjacent v1 p SG \<or> adjacent p v1 SG"
                    from h9a h4 have h9d: "src SG e \<noteq> Some p \<and> tgt SG e \<noteq> Some p"
                      by auto
                    from h1 h9b have h9e: "p \<in> NsAdjP SG \<or> p \<in> NsNotAdjP SG" 
                      by (simp add: in_NsAdjP_or_not)
                    from h9c h9d h9e show "False" 
                      by (auto simp add: NsAdjP_def NsNotAdjP_def adjacent_def)
        from h3i show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
        proof
          apply_end(erule conjE)
          fix v2
          assume h5a: "tgt SG e = Some v2"
          assume h5b: "v2 \<notin> NsNotAdjP SG"
          from h5a h5b h1d have h5c: "v2 \<in> NsP SG 
              \<or> (\<exists>p. p \<in> NsP SG \<and> (adjacent v2 p SG \<or> adjacent p v2 SG))"
            by (auto simp add: NsNotAdjP_def NsAdjP_def intro: ranI)
          from h4c show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
          proof 
            assume h6a: "v1 \<in> NsP SG"
            then show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
              using h4a by (rule_tac exI[where x="v1"])(auto)
          next
            apply_end(erule exE)
            fix p
            assume h6a: "p \<in> NsP SG \<and> (adjacent v1 p SG \<or> adjacent p v1 SG)"
            then show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
            proof (case_tac "p=v1")
              assume "p=v1"
              then show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
              using h4a h6a by (rule_tac exI[where x="p"])(auto simp add: adjacent_def)
            next
              assume h7a: "p\<noteq>v1"
              from h5c show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
              proof
                assume h8a: "v2 \<in> NsP SG"
                then show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
                using h5a by (rule_tac exI[where x="v2"])(auto)
              next
                apply_end(erule exE)
                fix p2
                assume h8a: "p2 \<in> NsP SG \<and> (adjacent v2 p2 SG \<or> adjacent p2 v2 SG)"
                from h6a h8a show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
                proof (case_tac "p=v2")
                  assume h8b: "p=v2"
                  from h6a h5a h8b show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
                    by (rule_tac exI[where x="p"])(auto simp add: adjacent_def)
                next
                  assume h8b: "p \<noteq> v2"
                  show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
                  proof (case_tac "p2=v1") 
                    assume "p2=v1"
                    then show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
                      using h8a h4a by (rule_tac exI[where x="p2"])(auto simp add: adjacent_def)
                  next
                    assume h8b: "p2\<noteq>v1"
                    show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
                    proof (case_tac "p2=v2")
                      assume h8c: "p2=v2"
                      from h6a h5a h8c show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
                        by (rule_tac exI[where x="p2"])(auto simp add: adjacent_def)
                    next
                      assume h8c: "p2\<noteq>v2" (*I AM HERE*)
                      from h6a show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
                      using h4a h6a by (rule_tac exI[where x="p"])(auto simp add: adjacent_def)
                      by (rule_tac exI[where x="p2"])(auto simp add: adjacent_def)
          
  qed*)
  

(*lemma inhG_partitions_disjEsGs:
  shows "disjEsGs (restrict (inhG SG) (Es (inhG SG) - EsP SG)) (restrict (inhG SG) (EsP SG))"
    by (auto simp add: disjEsGs_def)*)

(*

lemma SG_EsA_no_inh: 
  assumes h1: "Es SG = EsA SG" and h2: "is_wf_sg SG"
  shows "EsI SG = {}"
  proof 
    show "EsI SG \<subseteq> {}"
    proof
      fix y
      assume a1: "y \<in> EsI SG"
      show "y \<in> {}"
      proof (rule ccontr, simp)
        have a2: "ftotal_on (ety SG) (Es SG) SGETy_set" 
          using h2 by (simp add: is_wf_sg_def)
        have a3: "dom (ety SG) = (Es SG)" using a2 by (simp add: ftotal_on_dom)
        have a4: "y \<in> dom (ety SG)" using a1 a3 by (auto simp: EsI_def EsA_def EsTy_def)
        then show "False" 
        using a1 a2 a3 h1 by (auto simp: ftotal_on_def EsA_def EsI_def EsTy_def vimage_def)
     qed
  qed
  next
  show "{} \<subseteq> EsI SG" by (auto)
  qed

lemma EsR_sub_Es: 
  assumes h1: "is_wf_sg SG"
  shows "EsR SG \<subseteq> Es SG"
  proof -
    from h1 have h1a: "ftotal_on (ety SG) (Es SG) SGETy_set"
      by (simp add: is_wf_sg_def)
    from h1a show ?thesis
      by (auto simp add: EsR_def EsTy_def ftotal_on_def)
  qed

lemma in_EsR_in_Es:
  assumes h1: "is_wf_sg SG" and h2: "x \<in> EsR SG"
  shows "x \<in> (Es SG)"
  proof -
    from assms show ?thesis
    using EsR_sub_Es[where SG="SG"]
    by (auto) 
  qed

lemma EsRP_sub_Es: 
  assumes h1: "is_wf_sg SG"
  shows "EsRP SG \<subseteq> Es SG"
  proof -
    from h1 have h1a: "ftotal_on (ety SG) (Es SG) SGETy_set"
      by (simp add: is_wf_sg_def)
    from h1a show ?thesis
      by (auto simp add: EsRP_def EsR_def EsTy_def ftotal_on_def)
  qed

lemma in_EsRP_in_Es:
  assumes h1: "is_wf_sg SG" and h2: "e \<in> EsRP SG"
  shows "e \<in> Es SG"
  proof -
    from assms show ?thesis
    using EsRP_sub_Es[where SG="SG"]
    by (auto) 
  qed

lemma in_EsRP_src_proxy:
  assumes h1: "e \<in> EsRP SG"
  shows "\<exists> v. (src SG) e = Some v \<and> v \<in> (NsP SG)"
  using assms by (auto simp add: EsRP_def)

(*lemma SG_in_EsA:
  assumes "(ety SG) e = Some erelbi"
  shows "e \<in> EsA SG"
proof -
  from assms show ?thesis by (simp add: EsA_def EsTy_def)
qed*)


lemma inhst_inh_subsetid: "r \<subseteq> Id \<Longrightarrow> inhst SG = (inh SG-r)^*"
  unfolding inhst_def
  apply (insert "rtrancl_minus_subsetid"[where s = "r" and r ="inh SG"])
  apply (rule sym)
  by (simp)

*)


(*
lemma in_srcst_subeq_src:
  assumes ha: "Es SG = EsA SG" and hb: "is_wf_sg SG"
  shows "srcst SG \<subseteq> pfunToRel (src SG)"
proof (rule subrelI)
  fix x y 
  assume "(x, y) \<in> srcst SG"
  hence h2: "(src SG) x = Some y"
    using ha hb 
    by (simp add: srcst_def inhst_is_id)(simp add: EsA_def EsTy_def dres_def pfunToRel_def)
  thus "(x, y) \<in> pfunToRel (src SG)" by (auto simp: pfunToRel_def)
qed*)

(*
lemma srcst_eq_src_EsA:
  assumes ha: "Es SG = EsA SG" and hb: "is_wf_sg SG"
  shows "srcst SG = pfunToRel (src SG)"
  proof
    show "srcst SG \<subseteq> pfunToRel (src SG)"
      using ha hb by (simp add: in_srcst_subeq_src)
  next
    show "pfunToRel (src SG) \<subseteq> srcst SG"
    proof (rule subrelI)
      fix x y 
      assume b1: "(x, y) \<in> pfunToRel (src SG)"
      hence b2: "(src SG) x = Some y"
        by (auto simp: pfunToRel_def)
      have b3: "ftotal_on (src SG) (Es SG) (Ns SG)" 
        using hb by (simp add: is_wf_sg_def is_wf_g_def)
      have b4: "x \<in> Es SG" using b2 b3 by (auto simp add: ftotal_on_def dom_def)
      have b5: "x : EsA SG" using b4 ha by (auto)
      have b6: "EsI SG = {}" using ha hb by (rule SG_EsA_no_inh)
      thus "(x, y) \<in> srcst SG"
        by (simp add: b1 b5 dres_def ha hb inhst_is_id srcst_def)

   qed
qed



lemma the_src_in_srcst: 
  assumes "is_wf_sg SG" and "e \<in> EsA SG"
  shows "(e, the (src SG e)) \<in> srcst SG"
  proof -
    from assms have h1: "is_wf_g SG" by (simp add: is_wf_sg_def)
    show ?thesis
      by (simp add: assms(1) assms(2) e_v_src_in_srcst src_aedge_sg)
  qed

lemma srcpar_in_srcst: "e \<in> EsA SG \<Longrightarrow> src SG e = Some v1 \<Longrightarrow> v2 \<in> clan v1 SG  
  \<Longrightarrow> (e, v2) \<in> srcst SG"
  by (auto simp add: srcst_def dres_def pfunToRel_def inhst_def EsA_def clan_def)

definition tgtst ::"SGr \<Rightarrow> (E\<times>V) set"
where
  "tgtst SG \<equiv> (EsA (SG) \<lhd> pfunToRel(tgt SG)) O (inhst SG)\<inverse>"  
  (*"tgtst SG \<equiv> {(e, v). e \<in> EsA (SG) \<and> (\<exists>v2. v \<in> (clan v2 SG) \<and> (tgt SG) e = Some v2)}"*)

lemma tgt_in_tgtst: "\<lbrakk>e \<in> EsA SG; tgt SG e = Some v\<rbrakk> \<Longrightarrow> (e, v) \<in> tgtst SG"
  by (auto simp add: tgtst_def dres_def inhst_def pfunToRel_def)

lemma tgtpar_in_tgtst: "\<lbrakk>e \<in> EsA SG; tgt SG e = Some v1; v2 \<in> clan v1 SG\<rbrakk>  
  \<Longrightarrow> (e, v2) \<in> tgtst SG"
  by (auto simp add: tgtst_def dres_def inhst_def clan_def pfunToRel_def)

lemma the_tgt_in_tgtst: 
  assumes "is_wf_sg SG" and "e \<in> EsA SG"
  shows "(e, the (tgt SG e)) \<in> tgtst SG"
  proof -
    from assms have h1: "is_wf_g SG" by (simp add: is_wf_sg_def)
    show ?thesis
    by (simp add: assms(1) assms(2) tgt_aedge_sg tgt_in_tgtst)
  qed
*)

(*The following lemmas shows that the source or target of an edge is also in the extended set if the edge is of type 
association. In short: 
+ If it is in src, it is in src*
+ If it is in tgt, it is in tgt*)

 
(*lemma "\<lbrakk>is_wf_sg SG; e \<in> EsA(SG)\<rbrakk> \<Longrightarrow> \<exists> v. tgt SG e = Some v \<and> (e, v) \<in> tgtst SG"
  apply (frule tgt_aedge_sg, simp)
  apply (erule exE) 
  apply (rule_tac x="v" in exI)
  by (simp add: tgtst_def)*)

(*lemma "\<lbrakk>is_wf_sg SG; v1 \<in> Ns SG; v2 \<in> Ns SG; (v1, v2) \<in> inhst SG; e \<in> EsA(SG); src SG e = Some v2\<rbrakk> 
  \<Longrightarrow> (e, v1) \<in> srcst SG"  
    by (auto simp add: srcst_def inhst_def dres_def pfunToRel_def)  
*)

definition cupSG :: "SGr \<Rightarrow> SGr \<Rightarrow> SGr" (infixl "USG" 100)
where
  "SG1 USG SG2 \<equiv> \<lparr>Ns = Ns SG1 \<union> Ns SG2, 
    Es = Es SG1 \<union> Es SG2, 
    src = src SG1 ++ src SG2, 
    tgt = tgt SG1 ++ tgt SG2, 
    nty= nty SG1 ++ nty SG2, 
    ety= ety SG1 ++ ety SG2, 
    srcm = srcm SG1 ++ srcm SG2, 
    tgtm = tgtm SG1 ++ tgtm SG2,
    db = db SG1 ++ db SG2\<rparr>"


lemma USG_sym: 
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "SG1 USG SG2 = SG2 USG SG1"
proof (auto simp add: cupSG_def)
  show "(src SG1) ++ (src SG2) = (src SG2) ++ (src SG1)"
    using assms wf_sg_wf_g[of SG1] dom_src_G[of SG1]
      wf_sg_wf_g[of SG2] dom_src_G[of SG2]
      map_add_comm[of "src SG1" "src SG2"] 
    by (simp add: disjGs_def)
next
  show "tgt SG1 ++ tgt SG2 = tgt SG2 ++ tgt SG1"
    using assms wf_sg_wf_g[of SG1] dom_tgt_G[of SG1]
      wf_sg_wf_g[of SG2] dom_tgt_G[of SG2]
      map_add_comm[of "tgt SG1" "tgt SG2"] 
    by (simp add: disjGs_def)
next
  show "nty SG1 ++ nty SG2 = nty SG2 ++ nty SG1"
    using assms wf_sg_ftotal_on_nty[of SG1]
      wf_sg_ftotal_on_nty[of SG2]
      map_add_comm[of "nty SG1" "nty SG2"] 
    by (simp add: disjGs_def ftotal_on_def)
next
  show "ety SG1 ++ ety SG2 = ety SG2 ++ ety SG1"
    using assms wf_sg_ftotal_on_ety[of SG1]
      wf_sg_ftotal_on_ety[of SG2]
      map_add_comm[of "ety SG1" "ety SG2"] 
    by (simp add: disjGs_def ftotal_on_def)
next
  have "dom (srcm SG1) \<inter> dom (srcm SG2) = {}"
  proof (rule ccontr)
    assume "dom (srcm SG1) \<inter> dom (srcm SG2) \<noteq> {}"
    hence "\<exists> x. x \<in> dom (srcm SG1) \<inter> dom (srcm SG2)" by auto
    then show "False"
    proof
      fix x
      assume "x \<in> dom (srcm SG1) \<inter> dom (srcm SG2)"
      hence h: "x \<in> Es SG1 \<and> x \<in> Es SG2" 
        using assms wf_sg_ftotal_on_srcma[of SG1] 
        wf_sg_ftotal_on_srcma[of SG2] 
         EsC_sub_ES[of SG1] EsC_sub_ES[of SG2] 
         srcm_sub_srcma[of SG1] srcm_sub_srcma[of SG2]
         disjGs_imp_disjEsGs[of SG1 SG2]
        by (auto simp add: disjEsGs_def ftotal_on_def)
      from h show "False"
      using assms(3) by (auto simp add: disjGs_def )
    qed
  qed
  then show "srcm SG1 ++ srcm SG2 = srcm SG2 ++ srcm SG1"
    using map_add_comm[of "srcm SG1" "srcm SG2"]
    by simp
next
  show "tgtm SG1 ++ tgtm SG2 = tgtm SG2 ++ tgtm SG1"  
    using assms wf_sg_ftotal_on_tgtm[of SG1]
      wf_sg_ftotal_on_tgtm[of SG2]
      map_add_comm[of "tgtm SG1" "tgtm SG2"] 
      EsC_sub_ES[of SG1] EsC_sub_ES[of SG2]
      disjGs_imp_disjEsGs[of SG1 SG2]
    by (auto simp add: disjEsGs_def ftotal_on_def)
next
  show "db SG1 ++ db SG2 = db SG2 ++ db SG1"
    using assms wf_sg_dom_db[of SG1] wf_sg_dom_db[of SG2]
      EsD_sub_ES[of SG1] EsD_sub_ES[of SG2]
      map_add_comm[of "db SG1" "db SG2"] 
      disjGs_imp_disjEsGs[of SG1 SG2]
    by (auto simp add: disjEsGs_def)(force)
qed
    
lemma src_cupSG[simp]: "src (SG1 USG SG2) = src SG1 ++ src SG2"
  by (simp add: cupSG_def)

lemma tgt_cupSG[simp]: "tgt (SG1 USG SG2) = tgt SG1 ++ tgt SG2"
  by (simp add: cupSG_def)

lemma srcm_cupSG[simp]: "srcm (SG1 USG SG2) = srcm SG1 ++ srcm SG2"
  by (simp add: cupSG_def)

lemma tgtm_cupSG[simp]: "tgtm (SG1 USG SG2) = tgtm SG1 ++ tgtm SG2"
  by (simp add: cupSG_def)

lemma db_cupSG[simp]: "db (SG1 USG SG2) = db SG1 ++ db SG2"
  by (simp add: cupSG_def)

lemma restrict_USG: 
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjEsGs SG1 SG2"
  shows "(SG1 USG SG2) \<bowtie>\<^sub>E\<^sub>S es = (SG1 \<bowtie>\<^sub>E\<^sub>S es) UG (SG2 \<bowtie>\<^sub>E\<^sub>S es)"
  proof -
    have h4: "(SG1 USG SG2)\<bowtie>\<^sub>E\<^sub>S es = (SG1 UG SG2)\<bowtie>\<^sub>E\<^sub>S es"
      using assms wf_sg_wf_g[of SG1] wf_sg_wf_g[of SG2]
      by (simp add: cupSG_def restrict_def rst_Ns_dist_UG rst_Ns_def)
    show ?thesis 
      using assms wf_sg_wf_g[of SG1] wf_sg_wf_g[of SG2]
      by (simp add: h4 restrict_dist_UG)
  qed


lemma is_wf_g_Un2:
  assumes "wf_g G1" and "wf_g G2" and "disjGs G1 G2"
  shows "wf_g (G1 USG G2)"
proof (simp add: wf_g_def cupSG_def)
  apply_end (rule conjI)
  show "Ns G1 \<subseteq> V_A" 
    using assms(1) by (simp add: wf_g_def)
next
  apply_end (rule conjI)
  show "Ns G2 \<subseteq> V_A" 
    using assms(2) by (simp add: wf_g_def)
next
  apply_end (rule conjI)
  show "Es G1 \<subseteq> E_A" 
    using assms(1) by (simp add: wf_g_def)
next
  apply_end (rule conjI)
  show "Es G2 \<subseteq> E_A" 
    using assms(2) by (simp add: wf_g_def)
next
  apply_end (rule conjI)
  show "ftotal_on (src G1 ++ src G2) (Es G1 \<union> Es G2) (Ns G1 \<union> Ns G2)"
    using assms ftotal_on_src_G[of G1] ftotal_on_src_G[of G2]
    disjGs_imp_disjEsGs[of G1 G2] 
    by (simp add: disjEsGs_def ftotal_on_map_add)
next
  show "ftotal_on (tgt G1 ++ tgt G2) (Es G1 \<union> Es G2) (Ns G1 \<union> Ns G2)"
  using assms ftotal_on_tgt_G[of G1] ftotal_on_tgt_G[of G2]
    disjGs_imp_disjEsGs[of G1 G2] 
  by (simp add: disjEsGs_def ftotal_on_map_add)
qed

lemma EsTy_USG: 
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "EsTy (SG1 USG SG2) ets = EsTy SG1 ets \<union> EsTy SG2 ets"
  using assms disjGs_imp_disjEsGs[of SG1 SG2] 
      wf_sg_ftotal_on_ety[of SG1] wf_sg_ftotal_on_ety[of SG2]
      by (simp add: EsTy_def cupSG_def map_add_dists_vimage
          disjEsGs_def ftotal_on_def)

lemma NsTy_USG: 
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "NsTy (SG1 USG SG2) ets = NsTy SG1 ets \<union> NsTy SG2 ets"
  using assms  
      wf_sg_ftotal_on_nty[of SG1] wf_sg_ftotal_on_nty[of SG2]
      by (simp add: NsTy_def cupSG_def map_add_dists_vimage
          disjGs_def ftotal_on_def)

lemma EsA_USG: 
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "EsA (SG1 USG SG2) = (EsA SG1 \<union> EsA SG2)"
  using assms by (simp add: EsA_def EsTy_USG)    

lemma EsI_USG: 
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "EsI (SG1 USG SG2) = (EsI SG1 \<union> EsI SG2)"
  using assms by (simp add: EsI_def EsTy_USG)

lemma EsD_USG: 
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "EsD (SG1 USG SG2) = (EsD SG1 \<union> EsD SG2)"
  using assms by (simp add: EsD_def EsTy_USG)

lemma EsW_USG: 
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "EsW (SG1 USG SG2) = (EsW SG1 \<union> EsW SG2)"
  using assms by (simp add: EsW_def EsTy_USG)

lemma EsC_USG: 
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "EsC (SG1 USG SG2) = (EsC SG1 \<union> EsC SG2)"
  using assms 
  by (auto simp add: EsC_def EsA_USG EsW_USG EsD_USG)

(*lemma EsR_disj_dist: 
  assumes h1: "is_wf_sg SG1" and h2: "is_wf_sg SG2" and h3: "disjGs SG1 SG2"
  shows "EsR (SG1 USG SG2) = (EsR SG1 \<union> EsR SG2)"
  using h1 h2 h3 by (simp add: EsR_def EsTy_USG) *)

lemma NsP_disj_dist: 
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "NsP (SG1 USG SG2) = NsP SG1 \<union> NsP SG2"
  using assms by (simp add: NsP_def NsTy_USG)
 
(*lemma EsRP_Un_EsR_1: "\<lbrakk>disjGs SG1 SG2; is_wf_sg SG1; is_wf_sg SG2; 
  x \<in> EsR SG1; x \<in> EsRP SG1 \<or> x \<in> EsRP SG2\<rbrakk>
  \<Longrightarrow>x \<in> EsRP SG1"
  proof -
    assume h1: "disjGs SG1 SG2"
    have h1a: "Es SG1 \<inter> Es SG2 = {}"
      using h1 by (simp add: disjGs_def disjEsGs_def)
    assume h2: "is_wf_sg SG1"
    from h2 have h2a: "ftotal_on (ety SG1) (Es SG1) SGETy_set"
      by (simp add: is_wf_sg_def)
    assume h3: "is_wf_sg SG2"
    from h3 have h3a: "ftotal_on (ety SG2) (Es SG2) SGETy_set"
      by (simp add: is_wf_sg_def)
    assume h4: "x \<in> EsR SG1"
    from h4 have h4a: "x \<in> Es SG1"
      using h2a by (auto simp add: EsR_def EsTy_def ftotal_on_def)
    from h4 have h4b: "x \<notin> Es SG2" 
      using h3a h1a h2a by (auto simp add: EsR_def EsTy_def ftotal_on_def)
    from h4 have h4c: "x \<notin> EsR SG2" 
      using h3a h1a h4b by (auto simp add: EsR_def EsTy_def ftotal_on_def)
    assume h4: "x \<in> EsRP SG1 \<or> x \<in> EsRP SG2"
    show ?thesis
    using h1a h3 h3a h4 h4c by (simp add: EsRP_def)
  qed

lemma EsRP_disj_dist: "\<lbrakk>is_wf_sg SG1; is_wf_sg SG2; disjGs SG1 SG2\<rbrakk>
  \<Longrightarrow>EsRP (SG1 USG SG2) = EsRP SG1 \<union> EsRP SG2"
proof -
    assume h1: "disjGs SG1 SG2"
    have h1a: "Es SG1 \<inter> Es SG2 = {}"
      using h1 by (simp add: disjGs_def disjEsGs_def)
    have h1b: "Ns SG1 \<inter> Ns SG2 = {}"
      using h1 by (simp add: disjGs_def)
    assume h2: "is_wf_sg SG1"
    have h2a: "ftotal_on (ety SG1) (Es SG1) SGETy_set"
      using h2 by (simp add: is_wf_sg_def)
    have h2b: "ftotal_on (src SG1) (Es SG1) (Ns SG1)"
      using h2 by (simp add: is_wf_sg_def is_wf_g_def)
    from h2b have h2c: "dom (src SG1) = Es SG1"
      by (simp add: ftotal_on_def)
    from h2b have h2d: "ran (src SG1) \<subseteq> Ns SG1"
      by (simp add: ftotal_on_def)
    have "ftotal_on (nty SG1) (Ns SG1) SGNTy_set"
      using h2 by (simp add: is_wf_sg_def)
    then have h2e: "dom (nty SG1) = Ns SG1"
      by (simp add: ftotal_on_def)
    assume h3: "is_wf_sg SG2"
    have h3a: "ftotal_on (ety SG2) (Es SG2) SGETy_set"
      using h3 by (simp add: is_wf_sg_def)
    have h3b: "ftotal_on (src SG2) (Es SG2) (Ns SG2)"
      using h3 by (simp add: is_wf_sg_def is_wf_g_def)
    from h3b have h3c: "dom (src SG2) = Es SG2"
      by (simp add: ftotal_on_def)
    from h3b have h3d: "ran (src SG2) \<subseteq> Ns SG2"
      by (simp add: ftotal_on_def)
    have h4: "dom (ety SG1) \<inter> dom (ety SG2) = {}" 
      using h1a h2a h3a by (simp add: ftotal_on_dom)
    have h5: "dom (src SG1) \<inter> dom (src SG2) = {}"
      using h1a h2c h3c by simp
    from h4 have h6: "EsR SG1 \<inter> EsR SG2 = {}" 
      by (auto simp add: EsR_def EsTy_def vimage_def)
    show "EsRP (SG1 USG SG2) = EsRP SG1 \<union> EsRP SG2"
    proof
      show "EsRP (SG1 USG SG2) \<subseteq> EsRP SG1 \<union> EsRP SG2"
        proof
          fix x 
          assume h7: "x \<in> EsRP (SG1 USG SG2)"
          then have h7a: "x \<in> EsR SG1 \<or> x \<in> EsR SG2"
            using h1 h2 h3 by (simp add: EsRP_def EsR_disj_dist)
          from h7 show "x \<in> EsRP SG1 \<union> EsRP SG2"
            proof (case_tac "x \<in> EsR SG1")
              assume h8: "x \<in> EsR SG1"
              have h8a: "\<exists> v. src SG1 x = Some v \<and> v \<in> Ns SG1"
                using h8 h2 h2c h2d domD[where m="src SG1" and a ="x"]
                  ranI[where m="src SG1" and a ="x"]
                by (simp add: in_EsR_in_Es)(erule exE, auto)
              from h8 have h8c: "x \<in> EsRP SG1" 
                using h1 h2 h3 h7 h4 h5 h8a h2c h2d h1b
                by (simp add: EsRP_def EsR_disj_dist map_add_app_disj NsP_disj_dist in_EsR_in_Es)
                  (erule exE, auto simp add: in_NsP_Ns)
              from h8c show "x \<in> EsRP SG1 \<union> EsRP SG2"
                using h8 by (simp)
            next
              assume h8: "x \<notin> EsR SG1"
              show "x \<in> EsRP SG1 \<union> EsRP SG2"
              proof (case_tac "x \<in> EsR SG2")
                assume h9: "x \<in> EsR SG2"
              have h9a: "\<exists> v. src SG2 x = Some v \<and> v \<in> Ns SG2 \<and> v \<notin> Ns SG1"
                using h9 h3 h1b h3c h3d domD[where m="src SG2" and a ="x"]
                  ranI[where m="src SG2" and a ="x"]
                  EsR_sub_Es[where SG="SG2"]
                by (simp add: in_EsR_in_Es)(erule exE, auto)
              from h9 have h9c: "x \<in> EsRP SG2" 
                using h1 h2 h3 h7 h4 h5 h8 h9a h2c h3c h3d
                by (auto simp add: EsRP_def EsR_disj_dist map_add_app_disj NsP_disj_dist 
                  in_EsR_in_Es in_NsP_Ns split: if_splits)
              from h9c show "x \<in> EsRP SG1 \<union> EsRP SG2"
                by simp
            next
              assume h9: "x \<notin> EsR SG2"
              from h8 h9 show "x \<in> EsRP SG1 \<union> EsRP SG2"
                using h7a by simp
            qed
        qed
      qed
   next
      show "EsRP SG1 \<union> EsRP SG2 \<subseteq> EsRP (SG1 USG SG2)"
        proof
          fix x
          assume h7: "x \<in> EsRP SG1 \<union> EsRP SG2"
          from h7 have h7a: "x \<in> EsRP SG1 \<or> x \<in> EsRP SG2" 
            by simp
          show "x \<in> EsRP (SG1 USG SG2)"
          proof (case_tac "x \<in> EsRP SG1")
            assume h8: "x \<in> EsRP SG1"
            from h8 show "x \<in> EsRP (SG1 USG SG2)"
              using h1 h2 h3 h5 h2c
              by (auto simp add: EsRP_def EsR_disj_dist NsP_disj_dist map_add_app_disj
                in_EsR_in_Es)
          next
            assume h8: "x \<notin> EsRP SG1"
            from h8 h7a have h8a: "x \<in> EsRP SG2"
              by simp
            from h8a show "x \<in> EsRP (SG1 USG SG2)"
              using h1 h2 h3 h5 h2c
              by (auto simp add: EsRP_def EsR_disj_dist NsP_disj_dist map_add_app_disj
                in_EsR_in_Es)
          qed
        qed
   qed
qed *)

(*lemma EsI_disj_dist: "\<lbrakk>is_wf_sg SG1; is_wf_sg SG2; disjGs SG1 SG2\<rbrakk>
  \<Longrightarrow>EsI (SG1 USG SG2) = EsI SG1 \<union> EsI SG2"
proof -
  assume h1: "disjGs SG1 SG2"
  have h1a: "Es SG1 \<inter> Es SG2 = {}"
      using h1 by (simp add: disjGs_def disjEsGs_def)
  assume h2: "is_wf_sg SG1"
  have h2a: "ftotal_on (ety SG1) (Es SG1) SGETy_set"
      using h2 by (simp add: is_wf_sg_def)
  assume h3: "is_wf_sg SG2"
  have h3a: "ftotal_on (ety SG2) (Es SG2) SGETy_set"
      using h3 by (simp add: is_wf_sg_def)
  have h4: "None \<notin>  {Some einh}"
    by simp
  have h5: "dom (ety SG1) \<inter> dom (ety SG2) = {}" 
        using h1a h2a h3a by (simp add: ftotal_on_dom)
  show "EsI (SG1 USG SG2) = EsI SG1 \<union> EsI SG2"
  using h4 h5 by (simp add: EsI_def EsTy_def cupSG_def map_add_dists_vimage)
qed*)

(*lemma EsId_disj_dist: "\<lbrakk>is_wf_sg SG1; is_wf_sg SG2; disjGs SG1 SG2\<rbrakk>
  \<Longrightarrow>EsId (SG1 USG SG2) = EsId SG1 \<union> EsId SG2"
  proof -
    assume h1: "disjGs SG1 SG2"
    have h1a: "Es SG1 \<inter> Es SG2 = {}"
      using h1 by (simp add: disjGs_def disjEsGs_def)
    assume h2: "is_wf_sg SG1"
    have h2a: "ftotal_on (src SG1) (Es SG1) (Ns SG1)"
      using h2 by (simp add: is_wf_sg_def is_wf_g_def)
    have h2b: "ftotal_on (tgt SG1) (Es SG1) (Ns SG1)"
      using h2 by (simp add: is_wf_sg_def is_wf_g_def)
    assume h3: "is_wf_sg SG2"
    have h3a: "ftotal_on (src SG2) (Es SG2) (Ns SG2)"
      using h3 by (simp add: is_wf_sg_def is_wf_g_def)
    have h3b: "ftotal_on (tgt SG2) (Es SG2) (Ns SG2)"
      using h3 by (simp add: is_wf_sg_def is_wf_g_def)
    have h4: "dom (src SG1) \<inter> dom (src SG2) = {}" 
        using h1a h2a h3a by (simp add: ftotal_on_dom)
    have h5: "dom (tgt SG1) \<inter> dom (tgt SG2) = {}" 
        using h1a h2b h3b by (simp add: ftotal_on_dom)
    show "EsId (SG1 USG SG2) = EsId SG1 \<union> EsId SG2"
    proof
      show "EsId (SG1 USG SG2) \<subseteq> EsId SG1 \<union> EsId SG2"
      proof
        fix x
        assume h6: "x \<in> EsId (SG1 USG SG2)"
        have h6b: "x \<in> Es SG1 \<union> Es SG2"
          using h6 by (simp add: cupSG_def EsId_def)
        show "x \<in> EsId SG1 \<union> EsId SG2"
        proof (case_tac "x \<in> Es SG1")
          assume h7: "x \<in> Es SG1"
          have h7a: "x \<in> dom (src SG1)"
            using h7 h4 h2a by (simp add: ftotal_on_dom)
          have h7b: "x \<in> dom (tgt SG1)"
            using h7 h4 h2b by (simp add: ftotal_on_dom)
          have h8: "(src SG1 ++ src SG2) x = (src SG1) x" 
            using h7a h4 by (simp add: map_add_disj_domf)
          have h9: "(tgt SG1 ++ tgt SG2) x = (tgt SG1) x" 
            using h7b h5 by (simp add: map_add_disj_domf)
          have h10: "x \<in> EsId (SG1)"
            using h6 h7 h4 h5 h8 h9 by (auto simp add: cupSG_def EsId_def)
          show "x \<in> EsId SG1 \<union> EsId SG2"
          using h10 by (simp)
        next
          assume h7: "x \<notin> Es SG1"
          have h7a: "x \<in> Es SG2"
            using h1a h7 h6b by (simp)
          have h7b: "x \<in> dom (src SG2)"
            using h7a h4 h3a by (simp add: ftotal_on_dom)
          have h7c: "x \<in> dom (tgt SG2)"
            using h7a h4 h3b by (simp add: ftotal_on_dom)
          have h8: "(src SG1 ++ src SG2) x = (src SG2) x" 
            using h7b h4 by (simp add: map_add_dom_app_simps)
          have h9: "(tgt SG1 ++ tgt SG2) x = (tgt SG2) x" 
            using h7c h5 by (simp add: map_add_dom_app_simps)
          have h10: "x \<in> EsId (SG2)"
            using h6 h7 h4 h5 h8 h9 by (auto simp add: cupSG_def EsId_def)
          show "x \<in> EsId SG1 \<union> EsId SG2"
          using h10 by (simp)
        qed
      qed
    next 
    show "EsId SG1 \<union> EsId SG2 \<subseteq> EsId (SG1 USG SG2)"
    proof
      fix x
      assume h6: "x \<in> EsId SG1 \<union> EsId SG2"
      have h6a: "x \<in> EsId SG1 \<or> x \<in> EsId SG2"
        using h6 by simp
      have h6b: "x \<in> Es SG1 \<or> x \<in> Es SG2"
        using h6 by (auto simp add: EsId_def)
      show "x \<in> EsId (SG1 USG SG2)"
      proof (case_tac "x \<in> Es SG1")
        assume h7: "x \<in> Es SG1"
        have h7a: "x \<in> dom (src SG1)"
          using h7 h4 h2a by (simp add: ftotal_on_dom)
        have h7b: "(src SG1 ++ src SG2) x = (src SG1) x"
          using h7a h4 by (simp add: map_add_disj_domf)
        have h7c: "x \<in> dom (tgt SG1)"
          using h7 h5 h2b by (simp add: ftotal_on_dom)
        have h7d: "(tgt SG1 ++ tgt SG2) x = (tgt SG1) x"
          using h7c h5 by (simp add: map_add_disj_domf)
        show "x \<in> EsId (SG1 USG SG2)"
        using h1a h7 h7b h7d h6 by (auto simp add: cupSG_def EsId_def)
      next
        assume h7: "x \<notin> Es SG1"
        have h8: "x \<in> Es SG2"
          using h1a h7 h6b by (simp)
        have h8a: "x \<in> dom (src SG2)"
          using h8 h4 h3a by (simp add: ftotal_on_dom)
        have h8b: "(src SG1 ++ src SG2) x = (src SG2) x"
          using h8a h4 by (simp add: map_add_dom_app_simps)
        have h8c: "x \<in> dom (tgt SG2)"
          using h8 h5 h3b by (simp add: ftotal_on_dom)
        have h8d: "(tgt SG1 ++ tgt SG2) x = (tgt SG2) x"
          using h8c h5 by (simp add: map_add_dom_app_simps)
        show "x \<in> EsId (SG1 USG SG2)"
        using h1a h8 h8b h8d h6 by (auto simp add: cupSG_def EsId_def)
      qed
    qed
  qed
qed*)

lemma restrict_cup_wf_1: 
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "SG1 \<bowtie>\<^sub>E\<^sub>S (EsI SG1 \<union> EsI SG2) = SG1 \<bowtie>\<^sub>E\<^sub>S EsI SG1"
proof -
  have "EsI SG2 \<inter> Es SG1 = {}"
    using assms(2) assms(3) EsI_sub_Es[of SG2]
    by (auto simp add: disjGs_def disjEsGs_def)
  then show ?thesis
    using assms wf_sg_wf_g[of SG1] wf_sg_wf_g[of SG2]
    by (simp add: restrict_dist_cup_es)
qed

lemma disjGs_inhG:
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "disjGs (inhG SG1) (inhG SG2)"
proof (simp add: disjGs_def)
  apply_end(rule conjI)
  show "rst_Ns SG1 (EsI SG1) \<inter> rst_Ns SG2 (EsI SG2) = {}"
    using assms wf_sg_wf_g[of SG1] wf_sg_wf_g[of SG2]
      ran_src_G[of SG1] ran_src_G[of SG2] 
      ran_tgt_G[of SG1] ran_tgt_G[of SG2] 
      ran_restrict_sub[of "src SG1" "EsI SG1"]
      ran_restrict_sub[of "src SG2" "EsI SG2"]
      ran_restrict_sub[of "tgt SG1" "EsI SG1"]
      ran_restrict_sub[of "tgt SG2" "EsI SG2"]
    unfolding rst_Ns_def disjGs_def by force
next
  apply_end(rule conjI)
  show "rst_Ns SG1 (EsI SG1) \<inter> (Es SG1 \<inter> EsI SG1) = {}"
    using assms(1) assms(3) disj_V_E wf_sg_wf_g[of SG1]
      ran_restrict_sub[of "src SG1" "EsI SG1"]
      ran_restrict_sub[of "tgt SG1" "EsI SG1"]
    by (auto simp add: rst_Ns_def wf_g_def disjGs_def 
        ftotal_on_def)
next
  apply_end(rule conjI)
  show "rst_Ns SG1 (EsI SG1) \<inter> (Es SG2 \<inter> EsI SG2) = {}"
    using assms(1) assms(3) disj_V_E wf_sg_wf_g[of SG1]
      ran_restrict_sub[of "src SG1" "EsI SG1"]
      ran_restrict_sub[of "tgt SG1" "EsI SG1"]
    by (auto simp add: rst_Ns_def wf_g_def disjGs_def 
        ftotal_on_def)
next
  apply_end(rule conjI)
  show "rst_Ns SG2 (EsI SG2) \<inter> (Es SG1 \<inter> EsI SG1) = {}"
    using assms(2) assms(3) disj_V_E wf_sg_wf_g[of SG2]
      ran_restrict_sub[of "src SG2" "EsI SG2"]
      ran_restrict_sub[of "tgt SG2" "EsI SG2"]
    by (auto simp add: rst_Ns_def wf_g_def disjGs_def 
        ftotal_on_def)
next
  apply_end(rule conjI)
  show "rst_Ns SG2 (EsI SG2) \<inter> (Es SG2 \<inter> EsI SG2) = {}"
    using assms(2) assms(3) disj_V_E wf_sg_wf_g[of SG2]
      ran_restrict_sub[of "src SG2" "EsI SG2"]
      ran_restrict_sub[of "tgt SG2" "EsI SG2"]
    by (auto simp add: rst_Ns_def wf_g_def disjGs_def 
        ftotal_on_def)
next
  show "Es SG1 \<inter> EsI SG1 \<inter> (Es SG2 \<inter> EsI SG2) = {}"
    using assms EsI_sub_Es[of SG1] EsI_sub_Es[of SG2]
    disjGs_imp_disjEsGs[of SG1 SG2]
    by (auto simp add:  disjEsGs_def)
qed

lemma inh_disj_SGs_disj_fields: 
  assumes "wf_sg SG1" and "wf_sg SG2" and h3: "disjGs SG1 SG2"
  shows "Field (inh SG1) \<inter> Field (inh SG2) = {}"
  using assms disjGs_inhG[of SG1 SG2] wf_sg_wf_g[of SG1]
        wf_sg_wf_g[of SG2] wf_g_inhG[of SG1] wf_g_inhG[of SG2] 
        by (simp add: inh_def relG_disj_Gs)
      thm restrict_cup_wf_1

lemma inhG_USG:
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "inhG (SG1 USG SG2) = inhG (SG1) UG  inhG (SG2)"
proof -
  have h: "EsI SG1 \<union> EsI SG2 = EsI SG2 \<union> EsI SG1" by auto
  show ?thesis
  using assms disjGs_imp_disjEsGs[of SG1 SG2]
    restrict_cup_wf_1[of SG2 SG1] restrict_cup_wf_1[of SG1 SG2]
  by (simp add: inhG_def restrict_USG EsI_USG 
      disjGs_sym h)
qed

lemma inh_USG:
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "inh (SG1 USG SG2) = inh (SG1) \<union>  inh (SG2)"
proof -
  have h1: "EsI SG1 \<union> EsI SG2 = EsI SG2 \<union> EsI SG1" by auto
  have h2: "SG1 \<bowtie>\<^sub>E\<^sub>S EsI SG1 = inhG SG1" 
    by (simp add: inhG_def)
  have h3: "SG2 \<bowtie>\<^sub>E\<^sub>S EsI SG2 = inhG SG2" 
    by (simp add: inhG_def)
  show ?thesis
  using assms disjGs_imp_disjEsGs[of SG1 SG2]
      wf_sg_wf_g[of SG1] wf_sg_wf_g[of SG2]
      disjGs_inhG[of SG1 SG2] wf_g_inhG[of SG1] wf_g_inhG[of SG2]
      disjGs_imp_disjEsGs[of "inhG SG1" "inhG SG2"]
      restrict_cup_wf_1[of SG2 SG1] restrict_cup_wf_1[of SG1 SG2]
  by (simp add: inh_def inhG_def restrict_USG EsI_USG 
      disjGs_sym h1, (subst h2)+, (subst h3)+)
      (simp add: relG_UG)
qed

lemma srcma_disj_SGs:
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "dom(srcma SG1) \<inter> dom(srcma SG2) = {}"
  using assms wf_sg_ftotal_on_srcma[of SG1]
        wf_sg_ftotal_on_srcma[of SG2] 
        disjGs_imp_disjEsGs[of SG1 SG2] EsC_sub_ES[of SG1]
        EsC_sub_ES[of SG2]
      by (simp add: ftotal_on_def disjEsGs_def, force)

lemma dom_srcma_ecomp_uni_sub_dom_srcma:
  shows "dom(srcma_ecomp_uni SG) \<subseteq> dom(srcma SG)"
  by (simp add: srcma_def subsetI)

lemma dom_srcma_erel_uni_sub_dom_srcma:
  shows "dom(srcma_erel_uni SG) \<subseteq> dom(srcma SG)"
  by (simp add: srcma_def subsetI)

lemma srcma_ecomp_uni_USG_in_SG1:
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
    and "e \<in> Es SG1"
  shows "srcma_ecomp_uni (SG1 USG SG2) e = srcma_ecomp_uni SG1 e"
  using assms EsTy_sub_Es[of SG1 "{ecomp duni}"]
    EsTy_sub_Es[of SG2 "{ecomp duni}"]
    disjGs_imp_disjEsGs[of "SG1" "SG2"]
  by (auto simp add: srcma_ecomp_uni_def EsTy_USG disjEsGs_def)

lemma srcma_ecomp_uni_USG_nin_SG1:
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
    and "e \<notin> Es SG1"
  shows "srcma_ecomp_uni (SG1 USG SG2) e = srcma_ecomp_uni SG2 e"
  using assms EsTy_sub_Es[of SG1 "{ecomp duni}"]
          EsTy_sub_Es[of SG2 "{ecomp duni}"]
          disjGs_imp_disjEsGs[of "SG1" "SG2"]
  by (auto simp add: srcma_ecomp_uni_def EsTy_USG disjEsGs_def)
  
lemma srcma_ecomp_uni_USG:
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "srcma_ecomp_uni (SG1 USG SG2) = (srcma_ecomp_uni SG1) ++ (srcma_ecomp_uni SG2)"
proof -
  have h: "dom(srcma_ecomp_uni SG1) \<inter> dom(srcma_ecomp_uni SG2) = {}"
    using assms dom_srcma_ecomp_uni_sub_dom_srcma[of SG1]
      dom_srcma_ecomp_uni_sub_dom_srcma[of SG2]
      srcma_disj_SGs[of SG1 SG2]
    by (auto)
  show ?thesis
  proof
    fix e
    show "srcma_ecomp_uni (SG1 USG SG2) e =
         (srcma_ecomp_uni SG1 ++ srcma_ecomp_uni SG2) e"
    proof (case_tac "e \<in> Es SG1")
      assume h1: "e \<in> Es SG1"
      hence h2: "srcma_ecomp_uni (SG1 USG SG2) e = srcma_ecomp_uni SG1 e"
        using assms by (simp add: srcma_ecomp_uni_USG_in_SG1)
      have "e \<notin> dom(srcma_ecomp_uni SG2)"
      proof (rule ccontr, simp)
        assume "e \<in> dom (srcma_ecomp_uni SG2)"
        then show "False" 
          using EsC_sub_ES assms(2) assms(3) disjGs_imp_disjEsGs 
              es_disj_Ga_Gb ftotal_on_dom h1 srcma_def 
              wf_sg_ftotal_on_srcma by fastforce
      qed
      hence "(srcma_ecomp_uni SG1 ++ srcma_ecomp_uni SG2) e = srcma_ecomp_uni SG1 e"
        using h map_add_disj_dom2f[where f = "srcma_ecomp_uni SG1"]
        by simp
      then show "srcma_ecomp_uni (SG1 USG SG2) e =
        (srcma_ecomp_uni SG1 ++ srcma_ecomp_uni SG2) e"
        using h2 by auto
    next
      assume h1: "e \<notin> Es SG1"
      hence h2: "srcma_ecomp_uni (SG1 USG SG2) e = srcma_ecomp_uni SG2 e"
        using assms by (simp add: srcma_ecomp_uni_USG_nin_SG1)
      have "e \<notin> dom(srcma_ecomp_uni SG1)"
      proof (rule ccontr, simp)
        assume "e \<in> dom (srcma_ecomp_uni SG1)"
        then show "False" 
          using EsC_sub_ES assms(1) assms(3) disjGs_imp_disjEsGs 
              es_disj_Ga_Gb ftotal_on_dom h1 srcma_def 
              wf_sg_ftotal_on_srcma by fastforce
      qed
      hence "(srcma_ecomp_uni SG1 ++ srcma_ecomp_uni SG2) e = srcma_ecomp_uni SG2 e"
        using h map_add_disj_dom2f[where x = e and f = "srcma_ecomp_uni SG2" and g = "srcma_ecomp_uni SG1"]
        map_add_comm[of "srcma_ecomp_uni SG1" "srcma_ecomp_uni SG2"]
        by force
      then show "srcma_ecomp_uni (SG1 USG SG2) e =
        (srcma_ecomp_uni SG1 ++ srcma_ecomp_uni SG2) e"
        using h2 by auto
    qed
  qed
qed

lemma srcma_erel_uni_USG_in_SG1:
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
    and "e \<in> Es SG1"
  shows "srcma_erel_uni (SG1 USG SG2) e = srcma_erel_uni SG1 e"
  using assms EsTy_sub_Es[of SG1 "{erel duni}"]
    EsTy_sub_Es[of SG2 "{erel duni}"]
    disjGs_imp_disjEsGs[of "SG1" "SG2"]
  by (auto simp add: srcma_erel_uni_def EsTy_USG disjEsGs_def)

lemma srcma_erel_uni_USG_nin_SG1:
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
    and "e \<notin> Es SG1"
  shows "srcma_erel_uni (SG1 USG SG2) e = srcma_erel_uni SG2 e"
  using assms EsTy_sub_Es[of SG1 "{erel duni}"]
          EsTy_sub_Es[of SG2 "{erel duni}"]
          disjGs_imp_disjEsGs[of "SG1" "SG2"]
  by (auto simp add: srcma_erel_uni_def EsTy_USG disjEsGs_def)

lemma srcma_erel_uni_USG:
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "srcma_erel_uni (SG1 USG SG2) = (srcma_erel_uni SG1) ++ (srcma_erel_uni SG2)"
proof -
  have h: "dom(srcma_erel_uni SG1) \<inter> dom(srcma_erel_uni SG2) = {}"
  using assms dom_srcma_erel_uni_sub_dom_srcma[of SG1]
      dom_srcma_erel_uni_sub_dom_srcma[of SG2]
      srcma_disj_SGs[of SG1 SG2]
    by (auto)
  show ?thesis
  proof
    fix e
    show "srcma_erel_uni (SG1 USG SG2) e =
         (srcma_erel_uni SG1 ++ srcma_erel_uni SG2) e"
    proof (case_tac "e \<in> Es SG1")
      assume h1: "e \<in> Es SG1"
      hence h2: "srcma_erel_uni (SG1 USG SG2) e = srcma_erel_uni SG1 e"
        using assms srcma_erel_uni_USG_in_SG1 by auto
      have "e \<notin> dom(srcma_erel_uni SG2)"
      proof (rule ccontr, simp)
        assume "e \<in> dom (srcma_erel_uni SG2)"
        then show "False" 
          using EsC_sub_ES assms(2) assms(3) disjGs_imp_disjEsGs 
              es_disj_Ga_Gb ftotal_on_dom h1 srcma_def 
              wf_sg_ftotal_on_srcma by fastforce
      qed
      hence "(srcma_erel_uni SG1 ++ srcma_erel_uni SG2) e = srcma_erel_uni SG1 e"
        using h map_add_disj_dom2f[where f = "srcma_erel_uni SG1"]
        by simp
      then show "srcma_erel_uni (SG1 USG SG2) e =
        (srcma_erel_uni SG1 ++ srcma_erel_uni SG2) e"
        using h2 by auto
    next
      assume h1: "e \<notin> Es SG1"
      hence h2: "srcma_erel_uni (SG1 USG SG2) e = srcma_erel_uni SG2 e"
        using assms srcma_erel_uni_USG_nin_SG1 by auto
      have "e \<notin> dom(srcma_erel_uni SG1)"
      proof (rule ccontr, simp)
        assume "e \<in> dom (srcma_erel_uni SG1)"
        then show "False" 
          using EsC_sub_ES assms(1) assms(3) disjGs_imp_disjEsGs 
              es_disj_Ga_Gb ftotal_on_dom h1 srcma_def 
              wf_sg_ftotal_on_srcma by fastforce
      qed
      hence "(srcma_erel_uni SG1 ++ srcma_erel_uni SG2) e = srcma_erel_uni SG2 e"
        using h map_add_disj_dom2f[where x = e and f = "srcma_erel_uni SG2" and g = "srcma_erel_uni SG1"]
        map_add_comm[of "srcma_erel_uni SG1" "srcma_erel_uni SG2"]
        by force
      then show "srcma_erel_uni (SG1 USG SG2) e =
        (srcma_erel_uni SG1 ++ srcma_erel_uni SG2) e"
        using h2 by auto
    qed
  qed
qed
 
lemma srcma_USG:
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "srcma (SG1 USG SG2) = srcma (SG1) ++ srcma (SG2)"
proof
  fix e
  show "srcma (SG1 USG SG2) e = (srcma (SG1) ++ srcma (SG2)) e"
    by (smt (verit, ccfv_threshold) assms disjoint_iff domIff 
        map_add_dom_app_simps(1) map_add_dom_app_simps(3) 
        srcm_cupSG srcma_def srcma_disj_SGs 
        srcma_ecomp_uni_USG srcma_erel_uni_USG)
qed

lemma acyclic_SGr_Un_dist: 
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "acyclicGr (inhG (SG1 USG SG2)) = (acyclicGr (inhG SG1) \<and> acyclicGr (inhG SG2))"
  using assms wf_sg_wf_g[of SG1] wf_sg_wf_g[of SG2] 
    disjGs_imp_disjEsGs[of SG1 SG2]
    wf_g_inhG[of SG1] wf_g_inhG[of SG2] 
    disjGs_inhG[of SG1 SG2]
  by (simp add: inhG_USG acyclic_Gr_dist_disj)

lemma is_wf_sg_Un: 
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "wf_sg (SG1 USG SG2)"
proof (simp add: wf_sg_def)
  apply_end(rule conjI)
  show "wf_g (SG1 USG SG2)"
    using assms wf_sg_wf_g[of SG1] wf_sg_wf_g[of SG2]  
    by (simp add: is_wf_g_Un2)
next
  apply_end(rule conjI)
  show "ftotal_on (nty (SG1 USG SG2)) (Ns (SG1 USG SG2)) SGNT_set"
    using assms wf_sg_ftotal_on_nty[of SG1] wf_sg_ftotal_on_nty[of SG2] 
    ftotal_on_map_add[where f = "nty SG1" and g = "nty SG2" 
      and A="Ns SG1" and C="Ns SG2" and B="SGNT_set" and D="SGNT_set"]
    by (auto simp add: cupSG_def  disjGs_def)
next
  apply_end(rule conjI)
  show "ftotal_on (ety (SG1 USG SG2)) (Es (SG1 USG SG2)) SGET_set"
    using assms wf_sg_ftotal_on_ety[of SG1] wf_sg_ftotal_on_ety[of SG2] 
    ftotal_on_map_add[where f = "ety SG1" and g = "ety SG2" 
      and A="Es SG1" and C="Es SG2" and B="SGET_set" and D="SGET_set"] 
    by (auto simp add: cupSG_def  disjGs_def)
next
  apply_end(rule conjI)
  show "ftotal_on (srcma (SG1 USG SG2)) (EsC (SG1 USG SG2)) MultC_set"
  using assms wf_sg_ftotal_on_srcma[of SG1] 
        wf_sg_ftotal_on_srcma[of SG2] 
         EsC_sub_ES[of SG1] EsC_sub_ES[of SG2] 
         disjGs_imp_disjEsGs[of SG1 SG2]
        ftotal_on_map_add[where f = "srcma SG1" and g = "srcma SG2" 
      and A="EsC SG1" and C="EsC SG2" and B="MultC_set" and D="MultC_set"]
  by (simp add: EsC_USG srcma_USG disjEsGs_def, force)
next
  apply_end(rule conjI)
  show "ftotal_on (tgtm SG1 ++ tgtm SG2) (EsC (SG1 USG SG2)) MultC_set"
  using assms wf_sg_ftotal_on_tgtm[of SG1] 
        wf_sg_ftotal_on_tgtm[of SG2] 
        EsC_sub_ES[of SG1] EsC_sub_ES[of SG2] 
        disjGs_imp_disjEsGs[of SG1 SG2]
        ftotal_on_map_add[where f = "tgtm SG1" and g = "tgtm SG2" 
      and A="EsC SG1" and C="EsC SG2" and B="MultC_set" and D="MultC_set"]
  by (simp add: EsC_USG disjEsGs_def, force)
next
  apply_end(rule conjI)
  show "dom (db SG2) \<union> dom (db SG1) = EsD (SG1 USG SG2)"
  using assms wf_sg_dom_db[of SG1] wf_sg_dom_db[of SG2] 
  by (auto simp add:  EsD_USG)
next
  show "multsOk (SG1 USG SG2)"
qed
        
definition morphSGr :: "SGr \<Rightarrow> SGr \<Rightarrow> Morph set"
where
  "morphSGr SG1 SG2 \<equiv> {r. is_wf_sg SG1 \<and> is_wf_sg SG2
      \<and> ftotal_on (fV r) (Ns SG1) (Ns SG2) 
      \<and> ftotal_on (fE r) (Es SG1) (Es SG2)  
      \<and> srcst SG1 O pfunToRel(fV r)  \<subseteq> pfunToRel(fE r) O srcst SG2  
      \<and> tgtst SG1 O pfunToRel(fV r) \<subseteq> pfunToRel(fE r) O tgtst SG2  
      \<and> inhst SG1 O pfunToRel (fV r) \<subseteq> pfunToRel (fV r) O inhst SG2}"

definition morphGr2SGr :: "Gr \<Rightarrow> SGr \<Rightarrow> Morph set"
where
  "morphGr2SGr G1 SG2 \<equiv> {r. is_wf_g G1 \<and> is_wf_sg SG2
      \<and> ftotal_on (fV r) (Ns G1) (Ns SG2) 
      \<and> ftotal_on (fE r) (Es G1) (Es SG2)  
      \<and> pfunToRel((fV r) \<circ>\<^sub>m (src G1)) \<subseteq> pfunToRel(fE r) O srcst SG2  
      \<and> pfunToRel((fV r) \<circ>\<^sub>m (tgt G1)) \<subseteq> pfunToRel(fE r) O tgtst SG2}"

end
