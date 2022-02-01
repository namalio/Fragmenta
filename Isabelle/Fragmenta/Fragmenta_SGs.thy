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

definition consSG::"Gr \<Rightarrow> (V \<rightharpoonup> SGNT) \<Rightarrow> (E \<rightharpoonup> SGET) \<Rightarrow> (E \<rightharpoonup> MultC) \<Rightarrow> (E \<rightharpoonup> MultC) \<Rightarrow> (E \<rightharpoonup> E) \<Rightarrow> SGr"
  where
  "consSG G nt et ms mt d = 
    \<lparr>Ns = Ns G, Es = Es G, src = src G, tgt =  tgt G, 
    nty = nt, ety = et, srcm = ms, tgtm = mt, db = d\<rparr>"

(* Defines the empty SG*)
definition emptySG :: "SGr"
where
  "emptySG \<equiv> consSG emptyG Map.empty Map.empty Map.empty Map.empty Map.empty"

lemma emptySG_eq:
  shows "emptySG = \<lparr>Ns = {}, Es = {}, src = Map.empty, tgt =  Map.empty, 
    nty = Map.empty, ety = Map.empty, srcm = Map.empty, tgtm = Map.empty, 
    db = Map.empty\<rparr>" 
  by (auto simp add: emptySG_def consSG_def emptyG_eq)

lemma Ns_emptySG[simp]: "Ns emptySG = {}"
  by (simp add: emptySG_eq)

lemma Es_emptySG[simp]: "Es emptySG = {}"
  by (simp add: emptySG_eq)

lemma src_emptySG[simp]: "src emptySG = Map.empty"
  by (simp add: emptySG_eq)

lemma tgt_emptySG[simp]: "tgt emptySG = Map.empty"
  by (simp add: emptySG_eq)

lemma nty_emptySG[simp]: "nty emptySG = Map.empty"
  by (simp add: emptySG_eq)

lemma ety_emptySG[simp]: "ety emptySG = Map.empty"
  by (simp add: emptySG_eq)

lemma srcm_emptySG[simp]: "srcm emptySG = Map.empty"
  by (simp add: emptySG_eq)

lemma tgtm_emptySG[simp]: "tgtm emptySG = Map.empty"
  by (simp add: emptySG_eq)

lemma db_emptySG[simp]: "db emptySG = Map.empty"
  by (simp add: emptySG_eq)

lemma SGr_eq:
  shows "(SG1 = SG2) \<longleftrightarrow> Ns SG1 = Ns SG2 \<and> Es SG1 = Es SG2 \<and> src SG1 = src SG2 
    \<and> tgt SG1 = tgt SG2 \<and> nty SG1 = nty SG2 \<and> ety SG1 = ety SG2 
    \<and> srcm SG1 = srcm SG2 \<and> tgtm SG1 = tgtm SG2 \<and> db SG1 = db SG2 
    \<and> SGr.more SG1 = SGr.more SG2"
    by (auto)

definition gr_sg :: "SGr \<Rightarrow> Gr"
where
  "gr_sg SG = consG (Ns SG) (Es SG) (src SG) (tgt SG)"

lemma gr_sg_emptySG[simp]:
  "gr_sg emptySG = emptyG"
  by (auto simp add: gr_sg_def emptySG_def emptyG_def consSG_def consG_def)

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
  by (simp add: EsTy_def emptySG_eq)

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

definition inhG ::"SGr \<Rightarrow> Gr"
where
  "inhG SG \<equiv> restrict SG (EsI SG)"

lemma Ns_inhG[simp]: "Ns (inhG SG) = rNs SG (EsI SG)"
  by (simp add: inhG_def)

lemma Es_inhG[simp]: "Es (inhG SG) = Es SG \<inter> (EsI SG)"
  by (simp add: inhG_def)

lemma src_inhG[simp]: "src (inhG SG) = src SG |` EsI SG"
  by (simp add: inhG_def)

lemma tgt_inhG[simp]: "tgt (inhG SG) = tgt SG |` EsI SG"
  by (simp add: inhG_def)

definition inh ::"SGr \<Rightarrow> V rel"
where
  "inh SG \<equiv> (inhG SG)\<^sup>\<Leftrightarrow>"

lemma inh_noedgesI: "EsI SG = {} \<Longrightarrow> inh SG = {}"
  by (simp add: EsI_def inh_def relG_def adjacent_def restrict_def inhG_def)

lemma acyclic_sg_noEI:"EsI SG = {} \<Longrightarrow> acyclicGr (inhG SG)"
  by (simp add: acyclicGr_def inh_noedgesI wf_acyclic inh_def 
      inhG_def emptyG_eq relG_def adjacent_def)

definition srcma ::"SGr \<Rightarrow> E \<rightharpoonup> MultC"
where
  "srcma SG \<equiv> (srcm SG) 
    ++ (\<lambda> x. if x \<in> EsTy SG {ecomp duni} then Some (sm (val 1)) else None) 
    ++ (\<lambda> x. if x \<in> EsTy SG {erel duni} then Some (sm many) else None)"

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
  by (simp add: esIncidentst_def)

lemma esIncidentst_empty_vs:
  "SG \<circ>\<rightarrow>\<circ>\<^sup>* {} = {}"
  by (simp add: esIncidentst_def)

definition optsVoluntary::"SGr \<Rightarrow>bool"
  where
  "optsVoluntary SG \<equiv> pfunToRel (ety SG) ``((SG \<circ>\<rightarrow>\<circ>\<^sup>* (NsO SG)) - (EsI SG)) \<subseteq> {ewander}"

definition inhOk::"SGr \<Rightarrow>bool"
  where
  "inhOk SG \<equiv> (\<forall> v v'. (v, v') \<in> inh SG \<longrightarrow> the (nty SG v) <\<^sub>N\<^sub>T the (nty SG v'))
    \<and> acyclicGr (inhG SG) 
    \<and> pfun_on (((inhG SG) \<ominus>\<^sub>N\<^sub>S (NsV SG))\<^sup>\<Leftrightarrow>) (Ns SG)(Ns SG)"

definition wf_sg :: "SGr \<Rightarrow> bool"
where
  "wf_sg SG \<equiv> wf_g SG 
      \<and> ftotal_on (nty SG) (Ns SG) SGNT_set 
      \<and> ftotal_on (ety SG) (Es SG) SGET_set 
      \<and> ftotal_on (srcma SG) (EsC SG) MultC_set
      \<and> ftotal_on (tgtm SG) (EsC SG) MultC_set
      \<and> dom (db SG) = EsD SG
      \<and> multsOk SG
      \<and> optsVoluntary SG
      \<and> inhOk SG"

definition wf_tsg :: "SGr \<Rightarrow> bool"
  where
  "wf_tsg SG \<equiv> wf_sg SG \<and> NsEther SG \<subseteq> Range(inh SG)
  \<and> ran (db SG) \<subseteq> EsA SG
  \<and> (\<forall> e \<in> EsD SG. (the(src SG e), the (src SG (the (db SG e)))) \<in> (inhst SG)
    \<and> (the (tgt SG e), the (tgt SG (the (db SG e)))) \<in> (inhst SG))"

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

lemma wf_sg_inhOk:
  assumes "wf_sg SG"
  shows "inhOk SG"
  using assms by (simp add: wf_sg_def)

lemma NsTy_sub_Ns: 
  assumes "wf_sg SG"
  shows "NsTy SG ets \<subseteq> Ns SG"
  using assms wf_sg_ftotal_on_nty[of SG]
  by (auto simp add: NsTy_def ftotal_on_def)


lemma NsP_sub_Ns: 
  assumes "wf_sg SG"
  shows "NsP SG \<subseteq> Ns SG"
  using assms wf_sg_ftotal_on_nty [of SG]
  by (auto simp add: NsP_def NsTy_sub_Ns)

lemma NsO_sub_Ns: 
  assumes "wf_sg SG"
  shows "NsO SG \<subseteq> Ns SG"
  using assms wf_sg_ftotal_on_nty [of SG]
  by (auto simp add: NsO_def NsTy_sub_Ns)

lemma NsV_sub_Ns: 
  assumes "wf_sg SG"
  shows "NsV SG \<subseteq> Ns SG"
  using assms wf_sg_ftotal_on_nty [of SG]
  by (auto simp add: NsV_def NsTy_sub_Ns)

lemma wf_g_inhG:
  assumes "wf_g SG"
  shows "wf_g (inhG SG)"
  using assms by (simp add: inhG_def wf_restrict)

lemma NsInhG_sub_Ns: 
  assumes "wf_sg SG"
  shows "Ns (inhG SG) \<subseteq> Ns SG"
  using assms ran_restrict_sub[of "src SG" "EsI SG"] 
    ran_restrict_sub[of "tgt SG" "EsI SG"] 
    wf_sg_wf_g[of SG] ran_src_G[of SG]
    ran_tgt_G[of SG]
  by (auto simp add: inhG_def rNs_def)

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

lemma EsA_sub_Es: 
  assumes "wf_sg SG"
  shows "EsA SG \<subseteq> Es SG"
  using assms wf_sg_ftotal_on_ety[of SG]
  by (auto simp add: EsA_def EsTy_sub_Es)

lemma EsW_sub_Es: 
  assumes "wf_sg SG"
  shows "EsW SG \<subseteq> Es SG"
  using assms wf_sg_ftotal_on_ety[of SG]
  by (auto simp add: EsW_def EsTy_sub_Es)

lemma EsD_sub_Es: 
  assumes "wf_sg SG"
  shows "EsD SG \<subseteq> Es SG"
  using assms wf_sg_ftotal_on_ety[of SG]
  by (auto simp add: EsD_def EsTy_def ftotal_on_def)

lemma EsC_sub_Es: 
  assumes "wf_sg SG"
  shows "EsC SG \<subseteq> Es SG"
  using assms wf_sg_ftotal_on_ety[of SG]
  by (auto simp add: EsC_def EsA_sub_Es EsW_sub_Es EsD_sub_Es)

lemma Domain_inh:
  assumes "wf_sg SG"
  shows "Domain (inh SG) \<subseteq> Ns SG"
  using assms wf_sg_ftotal_on_srcG[of SG]
  by (auto simp add: inh_def relG_def adjacent_def ftotal_on_def 
      EsI_def EsTy_def
      restrict_map_def inhG_def intro!: ranI)

lemma Range_inh:
  assumes "wf_sg SG"
  shows "Range (inh SG) \<subseteq> Ns SG"
  using assms wf_sg_ftotal_on_tgtG[of SG]
  by (auto simp add: inh_def relG_def adjacent_def ftotal_on_def 
      EsI_def EsTy_def
      restrict_map_def inhG_def intro!: ranI)

lemma inhG_disj_Es:
  assumes "disjEsGs SG1 SG2"
  shows "disjEsGs (inhG SG1) (inhG SG2)"
  using assms EsI_sub_Es
  by (auto simp add: disjEsGs_def)

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

lemma dom_srcst_sub_Es:
  assumes "wf_sg SG"
  shows "Domain (srcst SG) \<subseteq> Es SG"
  using assms EsC_sub_Es
  by (auto simp add: srcst_def relcomp_unfold dres_def Domain_iff 
      subsetI)

lemma dom_tgtst_sub_Es:
  assumes "wf_sg SG"
  shows "Domain (tgtst SG) \<subseteq> Es SG"
  using assms EsC_sub_Es
  by (auto simp add: tgtst_def relcomp_unfold dres_def Domain_iff)

lemma esIncidentst_SG_Sub_EsSG:
  assumes "wf_sg SG"
  shows "SG \<circ>\<rightarrow>\<circ>\<^sup>* vs \<subseteq> Es SG"
  using assms dom_srcst_sub_Es[of SG] dom_tgtst_sub_Es[of SG]
  by (auto simp add: esIncidentst_def)

lemma esIncidentst_Un:
  shows "SG \<circ>\<rightarrow>\<circ>\<^sup>* (vs1 \<union> vs2) = SG \<circ>\<rightarrow>\<circ>\<^sup>* vs1 \<union> SG \<circ>\<rightarrow>\<circ>\<^sup>* vs2"
  using esIncidentst_def by auto

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

lemma USG_EmptySG:
  "emptySG USG SG = SG"
  by (simp add: emptySG_eq cupSG_def)

lemma emptySG_wf:
  "wf_sg emptySG"
proof (simp add: wf_sg_def)
  apply_end (rule conjI)
  show "wf_g emptySG"
  by (simp add: emptySG_eq wf_g_def ftotal_on_def)
next
  apply_end (rule conjI)
  show "ftotal_on Map.empty {} SGNT_set"
    by (simp add: ftotal_on_def)
next
  apply_end (rule conjI)
  show "ftotal_on Map.empty {} SGET_set"
    by (simp add: ftotal_on_def)
next
  apply_end (rule conjI)
  show "ftotal_on (srcma emptySG) {} MultC_set"
    by (simp add: ftotal_on_def srcma_def)
next
  apply_end (rule conjI)
  show "ftotal_on Map.empty {} MultC_set"
    by (simp add: ftotal_on_def)
next
  apply_end (rule conjI)
  show "multsOk emptySG"
    by (simp add: multsOk_def)
next
  apply_end (rule conjI)
  show "optsVoluntary emptySG"
    by (simp add: optsVoluntary_def)
next
  show "inhOk emptySG"
    by (simp add: inhOk_def emptySG_eq inhG_def pfun_on_def
        rel_on_def single_valued_def NsV_def inh_def EsI_def
        EsTy_def NsTy_def emptyG_eq acyclicGr_def relG_def 
        adjacent_def acyclic_def)
qed

definition subsumeSG::"SGr \<Rightarrow>(V \<rightharpoonup> V) \<Rightarrow> SGr" (infixl "\<odot>\<^sup>S\<^sup>G" 100)
  where
  "SG \<odot>\<^sup>S\<^sup>G s \<equiv> if fpartial_on s (NsP SG) (Ns SG) then 
    consSG ((gr_sg SG) \<odot> s) ((dom s-ran s) \<unlhd>\<^sub>m (nty SG))
    (ety SG) (srcm SG) (tgtm SG) (db SG) 
    else SG"

(*lemma emptySG_subsume_map_empty[simp]: 
  shows "emptySG \<odot> Map.empty = emptyG"
  by (simp add: subsumeG_def 
      fpartial_on_def emptyG_eq)*)

lemma Ns_gr_sg_eq:
  "Ns (gr_sg SG) = Ns SG"
  by (simp add: gr_sg_def consG_def)

lemma Es_gr_sg_eq:
  "Es (gr_sg SG) = Es SG"
  by (simp add: gr_sg_def consG_def)

lemma wf_g_SG_eq_gr_sg:
  "wf_g SG = wf_g (gr_sg SG)"
  by (simp add: consG_def gr_sg_def wf_g_def)

lemma subsumeSG_not_from_NsP:
  assumes "\<not>fpartial_on s (NsP SG) (Ns SG)"
  shows "(SG \<odot>\<^sup>S\<^sup>G s) = SG"
  using assms by (simp add: subsumeSG_def)

lemma gr_sg_subsumeSG_eq:
  assumes "fpartial_on s (NsP SG) (Ns SG)"
  shows "gr_sg (SG \<odot>\<^sup>S\<^sup>G s) = (gr_sg SG) \<odot> s"
  using assms
  by (simp add: subsumeSG_def consG_def consSG_def 
      gr_sg_def)

(*
  NsP_sub_Ns[of SG] not_fpartial_on_sub[of s "Ns SG" "Ns SG" "NsP SG"]
  by (simp add: subsumeSG_def consG_def consSG_def 
      gr_sg_def)
 lemma SG_subsumeg_eq:
  "SG \<odot> s = (gr_sg SG) \<odot> s"
  by (simp add: consG_def gr_sg_def subsumeG_def)*)

lemma subsumeSG_EmptySG:
  "emptySG \<odot>\<^sup>S\<^sup>G s = emptySG"
  using emptySG_def
  by (simp only: subsumeSG_def fpartial_on_def gr_sg_emptySG
      subsumeG_emptyG, simp)

lemma subsumeSG_MapEmpty[simp]:
  assumes "wf_sg SG"
  shows "SG \<odot>\<^sup>S\<^sup>G Map.empty = SG"
  using assms wf_sg_wf_g[of SG]
  by (auto simp add: subsumeSG_def fpartial_on_def 
      wf_g_SG_eq_gr_sg subsumeG_empty)
    (simp add: consSG_def gr_sg_def consG_def)

lemma ety_subsumeSG:
  shows "ety (SG \<odot>\<^sup>S\<^sup>G s) = ety SG"
  by (simp add: subsumeSG_def consSG_def)

lemma nty_subsumeSG_s_ok:
  assumes "fpartial_on s (NsP SG) (Ns SG)"
  shows "nty (SG \<odot>\<^sup>S\<^sup>G s) = (dom s - ran s) \<unlhd>\<^sub>m nty SG"
  using assms by (simp add: subsumeSG_def consSG_def)

lemma srcm_subsumeSG:
  shows "srcm (SG \<odot>\<^sup>S\<^sup>G s) = srcm SG"
  by (simp add: subsumeSG_def consSG_def)

lemma tgtm_subsumeSG:
  shows "tgtm (SG \<odot>\<^sup>S\<^sup>G s) = tgtm SG"
  by (simp add: subsumeSG_def consSG_def)

lemma db_subsumeSG:
  shows "db (SG \<odot>\<^sup>S\<^sup>G s) = db SG"
  by (simp add: subsumeSG_def consSG_def)

lemma EsTy_subsumeSG:
  shows "EsTy (SG \<odot>\<^sup>S\<^sup>G s) ets = EsTy (SG) ets"
  by (simp add: EsTy_def ety_subsumeSG)

lemma NsO_subsumeSG:
  assumes "wf_sg SG" and "fpartial_on s (NsP SG) (Ns SG)"
  shows "NsO (SG \<odot>\<^sup>S\<^sup>G s) = NsO (SG)"
proof -
  have "NsP SG  \<inter> NsO SG = {}"
    using assms(1) wf_sg_ftotal_on_nty[of SG]
    by (auto simp add: NsP_def NsO_def NsTy_def ftotal_on_def)
  have "dom s \<subseteq> NsP SG"
    using assms by (simp add: fpartial_on_def)
  have "(dom s - ran s) \<inter> dom(nty SG \<rhd>\<^sub>m {nopt}) = {}"
  proof (rule ccontr)
    assume "(dom s - ran s) \<inter> dom (nty SG \<rhd>\<^sub>m {nopt}) \<noteq> {}"
    then obtain x where "x \<in> (dom s - ran s) \<inter> dom (nty SG \<rhd>\<^sub>m {nopt})" 
      by auto
    from \<open>x \<in> (dom s - ran s) \<inter> dom (nty SG \<rhd>\<^sub>m {nopt})\<close> 
    have "x \<in> NsP SG" 
      using \<open>dom s \<subseteq> NsP SG\<close> by auto
    from \<open>x \<in> (dom s - ran s) \<inter> dom (nty SG \<rhd>\<^sub>m {nopt})\<close> 
    have "x \<in> dom (nty SG \<rhd>\<^sub>m {nopt})" by auto
    hence "x \<in> NsO SG"
      using assms wf_sg_ftotal_on_nty[of SG]
      by (auto simp add: NsO_def NsTy_def mrres_def 
          ftotal_on_def fpartial_on_def domIff split: if_splits)
    then show "False"
      using \<open>x \<in> NsP SG\<close> \<open>x \<in> NsO SG\<close> \<open>NsP SG  \<inter> NsO SG = {}\<close> 
      by auto 
  qed  
  then show ?thesis 
    using assms vimage_is_dom_rres[of "nty SG" "{nopt}"]
    mdsub_vimage_is_int[of "(dom s - ran s)" "nty SG" "{nopt}"]
  by (auto simp add: NsO_def NsTy_def nty_subsumeSG_s_ok)
qed

lemma EsA_subsumeSG:
  shows "EsA (SG \<odot>\<^sup>S\<^sup>G s) = EsA SG"
  by (simp add: EsA_def EsTy_subsumeSG)

lemma EsW_subsumeSG:
  shows "EsW (SG \<odot>\<^sup>S\<^sup>G s) = EsW SG"
  by (simp add: EsW_def EsTy_subsumeSG)

lemma EsD_subsumeSG:
  shows "EsD (SG \<odot>\<^sup>S\<^sup>G s) = EsD SG"
  by (simp add: EsD_def EsTy_subsumeSG)

lemma EsI_subsumeSG:
  shows "EsI (SG \<odot>\<^sup>S\<^sup>G s) = EsI SG"
  by (simp add: EsI_def EsTy_subsumeSG)

lemma EsC_subsumeSG:
  shows "EsC (SG \<odot>\<^sup>S\<^sup>G s) = EsC SG"
  by (simp add: EsC_def EsA_subsumeSG EsW_subsumeSG 
      EsD_subsumeSG)

lemma srcma_subsumeSG:
  assumes "wf_sg SG" 
  shows "srcma (SG \<odot>\<^sup>S\<^sup>G s) = srcma SG"
  using assms wf_sg_ftotal_on_srcma[of SG]
  by (simp add:  consSG_def srcma_def EsTy_subsumeSG
      ftotal_on_def srcm_subsumeSG)

lemma wf_g_subsumeSG:
  assumes "wf_sg SG" and "fpartial_on s (NsP SG) (Ns SG)"
  shows "wf_g (SG \<odot>\<^sup>S\<^sup>G s)"
  using assms wf_sg_wf_g[of SG]
  by (simp add: wf_g_SG_eq_gr_sg gr_sg_subsumeSG_eq
      wf_subsumeG)

lemma ftotal_on_nty_subsumeSG:
  assumes "wf_sg SG" and "fpartial_on s (NsP SG) (Ns SG)"
  shows "ftotal_on (nty (SG \<odot>\<^sup>S\<^sup>G s)) (Ns (SG \<odot>\<^sup>S\<^sup>G s)) SGNT_set"
  using assms wf_sg_ftotal_on_nty[of SG] 
      dom_mdsub_if[of "nty SG" "Ns SG" s] 
      ran_mdsub_sub[of "dom s - ran s" "nty SG"]  
      NsP_sub_Ns[of SG]
    by (auto simp add: subsumeSG_def ftotal_on_def consSG_def
        subsumeG_def Ns_gr_sg_eq fpartial_on_def ran_def 
        restrict_map_def mdsub_def split: if_splits)

lemma ftotal_on_ety_subsumeSG:
  assumes "wf_sg SG" and "fpartial_on s (NsP SG) (Ns SG)"
  shows "ftotal_on (ety (SG \<odot>\<^sup>S\<^sup>G s)) (Es (SG \<odot>\<^sup>S\<^sup>G s)) SGET_set"
  using assms wf_sg_ftotal_on_ety[of SG]
    NsP_sub_Ns[of SG]
    by (auto simp add: subsumeSG_def ftotal_on_def consSG_def
        subsumeG_def Ns_gr_sg_eq Es_gr_sg_eq consG_def) 

lemma ftotal_on_srcma_subsumeSG:
  assumes "wf_sg SG" and "fpartial_on s (NsP SG) (Ns SG)"
  shows "ftotal_on (srcma (SG \<odot>\<^sup>S\<^sup>G s)) (EsC (SG \<odot>\<^sup>S\<^sup>G s)) MultC_set"
    using assms wf_sg_ftotal_on_srcma[of SG]
    by (simp add: srcma_subsumeSG EsC_subsumeSG)

lemma ftotal_on_tgtm_subsumeSG:
  assumes "wf_sg SG" and "fpartial_on s (NsP SG) (Ns SG)"
  shows "ftotal_on (tgtm (SG \<odot>\<^sup>S\<^sup>G s)) (EsC (SG \<odot>\<^sup>S\<^sup>G s)) MultC_set"
  using assms wf_sg_ftotal_on_tgtm[of SG]
  by (simp add: tgtm_subsumeSG EsC_subsumeSG)

lemma dom_db_eq_EsD_subsumeSG:
  assumes "wf_sg SG" and "fpartial_on s (NsP SG) (Ns SG)"
  shows "dom (db (SG \<odot>\<^sup>S\<^sup>G s)) = EsD (SG \<odot>\<^sup>S\<^sup>G s)"
    using assms wf_sg_dom_db
    by (simp add: db_subsumeSG EsD_subsumeSG)

lemma multsOk_subsumeSG:
  assumes "wf_sg SG" 
    and "fpartial_on s (NsP SG) (Ns SG)"
  shows "multsOk (SG \<odot>\<^sup>S\<^sup>G s)"
    using assms 
    by (simp add: multsOk_def EsC_subsumeSG ety_subsumeSG
        srcma_subsumeSG tgtm_subsumeSG wf_sg_def)


lemma if_in_inh_subsume_SG:
  assumes "wf_sg SG" 
    and "fpartial_on s (NsP SG) (Ns SG)" 
    and "(v, v') \<in> inh (SG \<odot>\<^sup>S\<^sup>G s)" 
  shows "\<exists> va vb. (va, vb) \<in> inh SG \<and> (s va = Some v \<or> va = v) \<and> (s vb = Some v' \<or> vb = v')"
proof -
  have h: "fpartial_on s (Ns (gr_sg SG)) (Ns (gr_sg SG))"
    using assms(1) assms(2) NsP_sub_Ns[of SG]
    by (auto simp add: gr_sg_def consG_def fpartial_on_def)
  obtain e where "e \<in> EsI SG 
    \<and> (mtotalise_in s (Ns SG) \<circ>\<^sub>m src SG) e = Some v
    \<and> (mtotalise_in s (Ns SG) \<circ>\<^sub>m tgt SG) e = Some v'"
    using \<open>(v, v') \<in> inh (SG \<odot>\<^sup>S\<^sup>G s)\<close> assms h 
      EsI_subsumeSG[of SG s]
    by (auto simp add: subsumeSG_def gr_sg_def consSG_def 
        consG_def subsumeG_def inh_def inhG_def relG_def
        adjacent_def)
  then obtain va vb where "src SG e = Some va 
    \<and> mtotalise_in s (Ns SG) va = Some v
    \<and> tgt SG e = Some vb \<and> mtotalise_in s (Ns SG) vb = Some v'"
      using \<open>e \<in> EsI SG 
      \<and> (mtotalise_in s (Ns SG) \<circ>\<^sub>m src SG) e = Some v
      \<and> (mtotalise_in s (Ns SG) \<circ>\<^sub>m tgt SG) e = Some v'\<close>
      map_add_not_in_ran_g[of v s "mid_on (Ns SG)"]
      by (auto simp add: map_comp_Some_iff)
  have "e \<in> EsI SG"
    using \<open>e \<in> EsI SG 
      \<and> (mtotalise_in s (Ns SG) \<circ>\<^sub>m src SG) e = Some v
      \<and> (mtotalise_in s (Ns SG) \<circ>\<^sub>m tgt SG) e = Some v'\<close> by auto
  have "src SG e = Some va \<and> s va = Some v \<or> src SG e = Some v \<and> va = v"
  proof (case_tac "s va \<noteq> Some v")
    assume "s va \<noteq> Some v"
    hence "src SG e = Some v \<and> va = v"
      using assms(1) wf_sg_wf_g ran_src_G[of SG]
      \<open>src SG e = Some va \<and> mtotalise_in s (Ns SG) va = Some v
      \<and> tgt SG e = Some vb \<and> mtotalise_in s (Ns SG) vb = Some v'\<close>
      by (auto simp add: map_add_dom_app_simps
          mtotalise_in_def mid_on_def intro!: ranI)
    then show ?thesis by simp
  next
    assume "\<not> s va \<noteq> Some v"
    hence "s va = Some v" by simp
    then show ?thesis 
      using \<open>src SG e = Some va \<and> mtotalise_in s (Ns SG) va = Some v
      \<and> tgt SG e = Some vb \<and> mtotalise_in s (Ns SG) vb = Some v'\<close>
      by (simp add: mtotalise_in_def)
  qed
  have "tgt SG e = Some vb \<and> s vb = Some v' \<or> tgt SG e = Some v' \<and> vb = v'"
  proof (case_tac "s vb \<noteq> Some v'")
    assume "s vb \<noteq> Some v'"
    hence "tgt SG e = Some v' \<and> vb = v'"
      using assms(1) wf_sg_wf_g ran_tgt_G[of SG]
      \<open>src SG e = Some va \<and> mtotalise_in s (Ns SG) va = Some v
      \<and> tgt SG e = Some vb \<and> mtotalise_in s (Ns SG) vb = Some v'\<close>
      by (auto simp add: map_add_dom_app_simps
          mtotalise_in_def mid_on_def intro!: ranI)
    then show ?thesis by simp
  next
    assume "\<not> s vb \<noteq> Some v'"
    hence "s vb = Some v'" by simp
    then show ?thesis 
      using \<open>src SG e = Some va \<and> mtotalise_in s (Ns SG) va = Some v
      \<and> tgt SG e = Some vb \<and> mtotalise_in s (Ns SG) vb = Some v'\<close>
      by (simp add: mtotalise_in_def)
  qed
  then show ?thesis
  proof
    assume "tgt SG e = Some vb \<and> s vb = Some v'"
    from \<open>src SG e = Some va \<and> s va = Some v \<or> src SG e = Some v \<and> va = v\<close>
    show ?thesis 
    proof
      assume "src SG e = Some va \<and> s va = Some v"
      hence "(va, vb) \<in> inh SG \<and> s va = Some v \<and> s vb = Some v'"
        using \<open>tgt SG e = Some vb \<and> s vb = Some v'\<close>
        \<open>e \<in> EsI SG\<close> assms(1) EsI_sub_Es[of SG]
        by (auto simp add: inh_def inhG_def restrict_def relG_def
            adjacent_def restrict_map_def)
      then show ?thesis by auto
    next
      assume "src SG e = Some v \<and> va = v"
      hence "(v, vb) \<in> inh SG \<and> s vb = Some v'"
        using \<open>tgt SG e = Some vb \<and> s vb = Some v'\<close>
        \<open>e \<in> EsI SG\<close> assms(1) EsI_sub_Es[of SG]
        by (auto simp add: inh_def inhG_def restrict_def relG_def
            adjacent_def restrict_map_def)
      then show ?thesis by auto
    qed
  next
    assume "tgt SG e = Some v' \<and> vb = v'"
    from \<open>src SG e = Some va \<and> s va = Some v \<or> src SG e = Some v \<and> va = v\<close>
    show ?thesis 
    proof
      assume "src SG e = Some va \<and> s va = Some v"
      hence "(va, vb) \<in> inh SG \<and> s va = Some v \<and> vb = v'"
        using \<open>tgt SG e = Some v' \<and> vb = v'\<close>
        \<open>e \<in> EsI SG\<close> assms(1) EsI_sub_Es[of SG]
        by (auto simp add: inh_def inhG_def restrict_def relG_def
            adjacent_def restrict_map_def)
      then show ?thesis by auto
  next
    assume "src SG e = Some v \<and> va = v"
    hence "(va, vb) \<in> inh SG \<and> va = v \<and> vb = v'"
        using \<open>tgt SG e = Some v' \<and> vb = v'\<close>
        \<open>e \<in> EsI SG\<close> assms(1) EsI_sub_Es[of SG]
        by (auto simp add: inh_def inhG_def restrict_def relG_def
            adjacent_def restrict_map_def)
      then show ?thesis by auto
    qed
  qed
qed

(*
lemma if_in_inhst_subsume_SG:
  assumes "wf_sg SG" 
    and "fpartial_on s (NsP SG) (Ns SG - NsO SG)" 
    and "(v, v') \<in> inhst (SG \<odot>\<^sup>S\<^sup>G s)" 
  shows "\<exists> va vb. (va, vb) \<in> inhst SG \<and> (s va = Some v \<or> va = v) \<and> (s vb = Some v' \<or> vb = v')"
proof -
  have h: "fpartial_on s (Ns (gr_sg SG)) (Ns (gr_sg SG))"
    using assms(1) assms(2) NsP_sub_Ns[of SG]
    by (auto simp add: gr_sg_def consG_def fpartial_on_def)
  obtain e where "e \<in> EsI SG 
    \<and> (mtotalise_in s (Ns SG) \<circ>\<^sub>m src SG) e = Some v
    \<and> (mtotalise_in s (Ns SG) \<circ>\<^sub>m tgt SG) e = Some v'"
    using \<open>(v, v') \<in> inhst (SG \<odot>\<^sup>S\<^sup>G s)\<close> assms h 
      EsI_subsumeSG[of SG s]
    by (auto simp add: subsumeSG_def gr_sg_def consSG_def 
        consG_def subsumeG_def inhst_def )

lemma inhst_subsume_of_NsO:
  assumes "wf_sg SG" and "v \<in> NsO SG" 
    and "fpartial_on s (NsP SG) (Ns SG - NsO SG)"
    and "(v, v') \<in> inhst (SG \<odot>\<^sup>S\<^sup>G s)"
  shows "v' = v"
proof -
  have h: "fpartial_on s (Ns (gr_sg SG)) (Ns (gr_sg SG))"
    using assms(1) assms(3) NsP_sub_Ns[of SG]
    by (auto simp add: gr_sg_def consG_def fpartial_on_def)
  obtain va where  "(v, va) \<in> inh (SG \<odot>\<^sup>S\<^sup>G s)  \<and> (va, v') \<in> inhst (SG \<odot>\<^sup>S\<^sup>G s)"
      using \<open>(v, v') \<in> inhst (SG \<odot>\<^sup>S\<^sup>G s)\<close>
      sledgehammer
  show ?thesis
  
  proof (rule ccontr)
    assume "v' \<noteq> v"
    then obtain va where  "(v, va) \<in> inh (SG \<odot>\<^sup>S\<^sup>G s)  \<and> (va, v') \<in> inhst (SG \<odot>\<^sup>S\<^sup>G s)"
      using \<open>(v, v') \<in> inhst (SG \<odot>\<^sup>S\<^sup>G s)\<close>
      by (metis inhst_def converse_rtranclE)
    have "v \<notin> ran s \<and> v \<notin> dom s"
      using assms(2) assms(3) 
      by (auto simp add: fpartial_on_def NsO_def NsP_def NsTy_def)
    then show "False"
    proof (case_tac "va \<in> ran s")
     assume "va \<in> ran s"
     then obtain vb where "s vb = Some va \<and> vb \<in> NsP SG 
        \<and> va \<in> Ns SG \<and> va \<notin> NsO SG" 
       using assms(3)
       by (auto simp add: fpartial_on_def ran_def)
     hence "(v, vb) \<in> inh (SG)"
       using \<open>(v, va) \<in> inh (SG \<odot>\<^sup>S\<^sup>G s)  \<and> (va, v') \<in> inhst (SG \<odot>\<^sup>S\<^sup>G s)\<close>
       using \<open>s vb = Some va \<and> vb \<in> NsP SG 
        \<and> va \<in> Ns SG \<and> va \<notin> NsO SG\<close>
       using assms(3) h
       by (simp add: subsumeSG_def consSG_def inh_def subsumeG_def
           inhG_def relG_def adjacent_def)
   hence "the ((nty (SG \<odot>\<^sup>S\<^sup>G s)) v)  <\<^sub>N\<^sub>T the ((nty (SG \<odot>\<^sup>S\<^sup>G s)) va)"
     using assms(3) nty_subsumeSG_s_ok[of s SG] 
       assms(1) inhOk_def[of SG] 
        \<open>(v, va) \<in> inh (SG \<odot>\<^sup>S\<^sup>G s)  \<and> (va, v') \<in> inhst (SG \<odot>\<^sup>S\<^sup>G s)\<close> 
     sledgehammer
     by auto
   show "False"
     using assms(1) assms(2) wf_sg_inhOk[of SG] 
       \<open>(v, va) \<in> inh (SG \<odot>\<^sup>S\<^sup>G s)  \<and> (va, v') \<in> inhst (SG \<odot>\<^sup>S\<^sup>G s)\<close> 
     by (auto simp add: inh_def inhOk_def relG_def adjacent_def )
  qed

lemma srcst_img_inv_NsO:
  assumes "wf_sg SG" and "fpartial_on s (NsP SG) (Ns SG - NsO (SG))"
  shows "(srcst (SG \<odot>\<^sup>S\<^sup>G s))\<inverse> `` NsO (SG \<odot>\<^sup>S\<^sup>G s) = (srcst SG)\<inverse> `` (NsO SG)"
proof
  show "(srcst (SG \<odot>\<^sup>S\<^sup>G s))\<inverse> `` NsO (SG \<odot>\<^sup>S\<^sup>G s) \<subseteq> (srcst SG)\<inverse> `` NsO SG"
  proof
    fix e
    assume "e \<in> (srcst (SG \<odot>\<^sup>S\<^sup>G s))\<inverse> `` NsO (SG \<odot>\<^sup>S\<^sup>G s)"
    then obtain v where "(e, v) \<in> srcst (SG \<odot>\<^sup>S\<^sup>G s) \<and> v \<in> NsO (SG \<odot>\<^sup>S\<^sup>G s)"
      by auto
    hence "(e, v) \<in> srcr (SG \<odot>\<^sup>S\<^sup>G s) \<and> (v, v) \<in> inhst (SG \<odot>\<^sup>S\<^sup>G s)"
      using inhst_NsO[of "SG \<odot>\<^sup>S\<^sup>G s" v] 
      by (simp add: srcst_def relcomp_unfold)
    hence "e \<in> EsW (SG)" 
    hence "(e, v) \<in> srcst (SG)"
      by (simp add: srcst_def EsC_subsumeSG dres_def relcomp_unfold)
*)

(*lemma optsVoluntary_subsumeSG:
  assumes "wf_sg SG" and "fpartial_on s (NsP SG) (Ns SG)"
    and "(ran s) \<inter> NsO (SG) = {}"
  shows "optsVoluntary (SG \<odot>\<^sup>S\<^sup>G s)"
    using assms
    by (simp add: optsVoluntary_def ety_subsumeSG EsI_subsumeSG
        NsO_subsumeSG esIncidentst_def)*)

(*
lemma wf_subsumeSG:
  assumes "wf_sg SG" and "fpartial_on s (NsP SG) (Ns SG)"
  shows "wf_sg (SG \<odot>\<^sup>S\<^sup>G s)"
proof (simp add: wf_sg_def)
  apply_end (rule conjI)
  show "wf_g (SG \<odot>\<^sup>S\<^sup>G s)"
  using assms wf_sg_wf_g[of SG]
  by (simp add: wf_g_SG_eq_gr_sg gr_sg_subsumeSG_eq
      wf_subsumeG)
next
  apply_end (rule conjI)
  show "ftotal_on (nty (SG \<odot>\<^sup>S\<^sup>G s)) (Ns (SG \<odot>\<^sup>S\<^sup>G s)) SGNT_set"
    using assms wf_sg_ftotal_on_nty[of SG] 
      dom_mdsub_if[of "nty SG" "Ns SG" s] 
      ran_mdsub_sub[of "dom s - ran s" "nty SG"]  
      NsP_sub_Ns[of SG]
    by (auto simp add: subsumeSG_def ftotal_on_def consSG_def
        subsumeG_def Ns_gr_sg_eq fpartial_on_def )
next
  apply_end (rule conjI)
  show "ftotal_on (ety (SG \<odot>\<^sup>S\<^sup>G s)) (Es (SG \<odot>\<^sup>S\<^sup>G s)) SGET_set"
    using assms wf_sg_ftotal_on_ety[of SG]
    NsP_sub_Ns[of SG]
    by (auto simp add: subsumeSG_def ftotal_on_def consSG_def
        subsumeG_def Ns_gr_sg_eq Es_gr_sg_eq consG_def) 
next
  apply_end (rule conjI)
  show "ftotal_on (srcma (SG \<odot>\<^sup>S\<^sup>G s)) (EsC (SG \<odot>\<^sup>S\<^sup>G s)) MultC_set"
    using assms wf_sg_ftotal_on_srcma[of SG]
    by (simp add: srcma_subsumeSG EsC_subsumeSG)
next
  apply_end (rule conjI)
  show "ftotal_on (tgtm (SG \<odot>\<^sup>S\<^sup>G s)) (EsC (SG \<odot>\<^sup>S\<^sup>G s)) MultC_set"
  using assms wf_sg_ftotal_on_tgtm[of SG]
  by (simp add: tgtm_subsumeSG EsC_subsumeSG)
next
  apply_end (rule conjI)
  show "dom (db (SG \<odot>\<^sup>S\<^sup>G s)) = EsD (SG \<odot>\<^sup>S\<^sup>G s)"
    using assms wf_sg_dom_db
    by (simp add: db_subsumeSG EsD_subsumeSG)
next
  apply_end (rule conjI)
  show "multsOk (SG \<odot>\<^sup>S\<^sup>G s)"
    using assms 
    by (simp add: multsOk_def EsC_subsumeSG ety_subsumeSG
        srcma_subsumeSG tgtm_subsumeSG wf_sg_def)
next
  apply_end (rule conjI)
  show "optsVoluntary (SG \<odot>\<^sup>S\<^sup>G s)"
    using assms
    by (simp add: optsVoluntary_def ety_subsumeSG EsI_subsumeSG
        NsO_subsumeSG)


lemma wf_subsumeSG_2:
  assumes "wf_sg SG" and "\<not>fpartial_on s (NsP SG) (Ns SG)"
  shows "wf_sg (SG \<odot>\<^sup>S\<^sup>G s)"
  using assms wf_sg_wf_g[of SG] subsumeSG_not_from_NsP[of s SG] 
      by simp*)

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
         EsC_sub_Es[of SG1] EsC_sub_Es[of SG2] 
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
      EsC_sub_Es[of SG1] EsC_sub_Es[of SG2]
      disjGs_imp_disjEsGs[of SG1 SG2]
    by (auto simp add: disjEsGs_def ftotal_on_def)
next
  show "db SG1 ++ db SG2 = db SG2 ++ db SG1"
    using assms wf_sg_dom_db[of SG1] wf_sg_dom_db[of SG2]
      EsD_sub_Es[of SG1] EsD_sub_Es[of SG2]
      map_add_comm[of "db SG1" "db SG2"] 
      disjGs_imp_disjEsGs[of SG1 SG2]
    by (auto simp add: disjEsGs_def)(force)
qed

lemma Ns_cupSG[simp]: "Ns (SG1 USG SG2) = (Ns SG1) \<union> (Ns SG2)"
  by (simp add: cupSG_def)

lemma src_cupSG[simp]: "src (SG1 USG SG2) = src SG1 ++ src SG2"
  by (simp add: cupSG_def)

lemma tgt_cupSG[simp]: "tgt (SG1 USG SG2) = tgt SG1 ++ tgt SG2"
  by (simp add: cupSG_def)

lemma ety_cupSG[simp]: "ety (SG1 USG SG2) = ety SG1 ++ ety SG2"
  by (simp add: cupSG_def)

lemma nty_cupSG[simp]: "nty (SG1 USG SG2) = nty SG1 ++ nty SG2"
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
      by (simp add: cupSG_def restrict_def rNs_dist_UG rNs_def)
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

lemma NsP_USG: 
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "NsP (SG1 USG SG2) = NsP SG1 \<union> NsP SG2"
  using assms by (simp add: NsP_def NsTy_USG)

lemma NsO_USG: 
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "NsO (SG1 USG SG2) = NsO SG1 \<union> NsO SG2"
  using assms by (simp add: NsO_def NsTy_USG)

lemma NsV_USG: 
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "NsV (SG1 USG SG2) = NsV SG1 \<union> NsV SG2"
  using assms by (simp add: NsV_def NsTy_USG)

lemma dom_srcr_eq_Es:
  assumes "wf_sg SG" 
  shows "Domain (srcr SG) = Es SG"
  using assms wf_sg_wf_g[of SG] dom_src_G[of SG] dom_tgt_G[of SG]
  by (auto simp add: srcr_def pfunToRel_def dres_def EsW_sub_Es)

lemma dom_tgtr_eq_Es:
  assumes "wf_sg SG" 
  shows "Domain (tgtr SG) = Es SG"
  using assms wf_sg_wf_g[of SG] dom_src_G[of SG] dom_tgt_G[of SG]
  by (auto simp add: tgtr_def pfunToRel_def dres_def EsW_sub_Es)

lemma ran_srcr_sub_Ns:
  assumes "wf_sg SG" 
  shows "Range (srcr SG) \<subseteq> Ns SG"
  using assms wf_sg_wf_g[of SG] ran_src_G[of SG] ran_tgt_G[of SG]
  by (auto simp add: srcr_def pfunToRel_def dres_def EsW_sub_Es 
      ran_def Range_iff)

lemma ran_tgtr_sub_Ns:
  assumes "wf_sg SG" 
  shows "Range (tgtr SG) \<subseteq> Ns SG"
  using assms wf_sg_wf_g[of SG] ran_src_G[of SG] ran_tgt_G[of SG]
  by (auto simp add: tgtr_def pfunToRel_def dres_def EsW_sub_Es 
      ran_def Range_iff)

lemma esIncidentst_disjoint_vs:
  assumes "wf_sg SG" and "vs \<inter> Ns SG = {}"
  shows "SG \<circ>\<rightarrow>\<circ>\<^sup>* vs = {}"
proof (rule ccontr)
  assume "SG \<circ>\<rightarrow>\<circ>\<^sup>* vs \<noteq> {}"
  hence "\<exists> e v. v \<in> vs \<and> ((e, v) \<in> (srcst SG) \<or> (e, v) \<in> (tgtst SG))" 
    by (auto simp add: esIncidentst_def)
  then show "False"
  proof (clarsimp)
    fix e v
    assume h1:"v \<in> vs" 
    assume "(e, v) \<in> (srcst SG) \<or> (e, v) \<in> (tgtst SG)"
    then show "False"
    proof
      assume "(e, v) \<in> srcst SG"
      hence "\<exists> v'. (e, v') \<in> srcr SG \<and> (v, v') \<in> (inhst SG)" 
        by (auto simp add: srcst_def dres_def relcomp_unfold)
      then show "False"
      proof
        fix v' 
        assume h:"(e, v') \<in> srcr SG \<and> (v, v') \<in> inhst SG"
        then show "False"
        proof (case_tac "v = v'")
          assume "v = v'"
          hence "v \<in> Ns SG"
            using h ran_srcr_sub_Ns[of SG] assms(1)
            by (auto simp add: Range_iff)
          then show "False"
            using assms h1 by auto
        next
          assume h': "v \<noteq> v'"
          have "(v, v') \<in> inhst SG" using h by auto
          hence "v \<in> Domain (inh SG)" 
            using h' 
            by (simp add: inhst_def in_rtrcl_in_Domain_if_neq)
          then show "False"
            using assms Domain_inh h1 by auto
        qed
      qed
    next
      assume "(e, v) \<in> tgtst SG"
      hence "\<exists> v'. (e, v') \<in> tgtr SG \<and> (v, v') \<in> (inhst SG)" 
        by (auto simp add: tgtst_def dres_def relcomp_unfold)
      then show "False"
      proof
        fix v' 
        assume h:"(e, v') \<in> tgtr SG \<and> (v, v') \<in> inhst SG"
        then show "False"
        proof (case_tac "v = v'")
          assume "v = v'"
          hence "v \<in> Ns SG"
            using h ran_tgtr_sub_Ns[of SG] assms(1)
            by (auto simp add: Range_iff)
          then show "False"
            using assms h1 by auto
        next
          assume h': "v \<noteq> v'"
          have "(v, v') \<in> inhst SG" using h by auto
          hence "v \<in> Domain (inh SG)" 
            using h' 
            by (simp add: inhst_def in_rtrcl_in_Domain_if_neq)
          then show "False"
            using assms Domain_inh h1 by auto
        qed
      qed
    qed
  qed
qed

lemma srcr_USG: 
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "srcr (SG1 USG SG2) = srcr SG1 \<union> srcr SG2"  
proof -
  have h1: "EsW SG2 \<inter> Domain (pfunToRel (tgt SG1)) = {}"
    using assms EsW_sub_Es[of SG2] wf_sg_wf_g[of SG1]
      wf_sg_wf_g[of SG2]
      disjGs_imp_disjEsGs[of SG1 SG2] 
      dom_tgt_G[of SG1] dom_tgt_G[of SG2]
    by (auto simp add: disjEsGs_def pfunToRel_iff)(force)
  have h2: "EsW SG1 \<inter> Domain (pfunToRel (tgt SG2)) = {}"
    using assms EsW_sub_Es[of SG1] wf_sg_wf_g[of SG1]
      wf_sg_wf_g[of SG2]
      disjGs_imp_disjEsGs[of SG1 SG2] 
      dom_tgt_G[of SG1] dom_tgt_G[of SG2]
    by (auto simp add: disjEsGs_def pfunToRel_iff)(force)
  show ?thesis
  using assms disjGs_imp_disjEsGs[of SG1 SG2] 
    wf_sg_wf_g[of SG1] wf_sg_wf_g[of SG2]
    dom_src_G[of SG1] dom_src_G[of SG2]
    dom_tgt_G[of SG1] dom_tgt_G[of SG2]
    EsW_sub_Es[of SG1] EsW_sub_Es[of SG2]
  by (auto simp add: srcr_def pfunToRel_map_add disjEsGs_def h1 h2
      dres_union_r EsW_USG dres_union_set dres_not_in_dom)
qed

lemma tgtr_USG: 
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "tgtr (SG1 USG SG2) = tgtr SG1 \<union> tgtr SG2"  
proof -
  have h1: "EsW SG2 \<inter> Domain (pfunToRel (src SG1)) = {}"
    using assms EsW_sub_Es[of SG2] wf_sg_wf_g[of SG1]
      wf_sg_wf_g[of SG2]
      disjGs_imp_disjEsGs[of SG1 SG2] 
      dom_src_G[of SG1] dom_src_G[of SG2]
    by (auto simp add: disjEsGs_def pfunToRel_iff)(force)
  have h2: "EsW SG1 \<inter> Domain (pfunToRel (src SG2)) = {}"
    using assms EsW_sub_Es[of SG1] wf_sg_wf_g[of SG1]
      wf_sg_wf_g[of SG2]
      disjGs_imp_disjEsGs[of SG1 SG2] 
      dom_src_G[of SG1] dom_src_G[of SG2]
    by (auto simp add: disjEsGs_def pfunToRel_iff)(force)
  show ?thesis
  using assms disjGs_imp_disjEsGs[of SG1 SG2] 
    wf_sg_wf_g[of SG1] wf_sg_wf_g[of SG2]
    dom_src_G[of SG1] dom_src_G[of SG2]
    dom_tgt_G[of SG1] dom_tgt_G[of SG2]
    EsW_sub_Es[of SG1] EsW_sub_Es[of SG2]
  by (auto simp add: tgtr_def pfunToRel_map_add disjEsGs_def h1 h2
      dres_union_r EsW_USG dres_union_set dres_not_in_dom)
qed

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
  show "rNs SG1 (EsI SG1) \<inter> rNs SG2 (EsI SG2) = {}"
    using assms wf_sg_wf_g[of SG1] wf_sg_wf_g[of SG2]
      ran_src_G[of SG1] ran_src_G[of SG2] 
      ran_tgt_G[of SG1] ran_tgt_G[of SG2] 
      ran_restrict_sub[of "src SG1" "EsI SG1"]
      ran_restrict_sub[of "src SG2" "EsI SG2"]
      ran_restrict_sub[of "tgt SG1" "EsI SG1"]
      ran_restrict_sub[of "tgt SG2" "EsI SG2"]
    unfolding rNs_def disjGs_def by force
next
  apply_end(rule conjI)
  show "rNs SG1 (EsI SG1) \<inter> (Es SG1 \<inter> EsI SG1) = {}"
    using assms(1) assms(3) disj_V_E wf_sg_wf_g[of SG1]
      ran_restrict_sub[of "src SG1" "EsI SG1"]
      ran_restrict_sub[of "tgt SG1" "EsI SG1"]
    by (auto simp add: rNs_def wf_g_def disjGs_def 
        ftotal_on_def)
next
  apply_end(rule conjI)
  show "rNs SG1 (EsI SG1) \<inter> (Es SG2 \<inter> EsI SG2) = {}"
    using assms(1) assms(3) disj_V_E wf_sg_wf_g[of SG1]
      ran_restrict_sub[of "src SG1" "EsI SG1"]
      ran_restrict_sub[of "tgt SG1" "EsI SG1"]
    by (auto simp add: rNs_def wf_g_def disjGs_def 
        ftotal_on_def)
next
  apply_end(rule conjI)
  show "rNs SG2 (EsI SG2) \<inter> (Es SG1 \<inter> EsI SG1) = {}"
    using assms(2) assms(3) disj_V_E wf_sg_wf_g[of SG2]
      ran_restrict_sub[of "src SG2" "EsI SG2"]
      ran_restrict_sub[of "tgt SG2" "EsI SG2"]
    by (auto simp add: rNs_def wf_g_def disjGs_def 
        ftotal_on_def)
next
  apply_end(rule conjI)
  show "rNs SG2 (EsI SG2) \<inter> (Es SG2 \<inter> EsI SG2) = {}"
    using assms(2) assms(3) disj_V_E wf_sg_wf_g[of SG2]
      ran_restrict_sub[of "src SG2" "EsI SG2"]
      ran_restrict_sub[of "tgt SG2" "EsI SG2"]
    by (auto simp add: rNs_def wf_g_def disjGs_def 
        ftotal_on_def)
next
  show "Es SG1 \<inter> EsI SG1 \<inter> (Es SG2 \<inter> EsI SG2) = {}"
    using assms EsI_sub_Es[of SG1] EsI_sub_Es[of SG2]
    disjGs_imp_disjEsGs[of SG1 SG2]
    by (auto simp add:  disjEsGs_def)
qed


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

lemma inh_disj_SGs_disj_fields: 
  assumes "wf_sg SG1" and "wf_sg SG2" and h3: "disjGs SG1 SG2"
  shows "Field (inh SG1) \<inter> Field (inh SG2) = {}"
  using assms disjGs_inhG[of SG1 SG2] wf_sg_wf_g[of SG1]
        wf_sg_wf_g[of SG2] wf_g_inhG[of SG1] wf_g_inhG[of SG2] 
        by (simp add: inh_def relG_disj_Gs)

lemma restrict_SG:
  shows "SG \<bowtie>\<^sub>E\<^sub>S es = gr_sg SG \<bowtie>\<^sub>E\<^sub>S es"
proof (simp add: restrict_def)
  apply_end (rule conjI)
  show "rNs SG es = rNs (gr_sg SG) es"
    by (simp add: rNs_def gr_sg_def consG_def)
next
  apply_end (rule conjI)
  show "Es SG \<inter> es = Es (gr_sg SG) \<inter> es"
    by (simp add: gr_sg_def consG_def)
next
  apply_end (rule conjI)
  show "src SG |` es = src (gr_sg SG) |` es"
    by (simp add: gr_sg_def consG_def)
next
  show "tgt SG |` es = tgt (gr_sg SG) |` es"
    by (simp add: gr_sg_def consG_def)
qed

(*lemma fpartial_on_SG_fpartial_rns_EsI:
  assumes "wf_sg SG" 
    and "fpartial_on s (NsP SG) (Ns SG - NsO SG)"
  shows "fpartial_on s (rNs (gr_sg SG) (EsI SG))
      (rNs (gr_sg SG) (EsI SG))"

lemma inhG_subsume_sg:
  assumes "wf_sg SG" 
    and "fpartial_on s (NsP SG) (Ns SG - NsO SG)"
  shows "inhG (SG \<odot>\<^sup>S\<^sup>G s) = (inhG SG) \<odot> s"
  using assms(2) EsI_subsumeSG[of SG s]
  by (simp add: inh_def inhG_def restrict_SG 
      gr_sg_subsumeSG_eq )

lemma inh_subsume_sg:
  assumes "wf_sg SG" 
    and "fpartial_on s (NsP SG) (Ns SG - NsO SG)"
  shows "inh (SG \<odot>\<^sup>S\<^sup>G s) = ((inhG SG) \<odot> s)\<^sup>\<Leftrightarrow>"
  using assms(2) EsI_subsumeSG[of SG s]
  assms wf_sg_wf_g[of SG] wf_g_SG_eq_gr_sg[of SG]
  subsume_restrict_eq[of "gr_sg SG" s "EsI SG"]
  by (simp add: inh_def inhG_def restrict_SG 
      gr_sg_subsumeSG_eq )
proof
  show "inh (SG \<odot>\<^sup>S\<^sup>G s) \<subseteq> (inhG SG \<odot> s)\<^sup>\<Leftrightarrow>"
  proof (rule subrelI)
    fix x y
    assume "(x, y) \<in> inh (SG \<odot>\<^sup>S\<^sup>G s)"
    using assms(2)
    by (simp add: subsumeSG_def inh_def)
lemma in_Domain_inh_subsume_in_SG:
  assumes "wf_sg SG" and "v \<notin> dom s"
  shows "v \<in> Domain (inh (SG \<odot>\<^sup>S\<^sup>G s)) \<longrightarrow> v \<in> Domain (inh SG)"
proof
  assume "v \<in> Domain (inh (SG \<odot>\<^sup>S\<^sup>G s))"
  then obtain v' where "(v, v') \<in> inh (SG \<odot>\<^sup>S\<^sup>G s)"
    by auto
  hence "(v, v') \<in> inh SG"
    by (simp add: subsumeSG_def inh_def)*)

lemma inhst_USG: 
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "inhst (SG1 USG SG2) = inhst SG1 \<union> inhst SG2"
  using assms
      by (simp add: inhst_def inh_USG 
          inh_disj_SGs_disj_fields rtrancl_disj_dist_Un)


lemma srcst_USG: 
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "srcst (SG1 USG SG2) = srcst SG1 \<union> srcst SG2"
proof
  show "srcst (SG1 USG SG2) \<subseteq> srcst SG1 \<union> srcst SG2"
  proof (rule subrelI)
    fix e v 
    assume "(e, v) \<in> srcst (SG1 USG SG2)"
    hence "\<exists> v'. (e, v') \<in>  EsC (SG1 USG SG2) \<lhd>srcr (SG1 USG SG2) 
      \<and> (v, v') \<in> inhst (SG1 USG SG2)" 
      using assms by (auto simp add: srcst_def)
    then show "(e, v) \<in> srcst SG1 \<union> srcst SG2"
    proof 
      fix v'
      assume h: "(e, v') \<in> EsC (SG1 USG SG2) \<lhd> srcr (SG1 USG SG2) \<and>
         (v, v') \<in> inhst (SG1 USG SG2)"
      hence "e \<in> EsC SG1 \<or> e \<in> EsC SG2"
        using assms by (simp add: EsC_USG dres_def)
      then show "(e, v) \<in> srcst SG1 \<union> srcst SG2"
      proof
        assume "e \<in> EsC SG1"
        hence "e \<in> Es SG1" using assms EsC_sub_Es[of SG1] by auto
        hence "(e, v') \<in> srcr SG1"
          using assms h EsC_sub_Es[of SG1] 
          disjGs_imp_disjEsGs[of SG1 SG2]
          dom_srcr_eq_Es[of SG1] dom_srcr_eq_Es[of SG2]
          by (auto simp add: srcr_USG EsC_USG dres_def disjEsGs_def)
        hence "v' \<in> Ns SG1" 
          using assms ran_srcr_sub_Ns[of SG1] by (auto)
        have "(v, v') \<in> inhst SG1"
        proof (rule ccontr)
          assume "(v, v') \<notin>  inhst SG1"
          then show "False"
          proof (case_tac "v = v'")
            assume "v = v'"
            then show "False" 
              using \<open>(v, v') \<notin>  inhst SG1\<close>
            by (auto simp add: inhst_def)
          next
            assume "v \<noteq> v'"
            hence "(v, v') \<in> inhst SG2"
              using \<open>(v, v') \<notin>  inhst SG1\<close> h assms
              by (auto simp add: inhst_USG EsC_USG srcr_USG )
            hence "v' \<in> Range(inh SG2)" 
              using \<open>v \<noteq> v'\<close>
              by (simp add: in_trancl_in_Range inhst_def 
                  rtrancl_eq_or_trancl)
              then show "False"
                using assms \<open>v' \<in> Ns SG1\<close> Range_inh[of SG2]
                by (auto simp add: inhst_def disjGs_def)
          qed
        qed 
        hence "(e, v) \<in> srcst SG1"
          using \<open>e \<in> EsC SG1\<close> \<open>(e, v') \<in> srcr SG1\<close> 
          by (auto simp add: srcst_def dres_def)
        then show "(e, v) \<in> srcst SG1 \<union> srcst SG2" 
           by simp
      next
        assume "e \<in> EsC SG2"
        hence "e \<in> Es SG2" using assms EsC_sub_Es[of SG2] by auto
        hence "(e, v') \<in> srcr SG2"
          using assms h EsC_sub_Es[of SG2] 
          disjGs_imp_disjEsGs[of SG1 SG2]
          dom_srcr_eq_Es[of SG1] dom_srcr_eq_Es[of SG2]
          by (auto simp add: srcr_USG EsC_USG dres_def disjEsGs_def)
        hence "v' \<in> Ns SG2" 
          using assms ran_srcr_sub_Ns[of SG2] by (auto)
        have "(v, v') \<in> inhst SG2"
        proof (rule ccontr)
          assume "(v, v') \<notin>  inhst SG2"
          then show "False"
          proof (case_tac "v = v'")
            assume "v = v'"
            then show "False" 
              using \<open>(v, v') \<notin>  inhst SG2\<close>
            by (auto simp add: inhst_def)
          next
            assume "v \<noteq> v'"
            hence "(v, v') \<in> inhst SG1"
              using \<open>(v, v') \<notin>  inhst SG2\<close> h assms
              by (auto simp add: inhst_USG EsC_USG srcr_USG )
            hence "v' \<in> Range(inh SG1)" 
              using \<open>v \<noteq> v'\<close>
              by (simp add: in_trancl_in_Range inhst_def 
                  rtrancl_eq_or_trancl)
            then show "False"
              using assms \<open>v' \<in> Ns SG2\<close> Range_inh[of SG1]
              by (auto simp add: inhst_def disjGs_def)
          qed
        qed 
        hence "(e, v) \<in> srcst SG2"
          using \<open>e \<in> EsC SG2\<close> \<open>(e, v') \<in> srcr SG2\<close> 
          by (auto simp add: srcst_def dres_def)
        then show "(e, v) \<in> srcst SG1 \<union> srcst SG2" 
          by simp
      qed
    qed
  qed
next
  show "srcst SG1 \<union> srcst SG2 \<subseteq> srcst (SG1 USG SG2)"
  proof (rule subrelI)
    fix e v
    assume "(e, v) \<in> srcst SG1 \<union> srcst SG2"
    then show "(e, v) \<in> srcst (SG1 USG SG2)"
    proof
      assume "(e, v) \<in> srcst SG1"
      hence "\<exists> v'. (e, v') \<in> EsC SG1 \<lhd> srcr SG1 \<and>
         (v, v') \<in> inhst SG1"
        by (simp add: srcst_def relcomp_unfold)
      then show "(e, v) \<in> srcst (SG1 USG SG2)"
      proof
        fix v'
        assume h: "(e, v') \<in> EsC SG1 \<lhd> srcr SG1 \<and> (v, v') \<in> inhst SG1"
        hence "e \<in> EsC SG1" by (simp add: dres_def)
        hence "e \<in> EsC SG1 \<union> EsC SG2" by auto
        hence "e \<in> EsC (SG1 USG SG2)" 
          using assms by (simp add: EsC_USG)
        from h have "(e, v') \<in> srcr SG1" 
          by (simp add: dres_def)
        hence "(e, v') \<in> srcr (SG1 USG SG2)"
          using assms by (simp add: srcr_USG)
        from h have "(v, v') \<in> inhst SG1" by auto
        hence "(v, v') \<in> inhst (SG1 USG SG2)"
          using assms by (simp add: inhst_USG)
        then show "(e, v) \<in> srcst (SG1 USG SG2)"
          using \<open>e \<in> EsC (SG1 USG SG2)\<close> 
            \<open>(e, v') \<in> srcr (SG1 USG SG2)\<close>
          using assms 
          by (auto simp add: srcst_def dres_def)
      qed
    next
      assume "(e, v) \<in> srcst SG2"
      hence "\<exists> v'. (e, v') \<in> EsC SG2 \<lhd> srcr SG2 \<and>
         (v, v') \<in> inhst SG2"
        by (simp add: srcst_def relcomp_unfold)
      then show "(e, v) \<in> srcst (SG1 USG SG2)"
      proof
        fix v'
        assume h: "(e, v') \<in> EsC SG2 \<lhd> srcr SG2 \<and> (v, v') \<in> inhst SG2"
        hence "e \<in> EsC SG2" by (simp add: dres_def)
        hence "e \<in> EsC SG1 \<union> EsC SG2" by auto
        hence "e \<in> EsC (SG1 USG SG2)" 
          using assms by (simp add: EsC_USG)
        from h have "(e, v') \<in> srcr SG2" 
          by (simp add: dres_def)
        hence "(e, v') \<in> srcr (SG1 USG SG2)"
          using assms by (simp add: srcr_USG)
        from h have "(v, v') \<in> inhst SG2" by auto
        hence "(v, v') \<in> inhst (SG1 USG SG2)"
          using assms by (simp add: inhst_USG)
        then show "(e, v) \<in> srcst (SG1 USG SG2)"
          using \<open>e \<in> EsC (SG1 USG SG2)\<close> 
            \<open>(e, v') \<in> srcr (SG1 USG SG2)\<close>
          using assms 
          by (auto simp add: srcst_def dres_def)
      qed
    qed
  qed
qed

lemma tgtst_USG: 
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "tgtst (SG1 USG SG2) = tgtst SG1 \<union> tgtst SG2"
proof
  show "tgtst (SG1 USG SG2) \<subseteq> tgtst SG1 \<union> tgtst SG2"
  proof (rule subrelI)
    fix e v 
    assume "(e, v) \<in> tgtst (SG1 USG SG2)"
    hence "\<exists> v'. (e, v') \<in>  EsC (SG1 USG SG2) \<lhd>tgtr (SG1 USG SG2) 
      \<and> (v, v') \<in> inhst (SG1 USG SG2)" 
      using assms by (auto simp add: tgtst_def)
    then show "(e, v) \<in> tgtst SG1 \<union> tgtst SG2"
    proof 
      fix v'
      assume h: "(e, v') \<in> EsC (SG1 USG SG2) \<lhd> tgtr (SG1 USG SG2) \<and>
         (v, v') \<in> inhst (SG1 USG SG2)"
      hence "e \<in> EsC SG1 \<or> e \<in> EsC SG2"
        using assms by (simp add: EsC_USG dres_def)
      then show "(e, v) \<in> tgtst SG1 \<union> tgtst SG2"
      proof
        assume "e \<in> EsC SG1"
        hence "e \<in> Es SG1" using assms EsC_sub_Es[of SG1] by auto
        hence "(e, v') \<in> tgtr SG1"
          using assms h EsC_sub_Es[of SG1] 
          disjGs_imp_disjEsGs[of SG1 SG2]
          dom_tgtr_eq_Es[of SG1] dom_tgtr_eq_Es[of SG2]
          by (auto simp add: tgtr_USG EsC_USG dres_def disjEsGs_def)
        hence "v' \<in> Ns SG1" 
          using assms ran_tgtr_sub_Ns[of SG1] by (auto)
        have "(v, v') \<in> inhst SG1"
        proof (rule ccontr)
          assume "(v, v') \<notin>  inhst SG1"
          then show "False"
          proof (case_tac "v = v'")
            assume "v = v'"
            then show "False" 
              using \<open>(v, v') \<notin>  inhst SG1\<close>
            by (auto simp add: inhst_def)
          next
            assume "v \<noteq> v'"
            hence "(v, v') \<in> inhst SG2"
              using \<open>(v, v') \<notin>  inhst SG1\<close> h assms
              by (auto simp add: inhst_USG EsC_USG srcr_USG )
            hence "v' \<in> Range(inh SG2)" 
              using \<open>v \<noteq> v'\<close>
              by (simp add: in_trancl_in_Range inhst_def 
                  rtrancl_eq_or_trancl)
              then show "False"
                using assms \<open>v' \<in> Ns SG1\<close> Range_inh[of SG2]
                by (auto simp add: inhst_def disjGs_def)
          qed
        qed 
        hence "(e, v) \<in> tgtst SG1"
          using \<open>e \<in> EsC SG1\<close> \<open>(e, v') \<in> tgtr SG1\<close> 
          by (auto simp add: tgtst_def dres_def)
        then show "(e, v) \<in> tgtst SG1 \<union> tgtst SG2" 
           by simp
      next
        assume "e \<in> EsC SG2"
        hence "e \<in> Es SG2" using assms EsC_sub_Es[of SG2] by auto
        hence "(e, v') \<in> tgtr SG2"
          using assms h EsC_sub_Es[of SG2] 
          disjGs_imp_disjEsGs[of SG1 SG2]
          dom_tgtr_eq_Es[of SG1] dom_tgtr_eq_Es[of SG2]
          by (auto simp add: tgtr_USG EsC_USG dres_def disjEsGs_def)
        hence "v' \<in> Ns SG2" 
          using assms ran_tgtr_sub_Ns[of SG2] by (auto)
        have "(v, v') \<in> inhst SG2"
        proof (rule ccontr)
          assume "(v, v') \<notin>  inhst SG2"
          then show "False"
          proof (case_tac "v = v'")
            assume "v = v'"
            then show "False" 
              using \<open>(v, v') \<notin>  inhst SG2\<close>
            by (auto simp add: inhst_def)
          next
            assume "v \<noteq> v'"
            hence "(v, v') \<in> inhst SG1"
              using \<open>(v, v') \<notin>  inhst SG2\<close> h assms
              by (auto simp add: inhst_USG EsC_USG srcr_USG )
            hence "v' \<in> Range(inh SG1)" 
              using \<open>v \<noteq> v'\<close>
              by (simp add: in_trancl_in_Range inhst_def 
                  rtrancl_eq_or_trancl)
            then show "False"
              using assms \<open>v' \<in> Ns SG2\<close> Range_inh[of SG1]
              by (auto simp add: inhst_def disjGs_def)
          qed
        qed 
        hence "(e, v) \<in> tgtst SG2"
          using \<open>e \<in> EsC SG2\<close> \<open>(e, v') \<in> tgtr SG2\<close> 
          by (auto simp add: tgtst_def dres_def)
        then show "(e, v) \<in> tgtst SG1 \<union> tgtst SG2" 
          by simp
      qed
    qed
  qed
next
  show "tgtst SG1 \<union> tgtst SG2 \<subseteq> tgtst (SG1 USG SG2)"
  proof (rule subrelI)
    fix e v
    assume "(e, v) \<in> tgtst SG1 \<union> tgtst SG2"
    then show "(e, v) \<in> tgtst (SG1 USG SG2)"
    proof
      assume "(e, v) \<in> tgtst SG1"
      hence "\<exists> v'. (e, v') \<in> EsC SG1 \<lhd> tgtr SG1 \<and>
         (v, v') \<in> inhst SG1"
        by (simp add: tgtst_def relcomp_unfold)
      then show "(e, v) \<in> tgtst (SG1 USG SG2)"
      proof
        fix v'
        assume h: "(e, v') \<in> EsC SG1 \<lhd> tgtr SG1 \<and> (v, v') \<in> inhst SG1"
        hence "e \<in> EsC SG1" by (simp add: dres_def)
        hence "e \<in> EsC SG1 \<union> EsC SG2" by auto
        hence "e \<in> EsC (SG1 USG SG2)" 
          using assms by (simp add: EsC_USG)
        from h have "(e, v') \<in> tgtr SG1" 
          by (simp add: dres_def)
        hence "(e, v') \<in> tgtr (SG1 USG SG2)"
          using assms by (simp add: tgtr_USG)
        from h have "(v, v') \<in> inhst SG1" by auto
        hence "(v, v') \<in> inhst (SG1 USG SG2)"
          using assms by (simp add: inhst_USG)
        then show "(e, v) \<in> tgtst (SG1 USG SG2)"
          using \<open>e \<in> EsC (SG1 USG SG2)\<close> 
            \<open>(e, v') \<in> tgtr (SG1 USG SG2)\<close>
          using assms 
          by (auto simp add: tgtst_def dres_def)
      qed
    next
      assume "(e, v) \<in> tgtst SG2"
      hence "\<exists> v'. (e, v') \<in> EsC SG2 \<lhd> tgtr SG2 \<and>
         (v, v') \<in> inhst SG2"
        by (simp add: tgtst_def relcomp_unfold)
      then show "(e, v) \<in> tgtst (SG1 USG SG2)"
      proof
        fix v'
        assume h: "(e, v') \<in> EsC SG2 \<lhd> tgtr SG2 \<and> (v, v') \<in> inhst SG2"
        hence "e \<in> EsC SG2" by (simp add: dres_def)
        hence "e \<in> EsC SG1 \<union> EsC SG2" by auto
        hence "e \<in> EsC (SG1 USG SG2)" 
          using assms by (simp add: EsC_USG)
        from h have "(e, v') \<in> tgtr SG2" 
          by (simp add: dres_def)
        hence "(e, v') \<in> tgtr (SG1 USG SG2)"
          using assms by (simp add: tgtr_USG)
        from h have "(v, v') \<in> inhst SG2" by auto
        hence "(v, v') \<in> inhst (SG1 USG SG2)"
          using assms by (simp add: inhst_USG)
        then show "(e, v) \<in> tgtst (SG1 USG SG2)"
          using \<open>e \<in> EsC (SG1 USG SG2)\<close> 
            \<open>(e, v') \<in> tgtr (SG1 USG SG2)\<close>
          using assms 
          by (auto simp add: tgtst_def dres_def)
      qed
    qed
  qed
qed
    
lemma EsIncidentst_USG:
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "(SG1 USG SG2) \<circ>\<rightarrow>\<circ>\<^sup>* vs = SG1 \<circ>\<rightarrow>\<circ>\<^sup>* vs \<union> SG2 \<circ>\<rightarrow>\<circ>\<^sup>* vs"
  using assms
  by (auto simp add: esIncidentst_def srcst_USG tgtst_USG)

lemma EsIncidentst_Un_disj_vs:
  assumes "wf_sg SG" and "vs2 \<inter> Ns SG = {}" 
  shows "SG \<circ>\<rightarrow>\<circ>\<^sup>* (vs1 \<union> vs2) = SG \<circ>\<rightarrow>\<circ>\<^sup>* vs1"
  using assms 
  by (simp add: esIncidentst_Un esIncidentst_disjoint_vs)

(*lemma EsIncidentst_subsumeSG:
  assumes "wf_sg SG" and "vs \<inter> NsP SG = {}"
  shows "(SG \<odot>\<^sup>S\<^sup>G s) \<circ>\<rightarrow>\<circ>\<^sup>* vs = SG \<circ>\<rightarrow>\<circ>\<^sup>* vs"
proof
  show "SG \<odot>\<^sup>S\<^sup>G s \<circ>\<rightarrow>\<circ>\<^sup>* vs \<subseteq> SG \<circ>\<rightarrow>\<circ>\<^sup>* vs"
  proof
    fix e 
    assume "e \<in> SG \<odot>\<^sup>S\<^sup>G s \<circ>\<rightarrow>\<circ>\<^sup>* vs"
    then show "e \<in> SG \<circ>\<rightarrow>\<circ>\<^sup>* vs"
    by (simp add: esIncidentst_def)*)
  

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




lemma srcma_disj_SGs:
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "dom(srcma SG1) \<inter> dom(srcma SG2) = {}"
  using assms wf_sg_ftotal_on_srcma[of SG1]
        wf_sg_ftotal_on_srcma[of SG2] 
        disjGs_imp_disjEsGs[of SG1 SG2] EsC_sub_Es[of SG1]
        EsC_sub_Es[of SG2]
      by (simp add: ftotal_on_def disjEsGs_def, force)

lemma srcma_USG:
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "srcma (SG1 USG SG2) = srcma (SG1) ++ srcma (SG2)"
proof
  fix e
  show "srcma (SG1 USG SG2) e = (srcma (SG1) ++ srcma (SG2)) e"
    by (smt (z3) EsTy_USG Un_iff assms disjoint_iff domIff 
        map_add_dom_app_simps(1) map_add_dom_app_simps(3) 
        srcm_cupSG srcma_def srcma_disj_SGs)  
qed

lemma acyclic_SGr_Un_dist: 
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "acyclicGr (inhG (SG1 USG SG2)) = (acyclicGr (inhG SG1) \<and> acyclicGr (inhG SG2))"
  using assms wf_sg_wf_g[of SG1] wf_sg_wf_g[of SG2] 
    disjGs_imp_disjEsGs[of SG1 SG2]
    wf_g_inhG[of SG1] wf_g_inhG[of SG2] 
    disjGs_inhG[of SG1 SG2]
  by (simp add: inhG_USG acyclic_Gr_dist_disj)

lemma multsOk_USG:
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "multsOk (SG1 USG SG2)"
  by (smt (z3) EsC_USG EsC_sub_Es SGr.select_convs(2) Un_iff 
      assms cupSG_def disjGs_imp_disjEsGs es_disj_Ga_Gb 
      ftotal_on_dom map_add_disj_domf map_add_dom_app_simps(1) 
      multsOk_def srcma_USG srcma_disj_SGs subset_Un_eq 
      tgtm_cupSG wf_sg_def)

  
lemma optsVoluntary_USG:
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "optsVoluntary (SG1 USG SG2)"
proof -
  have h1: "optsVoluntary SG1" using assms(1) by (simp add: wf_sg_def)
  have h2: "optsVoluntary SG2" using assms(2) by (simp add: wf_sg_def)
  have h3: "NsO SG2 \<inter> Ns SG1 = {}" using assms NsO_sub_Ns[of SG2]
    by (auto simp add: disjGs_def)
  have h4: "NsO SG1 \<inter> Ns SG2 = {}" using assms NsO_sub_Ns[of SG1]
    by (auto simp add: disjGs_def)
  have h5: "(SG1 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG1 \<union> SG2 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG2 - (EsI SG1 \<union> EsI SG2))
    = (SG1 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG1) - EsI SG1 \<union> (SG2 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG2) - EsI SG2"
    using assms EsI_sub_Es[of SG1] EsI_sub_Es[of SG2]
    disjGs_imp_disjEsGs[of SG1 SG2]
    esIncidentst_SG_Sub_EsSG[of SG1 "NsO SG1"]
    esIncidentst_SG_Sub_EsSG[of SG2 "NsO SG2"]
    by (auto simp add: disjEsGs_def)
  have h6: "dom (ety SG1) \<inter> dom (ety SG2) = {}" 
    using assms disjGs_imp_disjEsGs[of SG1 SG2] 
    wf_sg_ftotal_on_ety[of SG1] wf_sg_ftotal_on_ety[of SG2]
    by (simp add: disjEsGs_def ftotal_on_def)
  have h7: "(SG1 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG1 - EsI SG1) \<inter> Es SG2 = {}"
    using assms(1) assms(3) disjGs_imp_disjEsGs 
      esIncidentst_SG_Sub_EsSG es_disj_Ga_Gb 
    by fastforce
  have h8: "(SG2 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG2 - EsI SG2) \<inter> Es SG1 = {}"
    using assms(2) assms(3) disjGs_imp_disjEsGs 
      esIncidentst_SG_Sub_EsSG es_disj_Ga_Gb 
    by fastforce
  have h9: "(pfunToRel (ety SG1) \<union> pfunToRel (ety SG2)) ``
    (SG1 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG1 - EsI SG1 \<union> SG2 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG2 - EsI SG2)
    =  pfunToRel (ety SG1) `` (SG1 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG1 - EsI SG1)
    \<union> pfunToRel (ety SG2) `` (SG2 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG2 - EsI SG2)"
  proof
    show "(pfunToRel (ety SG1) \<union> pfunToRel (ety SG2)) ``
    (SG1 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG1 - EsI SG1 \<union> SG2 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG2 - EsI SG2)
    \<subseteq> pfunToRel (ety SG1) `` (SG1 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG1 - EsI SG1) \<union>
       pfunToRel (ety SG2) `` (SG2 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG2 - EsI SG2)"
    proof
      fix x
      assume "x \<in> (pfunToRel (ety SG1) \<union> pfunToRel (ety SG2)) ``
             (SG1 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG1 - EsI SG1 \<union> SG2 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG2 -
              EsI SG2)"
      hence "x \<in> (pfunToRel (ety SG1) \<union> pfunToRel (ety SG2)) `` 
          (SG1 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG1 - EsI SG1) 
          \<union> (pfunToRel (ety SG1) \<union> pfunToRel (ety SG2)) `` (SG2 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG2 -
              EsI SG2)" by auto
      hence "x \<in> pfunToRel (ety SG1) `` (SG1 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG1 - EsI SG1)
        \<union> pfunToRel (ety SG1) `` (SG2 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG2 - EsI SG2)
        \<union> pfunToRel (ety SG2) `` (SG1 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG1 - EsI SG1)
        \<union> pfunToRel (ety SG2) `` (SG2 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG2 - EsI SG2)" 
        by auto  
      then show "x \<in> pfunToRel (ety SG1) `` (SG1 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG1 - EsI SG1) \<union>
              pfunToRel (ety SG2) `` (SG2 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG2 - EsI SG2)"
       using h7 h8 assms wf_sg_ftotal_on_ety[of SG1] 
            wf_sg_ftotal_on_ety[of SG2]
        by (simp add: Image_outside_domain ftotal_on_def
            disjGs_imp_disjEsGs es_disj_Ga_Gb Domain_is_dom)
    qed
  next
    show "pfunToRel (ety SG1) `` (SG1 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG1 - EsI SG1) \<union>
    pfunToRel (ety SG2) `` (SG2 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG2 - EsI SG2)
    \<subseteq> (pfunToRel (ety SG1) \<union> pfunToRel (ety SG2)) ``
       (SG1 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG1 - EsI SG1 \<union> SG2 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG2 - EsI SG2)"
    proof
      fix x
      assume "x \<in> pfunToRel (ety SG1) `` (SG1 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG1 - EsI SG1) \<union>
      pfunToRel (ety SG2) `` (SG2 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG2 - EsI SG2)"
      then show "x \<in> (pfunToRel (ety SG1) \<union> pfunToRel (ety SG2)) ``
              (SG1 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG1 - EsI SG1 \<union> SG2 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG2 -
               EsI SG2)" 
      proof
        assume "x \<in> pfunToRel (ety SG1) `` (SG1 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG1 - EsI SG1)"
        hence "x \<in> (pfunToRel (ety SG1) \<union> pfunToRel (ety SG2)) `` 
          (SG1 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG1 - EsI SG1)"
          by auto
        then show "x \<in> (pfunToRel (ety SG1) \<union> pfunToRel (ety SG2)) ``
              (SG1 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG1 - EsI SG1 \<union> SG2 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG2 - EsI SG2)"
          by (smt (verit, ccfv_SIG) DiffI EsI_sub_Es ImageE ImageI IntD1 Un_Int_eq(1) assms(2) disjoint_iff h7 subset_eq)
      next
        assume "x \<in> pfunToRel (ety SG2) `` (SG2 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG2 - EsI SG2)"
        then show "x \<in> (pfunToRel (ety SG1) \<union> pfunToRel (ety SG2)) ``
              (SG1 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG1 - EsI SG1 \<union> SG2 \<circ>\<rightarrow>\<circ>\<^sup>* NsO SG2 - EsI SG2)"
         by auto
      qed
    qed
  qed
  show ?thesis
    using assms h1 h2 h3 h4
    esIncidentst_disjoint_vs[of SG1 "NsO SG2"]
    esIncidentst_disjoint_vs[of SG2 "NsO SG1"]
    wf_sg_ftotal_on_ety[of SG1] wf_sg_ftotal_on_ety[of SG2]
    h6 
  by (simp add: optsVoluntary_def NsO_USG EsI_USG 
      EsIncidentst_USG wf_sg_def esIncidentst_Un h5
      ftotal_on_def pfunToRel_map_add h9)
qed

lemma inhOk_SG1_USG_SG2:
  assumes "wf_sg SG1" and "wf_sg SG2" and "disjGs SG1 SG2"
  shows "inhOk (SG1 USG SG2)"
proof-
  have h1: "acyclicGr (inhG SG1)" 
    using assms(1) by (simp add: wf_sg_def inhOk_def)
  have h2: "acyclicGr (inhG SG2)" 
    using assms(2) by (simp add: wf_sg_def inhOk_def)
  have h3: "pfun_on ((inhG SG1  \<ominus>\<^sub>N\<^sub>S NsV SG1 )\<^sup>\<Leftrightarrow>) (Ns (SG1)) (Ns (SG1))"
    using assms(1) by (simp add: wf_sg_def inhOk_def)
  have h4: "pfun_on ((inhG SG2  \<ominus>\<^sub>N\<^sub>S NsV SG2 )\<^sup>\<Leftrightarrow>) (Ns (SG2)) (Ns (SG2))"
    using assms(2) by (simp add: wf_sg_def inhOk_def)
  show ?thesis
  proof (simp add: inhOk_def)
    apply_end (rule conjI)
    show "\<forall>v v'.
       (v, v') \<in> inh (SG1 USG SG2) \<longrightarrow>
       the ((nty SG1 ++ nty SG2) v) <\<^sub>N\<^sub>T the ((nty SG1 ++ nty SG2) v')"
    proof (clarsimp)
      fix v v'
      assume "(v, v') \<in> inh (SG1 USG SG2)"
      hence "(v, v') \<in> (inh SG1) \<or> (v, v') \<in> (inh SG2)"
        using assms by (simp add: inh_USG)
      then show "the ((nty SG1 ++ nty SG2) v) <\<^sub>N\<^sub>T the ((nty SG1 ++ nty SG2) v')"
      proof
        assume "(v, v') \<in> inh SG1"
        hence "v \<in> Ns SG1" 
          using assms(1) Domain_inh 
          by (auto simp add: Domain_iff)
        hence ha: "(nty SG1 ++ nty SG2) v = nty SG1 v"
          using assms wf_sg_ftotal_on_nty[of SG1]
            wf_sg_ftotal_on_nty[of SG2]
          by (simp add: ftotal_on_dom map_add_disj_domf ns_disj_Ga_Gb)
        have "v' \<in> Ns SG1"
          using assms(1) Range_inh \<open>(v, v') \<in> inh SG1\<close>
          by (auto simp add: Range_iff)
        hence hb: "(nty SG1 ++ nty SG2) v' = nty SG1 v'"
          using assms wf_sg_ftotal_on_nty[of SG1]
            wf_sg_ftotal_on_nty[of SG2]
          by (simp add: ftotal_on_dom map_add_disj_domf ns_disj_Ga_Gb)
        show "the ((nty SG1 ++ nty SG2) v) <\<^sub>N\<^sub>T the ((nty SG1 ++ nty SG2) v')"
          using \<open>(v, v') \<in> inh SG1\<close> assms(1) ha hb inhOk_def wf_sg_def 
          by auto
      next
        assume "(v, v') \<in> inh SG2"
        hence "v \<in> Ns SG2" 
          using assms(2) Domain_inh 
          by (auto simp add: Domain_iff)
        hence ha: "(nty SG1 ++ nty SG2) v = nty SG2 v"
          using assms wf_sg_ftotal_on_nty[of SG1]
            wf_sg_ftotal_on_nty[of SG2] 
            map_add_disj_domf[of "nty SG2" "nty SG1" v]
          by (auto simp add: ftotal_on_def map_add_comm disjGs_def)
        have "v' \<in> Ns SG2"
          using assms(2) Range_inh \<open>(v, v') \<in> inh SG2\<close>
          by (auto simp add: Range_iff)
        hence hb: "(nty SG1 ++ nty SG2) v' = nty SG2 v'"
          using assms wf_sg_ftotal_on_nty[of SG1]
            wf_sg_ftotal_on_nty[of SG2]
            map_add_disj_domf[of "nty SG2" "nty SG1" v']
          by (auto simp add: ftotal_on_dom map_add_disj_domf map_add_comm
              disjGs_def)
        show "the ((nty SG1 ++ nty SG2) v) <\<^sub>N\<^sub>T the ((nty SG1 ++ nty SG2) v')"
          using \<open>(v, v') \<in> inh SG2\<close> assms(2) ha hb inhOk_def wf_sg_def 
          by auto
      qed
    qed
  next
    apply_end (rule conjI)
    show "acyclicGr (inhG (SG1 USG SG2))"
      using assms h1 h2 by (simp add: acyclic_SGr_Un_dist)
  next
    have ha: "NsV SG2 \<inter> Ns (inhG SG1) = {}" 
      using assms ran_src_G[of SG1] wf_sg_wf_g[of SG1]
        ran_tgt_G[of SG1]
        NsV_sub_Ns[of SG2] NsInhG_sub_Ns[of SG1] 
        ns_disj_Ga_Gb[of SG1 SG2]
      by (auto)
    have hb: "NsV SG1  \<inter> Ns (inhG SG2) = {}" 
      using assms ran_src_G[of SG2] wf_sg_wf_g[of SG2]
        ran_tgt_G[of SG2] NsInhG_sub_Ns[of SG2] 
        NsV_sub_Ns[of SG1] ns_disj_Ga_Gb[of SG1 SG2]
      by (auto)
    have hc: "NsV SG1 \<union> NsV SG2 = NsV SG2 Un NsV SG1" by auto
    have hd: "inhG SG1 \<ominus>\<^sub>N\<^sub>S (NsV (SG1 USG SG2)) = inhG SG1 \<ominus>\<^sub>N\<^sub>S (NsV SG1)"
      using assms subtract_Ns_disj[of "inhG SG1" "NsV SG2"] 
      NsV_sub_Ns[of SG1] NsV_sub_Ns[of SG2] 
      ns_disj_Ga_Gb[of SG1 SG2] ha wf_g_inhG[of SG1]
      wf_sg_wf_g[of SG1] 
      by (simp only: NsV_USG subtract_Ns_disj subtract_Ns_Un hc)
    have he: "inhG SG2 \<ominus>\<^sub>N\<^sub>S (NsV (SG1 USG SG2)) = inhG SG2 \<ominus>\<^sub>N\<^sub>S (NsV SG2)"
      using assms subtract_Ns_disj[of "inhG SG1" "NsV SG2"] 
      NsV_sub_Ns[of SG1] NsV_sub_Ns[of SG2] wf_sg_wf_g[of SG1] 
      ns_disj_Ga_Gb[of SG1 SG2] hb wf_g_inhG[of SG2]
      wf_sg_wf_g[of SG2] 
      by (simp only: NsV_USG subtract_Ns_disj subtract_Ns_Un)
    have hf: "wf_g (inhG SG1 \<ominus>\<^sub>N\<^sub>S NsV SG1)"
      using assms wf_sg_wf_g[of SG1] wf_g_inhG[of SG1]
      by (simp add: wf_subtractNs)
    have hg: "wf_g (inhG SG2 \<ominus>\<^sub>N\<^sub>S NsV SG2)"
      using assms wf_sg_wf_g[of SG2] wf_g_inhG[of SG2]
      by (simp add: wf_subtractNs)
    have hh: "disjEsGs (inhG SG1 \<ominus>\<^sub>N\<^sub>S NsV SG1) (inhG SG2 \<ominus>\<^sub>N\<^sub>S NsV SG2)"
      using assms disjGs_imp_disjEsGs[of SG1 SG2] 
        inhG_disj_Es[of SG1 SG2] disjEsGs_subtractG
      by (simp)
    show "pfun_on ((inhG (SG1 USG SG2) \<ominus>\<^sub>N\<^sub>S NsV (SG1 USG SG2))\<^sup>\<Leftrightarrow>) (Ns (SG1) \<union>  Ns(SG2)) (Ns (SG1) \<union> Ns(SG2))"
      using assms disjGs_imp_disjEsGs[of SG1 SG2]
      wf_sg_wf_g[of SG1] wf_sg_wf_g[of SG2] inhG_USG
      wf_g_inhG[of SG1] wf_g_inhG[of SG2] 
      disjGs_imp_disjEsGs[of "inhG SG1" "inhG SG2"]
      disjGs_inhG[of SG1 SG2] 
      subtract_Ns_disj[of "inhG SG1" "Ns (inhG SG2)"]
      subtract_Ns_disj[of "inhG SG2" "Ns (inhG SG1)"]
      ns_disj_Ga_Gb ha hb h3 h4
      by (auto simp add: inhG_USG subtract_Ns_UG  hd he hf hg hh 
          relG_UG pfun_on_Un disjGs_def)
  qed
qed
  

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
  show "ftotal_on (nty SG1 ++ nty SG2) (Ns SG1 \<union> Ns SG2) SGNT_set"
    using assms wf_sg_ftotal_on_nty[of SG1] wf_sg_ftotal_on_nty[of SG2] 
    ftotal_on_map_add[where f = "nty SG1" and g = "nty SG2" 
      and A="Ns SG1" and C="Ns SG2" and B="SGNT_set" and D="SGNT_set"]
    by (auto simp add: cupSG_def  disjGs_def)
next
  apply_end(rule conjI)
  show "ftotal_on (ety SG1 ++ ety SG2) (Es (SG1 USG SG2)) SGET_set"
    using assms wf_sg_ftotal_on_ety[of SG1] wf_sg_ftotal_on_ety[of SG2] 
    ftotal_on_map_add[where f = "ety SG1" and g = "ety SG2" 
      and A="Es SG1" and C="Es SG2" and B="SGET_set" and D="SGET_set"] 
    by (auto simp add: cupSG_def  disjGs_def)
next
  apply_end(rule conjI)
  show "ftotal_on (srcma (SG1 USG SG2)) (EsC (SG1 USG SG2)) MultC_set"
  using assms wf_sg_ftotal_on_srcma[of SG1] 
        wf_sg_ftotal_on_srcma[of SG2] 
         EsC_sub_Es[of SG1] EsC_sub_Es[of SG2] 
         disjGs_imp_disjEsGs[of SG1 SG2]
        ftotal_on_map_add[where f = "srcma SG1" and g = "srcma SG2" 
      and A="EsC SG1" and C="EsC SG2" and B="MultC_set" and D="MultC_set"]
  by (simp add: EsC_USG srcma_USG disjEsGs_def, force)
next
  apply_end(rule conjI)
  show "ftotal_on (tgtm SG1 ++ tgtm SG2) (EsC (SG1 USG SG2)) MultC_set"
  using assms wf_sg_ftotal_on_tgtm[of SG1] 
        wf_sg_ftotal_on_tgtm[of SG2] 
        EsC_sub_Es[of SG1] EsC_sub_Es[of SG2] 
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
  apply_end(rule conjI)
  show "multsOk (SG1 USG SG2)"
    using assms by (simp only: multsOk_USG)
next
  apply_end(rule conjI)
  show "optsVoluntary (SG1 USG SG2)" 
    using assms by (simp add: optsVoluntary_USG)
next
  show "inhOk (SG1 USG SG2)"
  using assms by (simp add: inhOk_SG1_USG_SG2)
qed
        
definition morphSGr :: "SGr \<Rightarrow> SGr \<Rightarrow> Morph set"
where
  "morphSGr SG1 SG2 \<equiv> {r. wf_sg SG1 \<and> wf_sg SG2
      \<and> ftotal_on (fV r) (Ns SG1) (Ns SG2) 
      \<and> ftotal_on (fE r) (Es SG1) (Es SG2)  
      \<and> srcst SG1 O pfunToRel(fV r)  \<subseteq> pfunToRel(fE r) O srcst SG2  
      \<and> tgtst SG1 O pfunToRel(fV r) \<subseteq> pfunToRel(fE r) O tgtst SG2  
      \<and> inhst SG1 O pfunToRel (fV r) \<subseteq> pfunToRel (fV r) O inhst SG2}"

definition morphGr2SGr :: "Gr \<Rightarrow> SGr \<Rightarrow> Morph set"
where
  "morphGr2SGr G1 SG2 \<equiv> {r. wf_g G1 \<and> wf_sg SG2
      \<and> ftotal_on (fV r) (Ns G1) (Ns SG2) 
      \<and> ftotal_on (fE r) (Es G1) (Es SG2)  
      \<and> pfunToRel((fV r) \<circ>\<^sub>m (src G1)) \<subseteq> pfunToRel(fE r) O srcst SG2  
      \<and> pfunToRel((fV r) \<circ>\<^sub>m (tgt G1)) \<subseteq> pfunToRel(fE r) O tgtst SG2}"

end
