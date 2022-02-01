(*  Title:       Fragmenta theory of Fragments (Frs)
    Description: 'Fragmenta' theory presented in the Models 2015 paper.
    Author:      Nuno Amálio
*)
theory Fragmenta_Frs
imports Fragmenta_SGs "../Extra/Rel_Extra" 
                    
begin

(*Fragments*)      
record Fr = 
  fsg :: "SGr"
  esr :: "E set"
  sr :: "E \<rightharpoonup> V"
  tr :: "E \<rightharpoonup> V"

definition consF::"SGr\<Rightarrow>E set\<Rightarrow>(E \<rightharpoonup> V)\<Rightarrow>(E \<rightharpoonup> V)\<Rightarrow>Fr"
  where 
  "consF sg es s t = \<lparr>fsg = sg, esr = es, sr = s, tr = t\<rparr>"

(* Empty Fragment*)
definition emptyF :: "Fr"
where
  "emptyF \<equiv> consF emptySG {} Map.empty Map.empty"

lemma Fr_eq: 
  shows "(F1 = F2) \<longleftrightarrow> fsg F1 = fsg F2 \<and> esr F1 = esr F2
    \<and> sr F1 = sr F2 \<and> tr F1 = tr F2 
    \<and> Fr.more F1 = Fr.more F2"
    by (auto)

(*Local edges*)
definition flEs :: "'a Fr_scheme \<Rightarrow> E set"
where
  "flEs F \<equiv> Es (fsg F)"

(*All edges*)
definition fEs :: "'a Fr_scheme \<Rightarrow> E set"
where
  "fEs F \<equiv> flEs F \<union> esr F"

(*Local nodes*)
definition flNs :: "'a Fr_scheme \<Rightarrow> V set"
where
  "flNs F \<equiv> Ns (fsg F)"

(*Referenced nodes*)
definition fRNs :: "'a Fr_scheme \<Rightarrow> V set"
where
  "fRNs F \<equiv> ran (tr F)"

(*Fragment nodes*)
definition fNs :: "'a Fr_scheme \<Rightarrow> V set"
where
  "fNs F \<equiv> flNs F \<union> fRNs F"

(*Source function with directed references*)
definition srcF :: "'a Fr_scheme \<Rightarrow> E \<rightharpoonup> V"
where
  "srcF F \<equiv> src (fsg F) ++ (sr F)"

(*Target function with directed references*)
definition tgtF :: "'a Fr_scheme \<Rightarrow> E \<rightharpoonup> V"
where
  "tgtF F \<equiv> tgt (fsg F) ++ (tr F)"

definition wf_fz :: "'a Fr_scheme \<Rightarrow> bool"
where
  "wf_fz F \<equiv> wf_sg (fsg F) 
    \<and> (esr F) \<subseteq> E_A 
    \<and> (esr F) \<inter> (flEs F) = {}
    \<and> fbij_on (sr F) (esr F) (NsP (fsg F))
    \<and> ftotal_on (tr F) (esr F) V_A"

lemma wf_fz_wf_sg:
  assumes "wf_fz F"
  shows "wf_sg (fsg F)"
  using assms by (simp add: wf_fz_def)

lemma wf_fz_sr_bij:
  assumes "wf_fz F"
  shows "fbij_on (sr F) (esr F) (NsP (fsg F))"
  using assms by (simp add: wf_fz_def)

lemma wf_fz_disj_esr_fles:
  assumes "wf_fz F"
  shows "(esr F) \<inter> (flEs F) = {}"
  using assms by (simp add: wf_fz_def)

lemma wf_fz_esr_sub_EA:
  assumes "wf_fz F"
  shows "(esr F) \<subseteq> E_A"
  using assms by (simp add: wf_fz_def)

lemma wf_fz_tr_ftotal: 
  assumes "wf_fz F"
  shows "ftotal_on (tr F) (esr F) (V_A)"
  using assms by (simp add: wf_fz_def)

definition disj_fs::"'a Fr_scheme \<Rightarrow>'a Fr_scheme\<Rightarrow>bool" 
  where
  "disj_fs F1 F2 \<equiv> disjoint [flNs F1, flNs F2] \<and> disjoint [fEs F1, fEs F2]"

lemma disj_fs_imp_disj_Gs:
  assumes "wf_fz F1" and "wf_fz F2" and "disj_fs F1 F2"
  shows "disjGs (fsg F1) (fsg F2)"
  using assms disj_V_E wf_fz_wf_sg[of F1] wf_sg_wf_g[of "fsg F1"]
    wf_fz_wf_sg[of F2] wf_sg_wf_g[of "fsg F2"]
  by (auto simp add: disjGs_def disj_fs_def flNs_def fEs_def 
      flEs_def  wf_g_def)

definition disj_fsL::"'a Fr_scheme list \<Rightarrow>bool" 
  where
  "disj_fsL Fs \<equiv> disjGsL (map fsg Fs) \<and> disjoint(map esr Fs)"

(*References Graph*)
definition refsG :: "'a Fr_scheme \<Rightarrow> Gr"
where
  "refsG F \<equiv> consG (NsP (fsg F) \<union> (fRNs F)) (esr F) (sr F) (tr F)"

lemma Ns_refsG[simp]: "Ns (refsG F) = NsP (fsg F) \<union> (fRNs F)"
  by (auto simp add: refsG_def consG_def)

lemma Es_refsG[simp]: "Es (refsG F) = esr F"
  by (simp add: refsG_def consG_def)

lemma src_refsG[simp]: "src (refsG F) = (sr F)"
  by (simp add: refsG_def consG_def)

lemma tgt_refsG[simp]: "tgt (refsG F) = (tr F)"
  by (simp add: refsG_def consG_def)

definition refEOf ::"'a Fr_scheme \<Rightarrow>V\<Rightarrow>E option"
  where
  "refEOf F \<equiv> \<lambda> v. if v \<in> NsP( fsg F) then (Some (the_elem ((sr F) -`{Some v}))) else None"

lemma one_e_in_dom_sr:
  assumes "wf_fz F" and "v \<in> NsP( fsg F)"
  shows "\<exists>!e. sr F e = Some v"
  proof (rule ccontr)
    assume h: "\<nexists>!e. sr F e = Some v"
    have "v \<in> ran (sr F)"
      using assms wf_fz_sr_bij[of F]
      by (simp add: fbij_on_def)
    hence "\<exists> e. sr F e = Some v" by (simp add: ran_def)
    then show "False"
      using h assms wf_fz_sr_bij[of F]
      by (force simp add: fbij_on_def finj_on_def Map_Extra.injective_def)
  qed

lemma refEOfIsFLE:
  assumes "wf_fz F" and "v \<in> NsP( fsg F)"
  shows "the (refEOf F v) \<in> (esr F)"
proof -
  show ?thesis
  proof (simp add: assms(2) refEOf_def)
    have h1: "\<exists>!e. sr F e = Some v"
      using assms one_e_in_dom_sr[of F v] by simp
    from h1 obtain e where "sr F e = Some v" by auto
    hence h2: "the_elem (sr F -` {Some v}) = e"
      using the1_equality[of "\<lambda> e. sr F e = Some v" "e"] h1
      by (auto simp add: the_elem_def vimage_def)
    have "e \<in> dom (sr F)" 
      using \<open>sr F e = Some v\<close> by (simp add: dom_def)
    then show "the_elem (sr F -` {Some v}) \<in> esr F"
      using h2 assms wf_fz_sr_bij[of F] 
      by (simp add: fbij_on_def finj_on_def ftotal_on_def)
  qed
qed

lemma dom_refEOf_eq_NsP:
  assumes "wf_fz F"
  shows "dom(refEOf F) = NsP( fsg F)"
  by (auto simp add: refEOf_def domIff subsetI split: if_splits)

lemma ran_refEOf_eq_esr:
  assumes "wf_fz F"
  shows "ran(refEOf F) = esr F"
proof
  show "ran (refEOf F) \<subseteq> esr F"
    by (smt (verit, best) assms domI dom_refEOf_eq_NsP mem_Collect_eq option.sel ran_def refEOfIsFLE subsetI)
next
  show "esr F \<subseteq> ran (refEOf F)"
  proof
    fix e
    assume "e \<in> esr F"
    hence "e \<in> dom (sr F)"
      using assms wf_fz_sr_bij[of F]
      by (simp add: fbij_on_def finj_on_def ftotal_on_def)
    then obtain v where "(sr F) e = Some v" by auto
    hence "v \<in> NsP (fsg F)"
      using assms wf_fz_sr_bij[of F]
      by (force simp add: fbij_on_def ranI)
    hence "\<exists>!e. sr F e = Some v"
      using assms one_e_in_dom_sr[of F v] by simp
    hence "the_elem (sr F -` {Some v}) = e"
      using the1_equality[of "\<lambda> e. sr F e = Some v" "e"]
      \<open>sr F e = Some v\<close>
      by (auto simp add: the_elem_def vimage_def)
    then show "e \<in> ran (refEOf F)"
      using \<open>v \<in> NsP (fsg F)\<close>
      by (auto simp add: refEOf_def ran_def)
  qed
qed

lemma sr_F_the_refEOf_eq_v:
  assumes "wf_fz F" and "v \<in> NsP( fsg F)"
  shows "sr F (the (refEOf F v)) = Some v"
proof (simp add: assms(2) refEOf_def vimage_def)
  have h1: "\<exists>!e. sr F e = Some v"
      using assms one_e_in_dom_sr[of F v] by simp
  from h1 obtain e where "sr F e = Some v" by auto
  hence h2: "the_elem {x. sr F x = Some v} = e"
    using the1_equality[of "\<lambda> e. sr F e = Some v" "e"] h1
    by (auto simp add: the_elem_def vimage_def)
  then show "sr F (the_elem {x. sr F x = Some v}) = Some v"
    using \<open>sr F e = Some v\<close> by auto
qed

(*References partial function, used in fragment resolution*)
definition refs :: "'a Fr_scheme \<Rightarrow> (V \<rightharpoonup> V)"
  where
  "refs F \<equiv> (\<lambda>v. if v \<in> NsP( fsg F) then  (tr F) (the (refEOf F v)) else None)"

lemma dom_refsF:
  assumes "wf_fz F"
  shows "dom (refs F) = NsP( fsg F)"
proof
  show "dom (refs F) \<subseteq> NsP (fsg F)"
    by (simp add: refs_def domIff subset_iff)
next
  show "NsP (fsg F) \<subseteq> dom (refs F)"
  proof
    fix v
    assume "v \<in> NsP (fsg F)"
    then show "v \<in> dom (refs F)"
    using assms wf_fz_tr_ftotal[of F] refEOfIsFLE[of F]
    by (auto simp add: refs_def domIff ftotal_on_def)
  qed
qed

lemma ran_refsF:
  assumes "wf_fz F"
  shows "ran (refs F) \<subseteq> V_A"
  using assms wf_fz_tr_ftotal[of F]
  by (auto simp add: refs_def subset_eq ftotal_on_def ran_def)

lemma Domain_refsG_eq_NsP:
  assumes "wf_fz F"
  shows "Domain ((refsG F)\<^sup>\<Leftrightarrow>) = NsP( fsg F)"
proof
  show "Domain ((refsG F)\<^sup>\<Leftrightarrow>) \<subseteq> NsP( fsg F)"
  proof
    fix v
    assume "v \<in> Domain ((refsG F)\<^sup>\<Leftrightarrow>)"
    hence "v \<in> ran(sr F)"
      by (auto simp add: relG_def adjacent_def ran_def)
    then show "v \<in> NsP (fsg F)"
      using assms wf_fz_sr_bij[of F] 
      by (simp add: fbij_on_def)
  qed
next
  show "NsP (fsg F) \<subseteq> Domain ((refsG F)\<^sup>\<Leftrightarrow>)"
  proof
    fix v
    assume "v \<in> NsP (fsg F)"
    hence "v \<in> ran(sr F)"
      using assms wf_fz_sr_bij[of F] 
      by (auto simp add: ran_def fbij_on_def)
    then obtain e where "e \<in> esr F \<and> sr F e = Some v"
      using assms wf_fz_sr_bij[of F]
      by (auto simp add: ran_def fbij_on_def finj_on_def ftotal_on_def)
    from \<open>e \<in> esr F \<and> sr F e = Some v\<close> obtain v' where "tr F e = Some v'"
      using assms wf_fz_tr_ftotal[of F]
      by (auto simp add: ftotal_on_def ran_def)
    show "v \<in> Domain ((refsG F)\<^sup>\<Leftrightarrow>)"
      using \<open>e \<in> esr F \<and> sr F e = Some v\<close> \<open>tr F e = Some v'\<close>
      by (auto simp add: Domain_iff relG_def adjacent_def)
  qed
qed

lemma refsF_eq_refsG_rel:
  assumes "wf_fz F"
  shows "pfunToRel (refs F) = (refsG F)\<^sup>\<Leftrightarrow>"
proof 
  show "pfunToRel (refs F) \<subseteq> (refsG F)\<^sup>\<Leftrightarrow>"
  proof (rule subrelI)
    fix v v'
    assume h: "(v, v') \<in> pfunToRel (refs F)"
    hence "v \<in> NsP (fsg F)"
      using assms dom_refsF
      by (auto simp add: pfunToRel_iff)
    hence "\<exists> e. e = the (refEOf F v) \<and> sr F e = Some v \<and> tr F e = Some v'"
      using h assms 
      by (auto simp add: refs_def pfunToRel_def sr_F_the_refEOf_eq_v)
    then show "(v, v') \<in> (refsG F)\<^sup>\<Leftrightarrow>"
      using \<open>v \<in> NsP (fsg F)\<close> adjacent_def assms 
        refEOfIsFLE relG_def by fastforce
  qed
next
  show "(refsG F)\<^sup>\<Leftrightarrow> \<subseteq> pfunToRel (refs F)"
  proof (rule subrelI)
    fix v v'
    assume h: "(v, v') \<in> (refsG F)\<^sup>\<Leftrightarrow>"
    hence "v \<in> NsP (fsg F)"
    using assms Domain_refsG_eq_NsP
    by (auto)
    hence "v \<in> ran(sr F)"
      using assms wf_fz_sr_bij[of F] 
      by (auto simp add: ran_def fbij_on_def)
    from \<open>v \<in> ran(sr F)\<close> obtain e where "e \<in> esr F \<and> sr F e = Some v"
      using assms wf_fz_sr_bij[of F]
      by (auto simp add: ran_def fbij_on_def finj_on_def ftotal_on_def)
    have "tr F e = Some v'"
      using assms wf_fz_tr_ftotal[of F] h  \<open>e \<in> esr F \<and> sr F e = Some v\<close>
      \<open>v \<in> NsP (fsg F)\<close> one_e_in_dom_sr
      by (auto simp add: ftotal_on_def relG_def adjacent_def)
    have "the (refEOf F v) = e"
      using assms \<open>e \<in> esr F \<and> sr F e = Some v\<close> \<open>v \<in> NsP (fsg F)\<close>
       one_e_in_dom_sr[of F v]
      by (auto simp add: refEOf_def vimage_def the_elem_def)
    show "(v, v') \<in> pfunToRel (refs F)"
      using \<open>tr F e = Some v'\<close> \<open>e \<in> esr F \<and> sr F e = Some v\<close> 
      \<open>v \<in> NsP (fsg F)\<close> \<open>the (refEOf F v) = e\<close>
      by (auto simp add: pfunToRel_iff refs_def)
  qed
qed

(*Fragments union*)
definition cupF :: "Fr \<Rightarrow> Fr \<Rightarrow> Fr" (infixl "\<union>\<^sub>F" 100)
where
  "F1 \<union>\<^sub>F F2 \<equiv> \<lparr>fsg =  (fsg F1) USG (fsg F2), esr = esr F1 \<union> esr F2,
    sr = sr F1 ++ sr F2, tr = tr F1 ++ tr F2\<rparr>"

lemma fsg_UF[simp]: "fsg (F1 \<union>\<^sub>F F2) = (fsg F1) USG (fsg F2)"
  by (simp add: cupF_def)

lemma esr_UF[simp]: "esr (F1 \<union>\<^sub>F F2) = esr F1 \<union> esr F2"
  by (simp add: cupF_def)

lemma sr_UF[simp]: "sr (F1 \<union>\<^sub>F F2) = sr F1 ++ sr F2"
  by (simp add: cupF_def)

lemma tr_UF[simp]: "tr (F1 \<union>\<^sub>F F2) = tr F1 ++ tr F2"
  by (simp add: cupF_def)

(*In most cases, '++' equates to union as fragments are disjoint*)

(* builds union of a set of fragments*)
primrec bUF :: "Fr list \<Rightarrow>Fr" ("\<Union>\<^sub>F") 
where
  bUF_base: "\<Union>\<^sub>F [] = emptyF" |
  bUF_induct: "\<Union>\<^sub>F (F#Fs) = F \<union>\<^sub>F (\<Union>\<^sub>F Fs)"

lemma refEOf_map_add_f:
  assumes "wf_fz F1" and "wf_fz F2"  and "disj_fs F1 F2" 
    and "v \<in> NsP (fsg F1)"
  shows "(refEOf F1 ++ refEOf F2) v = refEOf F1 v"
    using assms wf_fz_wf_sg[of F1] wf_fz_wf_sg[of F2]
         dom_refEOf_eq_NsP[of F1] dom_refEOf_eq_NsP[of F2] 
         map_add_disj_domf[of "refEOf F1" "refEOf F2" v]
         NsP_sub_Ns[of "fsg F1"] NsP_sub_Ns[of "fsg F2"]
    by (force simp add: disj_fs_def flNs_def fEs_def flEs_def)

lemma tr_map_addrefEOf_f:
  assumes "wf_fz F1" and "wf_fz F2"  and "disj_fs F1 F2" 
    and "v \<in> NsP (fsg F1)"
  shows "(tr F1 ++ tr F2) (the (refEOf F1 v)) = tr F1 (the (refEOf F1 v))"
proof-
  have "dom (tr F1) \<inter> dom(tr F2) = {}"
      using assms wf_fz_tr_ftotal[of F1] wf_fz_tr_ftotal[of F2]
      by (auto simp add:  disj_fs_def ftotal_on_def fEs_def)
  have "the (refEOf F1 v) \<in> dom (tr F1)"
    using assms wf_fz_tr_ftotal[of F1] refEOfIsFLE[of F1 v]
    by (simp add: ftotal_on_dom)
  show ?thesis
    using assms \<open>dom (tr F1) \<inter> dom(tr F2) = {}\<close> 
    \<open>the (refEOf F1 v) \<in> dom (tr F1)\<close> 
    map_add_disj_domf[of "tr F1" "tr F2" "the (refEOf F1 v)"] 
    by simp
qed

lemma refEOf_UF:
  assumes "wf_fz F1" and "wf_fz F2" and "disj_fs F1 F2"
  shows "refEOf (F1 \<union>\<^sub>F F2) = (refEOf F1)++(refEOf F2)"
proof -
  have "dom (sr F1) \<inter> dom(sr F2) = {}"
      using assms wf_fz_sr_bij[of F1] wf_fz_sr_bij[of F2]
      by (auto simp add:  disj_fs_def fbij_on_def finj_on_def 
          ftotal_on_def fEs_def)
  have "ran (sr F1) \<inter> ran(sr F2) = {}"
      using assms wf_fz_sr_bij[of F1] wf_fz_sr_bij[of F2]
      wf_fz_wf_sg[of F1] wf_fz_wf_sg[of F2]
      NsP_sub_Ns[of "fsg F1"] NsP_sub_Ns[of "fsg F2"]
      by (auto simp add:  disj_fs_def fbij_on_def fEs_def flNs_def)
  show ?thesis
  proof
    fix v
    show "refEOf (F1 \<union>\<^sub>F F2) v = (refEOf F1 ++ refEOf F2) v"
    proof (case_tac "v \<in> NsP (fsg F1 USG fsg F2)")
      assume "v \<in> NsP (fsg F1 USG fsg F2)"
      hence "v \<in> NsP (fsg F1) \<or> v \<in> NsP (fsg F2)"
        using assms wf_fz_wf_sg[of F1] wf_fz_wf_sg[of F2] 
        by (simp add: disj_fs_imp_disj_Gs NsP_USG)
      then show "refEOf (F1 \<union>\<^sub>F F2) v = (refEOf F1 ++ refEOf F2) v"
      proof
        assume "v \<in> NsP (fsg F1)"
        hence "v \<in> ran(sr F1)"
          using assms wf_fz_sr_bij[of F1] 
          by (auto simp add: ran_def fbij_on_def)
        show "refEOf (F1 \<union>\<^sub>F F2) v = (refEOf F1 ++ refEOf F2) v"
          using \<open>v \<in> NsP (fsg F1 USG fsg F2)\<close>
            \<open>dom (sr F1) \<inter> dom(sr F2) = {}\<close>
            \<open>ran (sr F1) \<inter> ran(sr F2) = {}\<close>
            \<open>v \<in> ran(sr F1)\<close> \<open>v \<in> NsP (fsg F1)\<close>
            assms vimage_disj_ran_1[of "sr F1" "sr F2" v]
          by (simp only: refEOf_map_add_f)
            (auto simp add: refEOf_def split: option.splits)
      next
        assume "v \<in> NsP (fsg F2)"
        hence "v \<in> ran(sr F2)"
          using assms wf_fz_sr_bij[of F2] 
          by (auto simp add: ran_def fbij_on_def)
        have h: "(refEOf F1 ++ refEOf F2) v = refEOf F2 v"
          using \<open>v \<in> NsP (fsg F2)\<close> assms(2)
            \<open>dom (sr F1) \<inter> dom(sr F2) = {}\<close>
            \<open>ran (sr F1) \<inter> ran(sr F2) = {}\<close>
          by (simp add: dom_refEOf_eq_NsP map_add_dom_app_simps)
        show "refEOf (F1 \<union>\<^sub>F F2) v = (refEOf F1 ++ refEOf F2) v"
          using \<open>v \<in> NsP (fsg F1 USG fsg F2)\<close> \<open>v \<in> NsP (fsg F2)\<close>
          vimage_disj_ran_2[of "sr F1" "sr F2" v]
          \<open>v \<in> ran(sr F2)\<close> \<open>dom (sr F1) \<inter> dom(sr F2) = {}\<close>
            \<open>ran (sr F1) \<inter> ran(sr F2) = {}\<close>
          by (simp only: h)
          (auto simp add: refEOf_def split: option.splits)
      qed
    next
      assume "v \<notin> NsP (fsg F1 USG fsg F2)"
      hence "v \<notin> NsP (fsg F1) \<and> v \<notin> NsP (fsg F2)"
        using assms
        by (simp add: NsP_USG disj_fs_imp_disj_Gs wf_fz_wf_sg)
      hence h: "(refEOf F1 ++ refEOf F2) v = None"
        by (simp add: refEOf_def)
      then show "refEOf (F1 \<union>\<^sub>F F2) v = (refEOf F1 ++ refEOf F2) v"
        using \<open>v \<notin> NsP (fsg F1 USG fsg F2)\<close>
        by (simp add: h)(simp add: refEOf_def)
    qed
  qed
qed

(*References relation restricted to local references*)
definition refsL :: "'a Fr_scheme \<Rightarrow> (V \<rightharpoonup> V)"
  where
  "refsL F \<equiv> (refs F) \<rhd>\<^sub>m (flNs F)"

(*Unresolved references edges of a fragment*)
definition uRefEs :: "'a Fr_scheme \<Rightarrow> E set"
  where
  "uRefEs F \<equiv> dom ((sr F) \<unrhd>\<^sub>m dom (refsL F))"

(*Resolves a fragment's SG*)
definition fresolveSG ::  "'a Fr_scheme \<Rightarrow> SGr" ("(\<Odot>\<^sup>S\<^sup>G_)" [1000] 999)
  where
  "\<Odot>\<^sup>S\<^sup>G F = (fsg F) \<odot>\<^sup>S\<^sup>G (refsL F)"

(*Resolves a fragment*)
definition fresolve ::"'a Fr_scheme \<Rightarrow> Fr" ("(\<Odot>_)" [1000] 999)
  where
  "\<Odot> F = consF (\<Odot>\<^sup>S\<^sup>G F) (uRefEs F) ((sr F) |` (uRefEs F)) ((tr F) |` (uRefEs F))"

definition wf_fa::"'a Fr_scheme \<Rightarrow>bool"
where
  "wf_fa F \<equiv> wf_fz F \<and> acyclicGr (refsG F)"

definition wf_f::"'a Fr_scheme \<Rightarrow>bool"
where
  "wf_f F \<equiv> wf_fa F \<and> wf_sg (\<Odot>\<^sup>S\<^sup>G F)"

definition refsLocal::"'a Fr_scheme \<Rightarrow>bool"
  where
  "refsLocal F \<equiv> fRNs F \<subseteq> flNs F"

definition wf_tf::"'a Fr_scheme \<Rightarrow>bool"
  where
  "wf_tf F \<equiv> wf_fa F \<and> refsLocal F \<and> wf_tsg (\<Odot>\<^sup>S\<^sup>G F)"

lemma wf_fa_wf_fz:
  assumes "wf_fa F"
  shows "wf_fz F"
  using assms
  by (simp add: wf_fa_def)

lemma wf_f_wf_fa:
  assumes "wf_f F"
  shows "wf_fa F"
  using assms
  by (simp add: wf_f_def)

lemma wf_f_wf_sg:
  assumes "wf_f F"
  shows "wf_sg (fsg F)"
  using assms
  by (simp add: wf_f_def wf_fa_def wf_fz_def)

lemma wf_tf_wf_fa:
  assumes "wf_tf F"
  shows "wf_fa F"
  using assms
  by (simp add: wf_tf_def)

lemma wf_tf_refsLocal:
  assumes "wf_tf F"
  shows "refsLocal F"
  using assms by (simp add: wf_tf_def)


definition frefs_in::"'a Fr_scheme \<Rightarrow>'a Fr_scheme \<Rightarrow> bool" (infixl "\<subseteq>\<^sup>r\<^sup>s" 100) 
  where
  "F1 \<subseteq>\<^sup>r\<^sup>s F2 \<equiv> ran (tr F1) \<inter> fNs F2 \<noteq> {}"

definition refs_from_to::"'a Fr_scheme \<Rightarrow>'a Fr_scheme \<Rightarrow> bool" (infixl "\<Rightarrow>\<^sup>r\<^sup>s" 100)
  where
  "F1 \<Rightarrow>\<^sup>r\<^sup>s F2 \<equiv> F1 \<subseteq>\<^sup>r\<^sup>s F2 \<and> \<not>(F2 \<subseteq>\<^sup>r\<^sup>s F1)"

lemma flEs_UF: 
  shows "flEs (F1 \<union>\<^sub>F F2) = flEs F1 \<union> flEs F2"
  by (simp add: cupF_def flEs_def disj_fs_def 
      wf_fz_def ftotal_on_def cupSG_def) 

lemma flNs_UF: 
  shows "flNs (F1 \<union>\<^sub>F F2) = flNs F1 \<union> flNs F2"
  by (simp add: cupF_def flNs_def disj_fs_def 
      wf_fz_def ftotal_on_def cupSG_def) 

lemma fRNs_UF: 
  assumes "wf_fz F1" and "wf_fz F2" and "disj_fs F1 F2"
  shows "fRNs (F1 \<union>\<^sub>F F2) = fRNs F1 \<union> fRNs F2"
  using assms
  ran_map_add[of "tr F1" "tr F2"]
  by (auto simp add: cupF_def fRNs_def disj_fs_def 
      wf_fz_def ftotal_on_def fEs_def)  

lemma refsG_UF:
  assumes "wf_fa F1" and "wf_fa F2" and "disj_fs F1 F2"
  shows "refsG (F1 \<union>\<^sub>F F2) = refsG F1 UG refsG F2"
  using assms wf_fa_wf_fz[of F1]  wf_fa_wf_fz[of F2] 
    wf_fz_wf_sg[of F1] wf_fz_wf_sg[of F2]
    NsP_USG[of "fsg F1" "fsg F2"] fRNs_UF[of F1 F2]
    disj_fs_imp_disj_Gs
  by (auto simp add: refsG_def disj_fs_def cupG_def consG_def)

lemma wf_refsG:
  assumes "wf_fa F"
  shows "wf_g (refsG F)"
  using assms wf_fa_wf_fz[of F] wf_fz_wf_sg[of F]
    wf_fz_wf_sg[of F] wf_sg_wf_g[of "fsg F"]
proof (simp add: refsG_def wf_g_def consG_def)
  apply_end(rule conjI)
  show "NsP (fsg F) \<subseteq> V_A"
    using assms wf_fa_wf_fz[of F] wf_fz_wf_sg[of F]
    wf_sg_wf_g[of "fsg F"] 
    NsP_sub_Ns[of "fsg F"]
    by (auto simp add: wf_g_def wf_fz_def)
next
  apply_end(rule conjI)
  show "fRNs F \<subseteq> V_A"
    using assms wf_fa_wf_fz[of F]
    by (auto simp add: wf_fz_def fRNs_def ftotal_on_def)
next
  apply_end(rule conjI)
  show "esr F \<subseteq> E_A"
    using assms wf_fa_wf_fz[of F]
    by (simp add: wf_fz_def)
next
  apply_end(rule conjI)
  show "ftotal_on (tr F) (esr F) (NsP (fsg F) \<union> fRNs F)"
    using assms wf_fa_wf_fz[of F] wf_fz_wf_sg[of F]
    NsP_sub_Ns[of "fsg F"]
    by (simp add: ftotal_on_def consG_def wf_fz_def 
        fbij_on_def finj_on_def fRNs_def)
next
  show "ftotal_on (sr F) (esr F) (NsP (fsg F) \<union> fRNs F)"
  using assms wf_fa_wf_fz[of F] wf_fz_wf_sg[of F]
    NsP_sub_Ns[of "fsg F"]
    by (simp add: ftotal_on_def consG_def wf_fz_def 
        fbij_on_def finj_on_def fRNs_def)
qed

lemma wf_fa_acyclicGr_refsG:
  assumes "wf_fa F"
  shows "acyclicGr (refsG F)"
  using assms by (simp add: wf_fa_def)

lemma disj_fs_imp_disjEsGs_RefsGs:
  assumes "disj_fs F1 F2"
  shows "disjEsGs (refsG F1) (refsG F2)"
  using assms
  by (auto simp add: refsG_def consG_def fRNs_def disjEsGs_def 
      disj_fs_def flNs_def fEs_def flEs_def)

lemma Domain_RefsG_eq_NsPSG:
  assumes "wf_fa F"
  shows "Domain ((refsG F)\<^sup>\<Leftrightarrow>) = NsP (fsg F)"
proof
  show "Domain ((refsG F)\<^sup>\<Leftrightarrow>) \<subseteq> NsP (fsg F)"
  using assms wf_fa_wf_fz[of F] wf_fz_wf_sg[of F]
    wf_fz_sr_bij[of F] 
    by (auto simp add: fbij_on_def relG_def adjacent_def refsG_def
        consG_def finj_on_def ftotal_on_def intro: ranI)
next
  show "NsP (fsg F) \<subseteq> Domain ((refsG F)\<^sup>\<Leftrightarrow>)"
  proof
    fix x
    assume "x \<in> NsP (fsg F)"
    hence "x \<in> ran (sr F)" 
      using assms wf_fz_sr_bij[of F] 
      by (simp add: wf_fa_def fbij_on_def)
    then obtain e where "e \<in> esr F \<and> sr F e = Some x" 
      using assms wf_fa_wf_fz[of F] wf_fz_sr_bij[of F] 
      by (auto simp add: ran_def fbij_on_def finj_on_def ftotal_on_def)
    then obtain v where "tr F e = Some v" 
      using assms wf_fa_wf_fz[of F] wf_fz_tr_ftotal[of F]
      by (auto simp add: ftotal_on_def)
    show "x \<in> Domain ((refsG F)\<^sup>\<Leftrightarrow>)"
      using \<open>e \<in> esr F \<and> sr F e = Some x\<close> \<open>tr F e = Some v\<close>
      by (auto simp add: relG_def adjacent_def refsG_def consG_def)
  qed
qed

lemma Range_RefsG_eq_fRNs:
  assumes "wf_fa F"
  shows "Range ((refsG F)\<^sup>\<Leftrightarrow>) = fRNs F"
proof
  show "Range ((refsG F)\<^sup>\<Leftrightarrow>) \<subseteq> fRNs F"
  using assms wf_fa_wf_fz[of F] wf_fz_wf_sg[of F]
    wf_fz_sr_bij[of F] 
    by (auto simp add: fbij_on_def relG_def adjacent_def refsG_def
        consG_def fRNs_def intro: ranI)
next
  show "fRNs F \<subseteq> Range ((refsG F)\<^sup>\<Leftrightarrow>)"
  proof
    fix x
    assume "x \<in> fRNs F"
    then obtain e where "e \<in> esr F \<and> tr F e = Some x" 
      using assms wf_fa_wf_fz[of F] wf_fz_tr_ftotal[of F]
      by (auto simp add: fRNs_def ran_def ftotal_on_def)
    hence "e \<in> dom (sr F)" 
      using assms wf_fa_wf_fz[of F] wf_fz_sr_bij[of F]
      by (auto simp add: fbij_on_def finj_on_def 
          ftotal_on_def)
    then obtain v where "sr F e = Some v" 
      using assms 
      by (auto simp add: domD)
    then show "x \<in> Range ((refsG F)\<^sup>\<Leftrightarrow>)"
      using \<open>e \<in> esr F \<and> tr F e = Some x\<close>
      by (auto simp add: refsG_def consG_def fRNs_def relG_def
          adjacent_def)
  qed
qed

lemma refs_from_to_implies:
  assumes "wf_fa F2" and "F1 \<Rightarrow>\<^sup>r\<^sup>s F2"
  shows "(fRNs F2) \<inter> (fNs F1) = {}"
proof (rule ccontr)
  assume h: "(fRNs F2) \<inter> (fNs F1) \<noteq> {}"
  then obtain x where "x \<in> (fRNs F2) \<inter> (fNs F1)"
    by auto
  hence "x \<in> fRNs F2" by auto
  hence "x \<notin> fNs F1"
    using assms(2) by (auto simp add: refs_from_to_def frefs_in_def
        fRNs_def fNs_def)
  then show "False"
    using \<open>x \<in> (fRNs F2) \<inter> (fNs F1)\<close> by auto
qed
  
lemma acyclic_UF: 
  assumes "wf_fa F1" and "wf_fa F2" and "disj_fs F1 F2" and "F1 \<Rightarrow>\<^sup>r\<^sup>s F2"
  shows "acyclicGr (refsG (F1 \<union>\<^sub>F F2)) = (acyclicGr (refsG F1) \<and> acyclicGr (refsG F2))"
proof
  assume "acyclicGr (refsG (F1 \<union>\<^sub>F F2))"
  then show "acyclicGr (refsG F1) \<and> acyclicGr (refsG F2)"
    using assms wf_refsG[of F1] wf_refsG[of F2] 
      disj_fs_imp_disjEsGs_RefsGs[of F1 F2] 
    by (simp add: acyclic_Gr_UG_disj_imp_acylic_Grs refsG_UF)
next
  apply_end(clarsimp)
  assume h1: "acyclicGr (refsG F1)" and h2: "acyclicGr (refsG F2)"
  from h1 have "acyclic ((refsG F1)\<^sup>\<Leftrightarrow>)" 
    by (simp add: acyclic_Gr_iff_acyclic_relG)
  from h2 have "acyclic ((refsG F2)\<^sup>\<Leftrightarrow>)" 
    by (simp add: acyclic_Gr_iff_acyclic_relG)
  have "Domain ((refsG F1)\<^sup>\<Leftrightarrow>) \<inter> Domain ((refsG F2)\<^sup>\<Leftrightarrow>) = {}"
    using assms wf_fa_wf_fz[of F1] wf_fa_wf_fz[of F2] 
     wf_fz_wf_sg[of F1] wf_fz_wf_sg[of F2] 
     NsP_sub_Ns[of "fsg F1"] NsP_sub_Ns[of "fsg F2"]
     Domain_RefsG_eq_NsPSG[of F1] Domain_RefsG_eq_NsPSG[of F2]
     ns_disj_Ga_Gb[of "fsg F1" "fsg F2"]
     disj_fs_imp_disj_Gs[of F1 F2]
    by (auto simp add: disj_fs_def flNs_def)
  have "Range ((refsG F2)\<^sup>\<Leftrightarrow>) \<inter> Domain ((refsG F1)\<^sup>\<Leftrightarrow>) = {}"
  proof (rule ccontr)
    assume "Range ((refsG F2)\<^sup>\<Leftrightarrow>) \<inter> Domain ((refsG F1)\<^sup>\<Leftrightarrow>) \<noteq> {}"
    then obtain x where "x \<in> Range ((refsG F2)\<^sup>\<Leftrightarrow>) \<inter> Domain ((refsG F1)\<^sup>\<Leftrightarrow>)"
      by auto
    hence "x \<in> (fRNs F2)" 
      using assms(2) 
      by (simp add: Range_RefsG_eq_fRNs)
    have "x \<in> (fNs F1)"
      using \<open>x \<in> Range ((refsG F2)\<^sup>\<Leftrightarrow>) \<inter> Domain ((refsG F1)\<^sup>\<Leftrightarrow>)\<close> 
      assms(1) assms(2) NsP_sub_Ns[of "fsg F1"] 
      wf_fa_wf_fz[of F1] wf_fz_wf_sg[of F1]
      by (auto simp add: Domain_RefsG_eq_NsPSG fNs_def
          flNs_def)
    then show "False"
      using assms(2) assms(4) refs_from_to_implies[of F2 F1] 
      \<open>x \<in> (fRNs F2)\<close> 
      by auto
  qed
  hence "acyclic (((refsG F1)\<^sup>\<Leftrightarrow>) \<union> ((refsG F2)\<^sup>\<Leftrightarrow>))"
    using \<open>Domain ((refsG F1)\<^sup>\<Leftrightarrow>) \<inter> Domain ((refsG F2)\<^sup>\<Leftrightarrow>) = {}\<close>
    \<open>acyclic ((refsG F1)\<^sup>\<Leftrightarrow>)\<close> \<open>acyclic ((refsG F2)\<^sup>\<Leftrightarrow>)\<close> 
    by (simp add: acyclic_Un)
  then show "acyclicGr (refsG (F1 \<union>\<^sub>F F2))"
    using assms relG_UG wf_refsG[of F1] wf_refsG[of F2]
    disj_fs_imp_disjEsGs_RefsGs[of F1 F2]
  by (simp add: refsG_UF acyclic_Gr_iff_acyclic_relG 
       relG_UG)
qed

lemma wfz_UF: 
  assumes "wf_fz F1" and "wf_fz F2" and "disj_fs F1 F2"
    and "F1 \<Rightarrow>\<^sup>r\<^sup>s F2"
  shows "wf_fz (F1 \<union>\<^sub>F F2)"
proof (simp add: wf_fz_def)
  apply_end(rule conjI)
  show "wf_sg (fsg F1 USG fsg F2)"
    using assms wf_fz_wf_sg[of F1] wf_fz_wf_sg[of F2]
    disj_fs_imp_disj_Gs[of F1 F2]
    by (simp add: is_wf_sg_Un disj_fs_def)
next
  apply_end(rule conjI)
  show "esr F1 \<subseteq> E_A"
    using assms(1) by (simp add: wf_fz_def)
next
  apply_end(rule conjI)
  show "esr F2 \<subseteq> E_A"
    using assms(2) by (simp add: wf_fz_def)
next
  apply_end(rule conjI)
  have h: "(esr F1 \<union> esr F2) \<inter> flEs (F1 \<union>\<^sub>F F2) =
    (esr F1 \<inter> flEs (F1 \<union>\<^sub>F F2)) \<union> (esr F2 \<inter> flEs (F1 \<union>\<^sub>F F2))" 
    by auto
  show "(esr F1 \<union> esr F2) \<inter> flEs (F1 \<union>\<^sub>F F2) = {}"
  proof (rule ccontr)
    assume "(esr F1 \<union> esr F2) \<inter> flEs (F1 \<union>\<^sub>F F2) \<noteq> {}"
    hence "(esr F1 \<inter> flEs (F1 \<union>\<^sub>F F2)) \<union> (esr F2 \<inter> flEs (F1 \<union>\<^sub>F F2)) \<noteq> {}"
      using h by auto
    then obtain x where "x \<in> (esr F1 \<inter> flEs (F1 \<union>\<^sub>F F2)) \<union> (esr F2 \<inter> flEs (F1 \<union>\<^sub>F F2))"
      by auto
    hence "x \<in> (esr F1 \<inter> flEs (F1 \<union>\<^sub>F F2)) \<or> x \<in> (esr F2 \<inter> flEs (F1 \<union>\<^sub>F F2))" 
    using assms(1) assms(2)
    by (simp add: flEs_UF wf_fz_def)
  then show "False" 
    using flEs_UF[of F1 F2] assms(1) assms(2)
      assms(3)
      wf_fz_disj_esr_fles[of F1] disj_fs_imp_disj_Gs[of F1 F2]
      wf_fz_disj_esr_fles[of F2]
      by (auto simp add: disj_fs_def flEs_def fEs_def)
  qed
next
  apply_end(rule conjI)
  have "disjoint [esr F1, esr F2, NsP (fsg F1), NsP (fsg F2)]"
    using assms wf_fz_wf_sg[of F1] wf_fz_wf_sg[of F2] 
      NsP_sub_Ns[of "fsg F1"]  NsP_sub_Ns[of "fsg F2"] 
      wf_fz_disj_esr_fles[of F1] wf_fz_disj_esr_fles[of F2]
      wf_fz_esr_sub_EA[of F1] wf_fz_esr_sub_EA[of F2]
      disj_V_E wf_sg_wf_g[of "fsg F1"] wf_sg_wf_g[of "fsg F2"]
    by (force simp add: disj_fs_def flNs_def flEs_def fEs_def
        wf_g_def)
  show "fbij_on (sr F1 ++ sr F2) (esr F1 \<union> esr F2)
     (NsP (fsg F1 USG fsg F2))"
    using assms wf_fz_sr_bij[of F1]
       wf_fz_sr_bij[of F2] wf_fz_wf_sg[of F1]
       wf_fz_wf_sg[of F2] disj_fs_imp_disj_Gs[of F1 F2]
       \<open>disjoint [esr F1, esr F2, NsP (fsg F1), NsP (fsg F2)]\<close>
      fbij_on_dist_map_add[of "sr F1" "esr F1" "NsP (fsg F1)" 
        "sr F2" "esr F2" "NsP (fsg F2)"] 
    by (auto simp add: NsP_USG)
next
  have "esr F1 \<inter> esr F2 = {}"
    using assms(3) by (auto simp add:  disj_fs_def fEs_def flEs_def)
  then show " ftotal_on (tr F1 ++ tr F2) (esr F1 \<union> esr F2) V_A"
    using assms wf_fz_tr_ftotal[of F1] wf_fz_wf_sg[of F1] 
      wf_fz_wf_sg[of F2] wf_fz_tr_ftotal[of F2] 
      NsO_USG[of "fsg F1" "fsg F2"]
      ftotal_on_map_add[of "tr F1" "esr F1" "V_A" "tr F2" "esr F2" "V_A"] 
    by (simp add: disj_fs_imp_disj_Gs ftotal_on_def)
qed

lemma wfa_UF: 
  assumes "wf_fa F1" and "wf_fa F2" and "disj_fs F1 F2"
    and "F1 \<Rightarrow>\<^sup>r\<^sup>s F2"
  shows "wf_fa (F1 \<union>\<^sub>F F2)"
proof (simp add: wf_fa_def)
  apply_end(rule conjI)
  show "wf_fz (F1 \<union>\<^sub>F F2)"
    using assms wf_fa_wf_fz[of F1] wf_fa_wf_fz[of F2]
    by (simp add: wfz_UF)
next
  show "acyclicGr (refsG (F1 \<union>\<^sub>F F2))"
    using assms  wf_fa_acyclicGr_refsG[of F1]
      wf_fa_acyclicGr_refsG[of F2]
    by (simp add: acyclic_UF)
qed

lemma wf_tf_ran_refsF_Ns_SG:
  assumes "wf_tf F"
  shows "ran (refs F) \<subseteq> Ns (fsg F)"
  using assms wf_tf_refsLocal[of F]
  by (auto simp add: refs_def fRNs_def refsLocal_def 
      flNs_def subset_eq ran_def split: if_splits)

lemma dom_refs_disj:
  assumes "wf_fz F1" and "wf_fz F2" and h3: "disj_fs F1 F2"
  shows "dom (refs F1) \<inter> dom (refs F2) = {}"
  using assms wf_fz_wf_sg[of F1] wf_fz_wf_sg[of F2]  
    dom_refsF[of F1] dom_refsF[of F2] 
    disj_fs_imp_disj_Gs[of F1 F2]
    NsP_sub_Ns[of "fsg F1"] NsP_sub_Ns[of "fsg F2"]
  by (auto simp add: disjGs_def)
  
lemma refs_UF:
  assumes "wf_f F1" and "wf_f F2" and h3: "disj_fs F1 F2"
  shows "refs (F1 \<union>\<^sub>F F2) = refs F1 ++ refs F2"
proof
  fix v
  show "refs (F1 \<union>\<^sub>F F2) v = (refs F1 ++ refs F2) v"
  proof (case_tac "v \<in> NsP (fsg F1 USG fsg F2)")
    assume "v \<in> NsP (fsg F1 USG fsg F2)"
    hence "v \<in> NsP (fsg F1) \<or> v \<in> NsP (fsg F2)"
      using assms wf_f_wf_fa[of F1] wf_f_wf_fa[of F2] 
        wf_fa_wf_fz[of F1] wf_fa_wf_fz[of F2] 
        wf_fz_wf_sg[of F1] wf_fz_wf_sg[of F2] 
        NsP_USG[of "fsg F1" "fsg F2"]
      by (simp add: refs_def disj_fs_imp_disj_Gs)
    then show "refs (F1 \<union>\<^sub>F F2) v = (refs F1 ++ refs F2) v"
    proof
      assume "v \<in> NsP (fsg F1)"
      have h: "(refs F1 ++ refs F2) v = refs F1 v"
        using assms dom_refsF[of F1] wf_f_wf_fa[of F1] 
          wf_fa_wf_fz[of F1] wf_f_wf_fa[of F2] 
          wf_fa_wf_fz[of F2] dom_refs_disj[of F1 F2]
          map_add_disj_domf[of "refs F1" "refs F2" v]
          \<open>v \<in> NsP (fsg F1)\<close>
        by (simp)
      show "refs (F1 \<union>\<^sub>F F2) v = (refs F1 ++ refs F2) v"
        using assms wf_f_wf_fa[of F1] wf_fa_wf_fz[of F1]
        wf_f_wf_fa[of F2] wf_fa_wf_fz[of F2]
        \<open>v \<in> NsP (fsg F1 USG fsg F2)\<close> \<open>v \<in> NsP (fsg F1)\<close>
        by (simp add: h)
          (simp add: refs_def refEOf_UF refEOf_map_add_f
            tr_map_addrefEOf_f split: option.splits)
    next
      assume "v \<in> NsP (fsg F2)"
      hence "v \<in> dom (refs F2)"
        using assms dom_refsF[of F2] 
          wf_f_wf_fa[of F2] wf_fa_wf_fz[of F2] 
        by auto
      hence h: "(refs F1 ++ refs F2) v = refs F2 v"
        by (simp add: map_add_dom_app_simps(1))
      have "v \<in> dom(refEOf F2)"
        using \<open>v \<in> NsP (fsg F2)\<close> assms(2)
        by (simp add:  dom_refEOf_eq_NsP wf_f_wf_fa wf_fa_wf_fz)
      have "the (refEOf F2 v) \<in> dom (tr F2)"
        using assms(2) wf_f_wf_fa[of F2] wf_fa_wf_fz[of F2]
          \<open>v \<in> NsP (fsg F2)\<close> refEOfIsFLE[of F2 v]
          wf_fz_tr_ftotal[of F2]
        by (simp add: ftotal_on_dom)
      then show "refs (F1 \<union>\<^sub>F F2) v = (refs F1 ++ refs F2) v"
        using assms wf_f_wf_fa[of F1] wf_fa_wf_fz[of F1]
        wf_f_wf_fa[of F2] wf_fa_wf_fz[of F2]
          \<open>v \<in> NsP (fsg F1 USG fsg F2)\<close> \<open>v \<in> NsP (fsg F2)\<close>
          \<open>v \<in> dom(refEOf F2)\<close>
        by (simp add: h)
          (simp add: refs_def refEOf_UF map_add_dom_app_simps(1))
    qed
  next
    assume "v \<notin> NsP (fsg F1 USG fsg F2)"
    hence "v \<notin> NsP (fsg F1) \<and> v \<notin> NsP (fsg F2)"
      using assms wf_f_wf_fa[of F1] wf_fa_wf_fz[of F1] 
       wf_fz_wf_sg[of F1] wf_f_wf_fa[of F2] wf_fa_wf_fz[of F2] 
       wf_fz_wf_sg[of F2] disj_fs_imp_disj_Gs[of F1 F2]
      by (simp add: NsP_USG)
    then show "refs (F1 \<union>\<^sub>F F2) v = (refs F1 ++ refs F2) v"
      using \<open>v \<notin> NsP (fsg F1 USG fsg F2)\<close>
      by (simp add: refs_def map_add_dom_app_simps(3) domIff)
  qed
qed

lemma wff_refsL_partial:
  assumes "wf_f F" 
  shows "fpartial_on (refsL F) (NsP (fsg F)) (Ns (fsg F))"
proof (simp add: fpartial_on_def)
  apply_end(rule conjI)
  show "dom (refsL F) \<subseteq> NsP (fsg F)"
    using assms wf_f_wf_fa[of F] wf_fa_wf_fz[of F]
    dom_refsF[of F] dom_mrres_sub_dom[of "refs F" "flNs F"]
    by (simp add: refsL_def)
next
  show "ran (refsL F) \<subseteq> Ns (fsg F)"
    using assms mrres_ran_sub1[of "refs F" "flNs F"]
    by (simp add: refsL_def mrres_ran_sub2 flNs_def)
qed


lemma wf_ufs_refsL_partial:
  assumes "wf_f F1" and  "wf_f F2"  and "disj_fs F1 F2" 
  shows "fpartial_on (refsL (F1 \<union>\<^sub>F F2)) (NsP (fsg (F1 \<union>\<^sub>F F2))) (Ns (fsg (F1 \<union>\<^sub>F F2)))"
proof (simp add: fpartial_on_def)
  apply_end(rule conjI)
  have "dom (refs F2) \<union> dom (refs F1) \<subseteq> NsP (fsg F1) \<union> NsP (fsg F2)"
    using assms(1) assms(2)
    by (simp add:  dom_refsF wf_f_wf_fa wf_fa_wf_fz)
  then show "dom (refsL (F1 \<union>\<^sub>F F2)) \<subseteq> NsP (fsg F1 USG fsg F2)"
    using assms wf_f_wf_fa[of F1] wf_fa_wf_fz[of F1] 
      wf_fz_wf_sg[of F1] wf_f_wf_fa[of F2] wf_fa_wf_fz[of F2] 
      wf_fz_wf_sg[of F2] disj_fs_imp_disj_Gs[of F1 F2] 
      dom_mrres_sub_dom[of "refs F1 ++ refs F2" "flNs F1 \<union> flNs F2"]
    by (force simp add: refsL_def NsP_USG refs_UF flNs_UF)
next
  show "ran (refsL (F1 \<union>\<^sub>F F2)) \<subseteq> Ns (fsg F1) \<union> Ns (fsg F2)"
    using assms 
      mrres_ran_sub1[of "refs F1 ++ refs F2" "(flNs F1 \<union> flNs F2)"]
    by (simp add: refsL_def refs_UF flNs_UF flNs_def)
qed

(*lemma wf_sg_fresolveSG:
  assumes "wf_f F1" and "wf_f F2" and "disj_fs F1 F2" 
    and "F1 \<Rightarrow>\<^sup>r\<^sup>s F2"
  shows "wf_sg(\<Odot>\<^sup>S\<^sup>G(F1 \<union>\<^sub>F F2))"
proof (simp add: wf_sg_def)
  apply_end(rule conjI)
  show "wf_g (\<Odot>\<^sup>S\<^sup>G(F1 \<union>\<^sub>F F2))"
    using assms(1) assms(2) assms(3) wf_f_wf_fa[of F1]
       wf_fa_wf_fz[of F1] wf_fz_wf_sg[of F1]
      wf_f_wf_fa[of F2]
       wf_fa_wf_fz[of F2] wf_fz_wf_sg[of F2] disj_fs_imp_disj_Gs[of F1 F2]
      wf_g_subsumeSG[of "fsg F1 USG fsg F2" "refsL (F1 \<union>\<^sub>F F2)"]
      is_wf_sg_Un[of "fsg F1" "fsg F2"]
      wf_ufs_refsL_partial
    by (simp add: fresolveSG_def )
next
  apply_end(rule conjI)
  show "ftotal_on (nty (\<Odot>\<^sup>S\<^sup>G(F1 \<union>\<^sub>F F2))) (Ns (\<Odot>\<^sup>S\<^sup>G(F1 \<union>\<^sub>F F2)))
     SGNT_set"
    using assms(1) assms(2) assms(3) wf_f_wf_fa[of F1]
       wf_fa_wf_fz[of F1] wf_fz_wf_sg[of F1]
       wf_f_wf_fa[of F2]
       wf_fa_wf_fz[of F2] wf_fz_wf_sg[of F2]
       disj_fs_imp_disj_Gs[of F1 F2]
       is_wf_sg_Un[of "fsg F1" "fsg F2"]
       ftotal_on_nty_subsumeSG[of "fsg F1 USG fsg F2" "refsL (F1 \<union>\<^sub>F F2)"]
       wf_ufs_refsL_partial
    by (simp add: fresolveSG_def )
next
  apply_end(rule conjI)
  show "ftotal_on (ety (\<Odot>\<^sup>S\<^sup>G(F1 \<union>\<^sub>F F2))) (Es (\<Odot>\<^sup>S\<^sup>G(F1 \<union>\<^sub>F F2)))
     SGET_set"
    using assms(1) assms(2) assms(3) wf_f_wf_fa[of F1]
       wf_fa_wf_fz[of F1] wf_fz_wf_sg[of F1]
       wf_f_wf_fa[of F2]
       wf_fa_wf_fz[of F2] wf_fz_wf_sg[of F2]
       disj_fs_imp_disj_Gs[of F1 F2]
       is_wf_sg_Un[of "fsg F1" "fsg F2"]
       ftotal_on_ety_subsumeSG[of "fsg F1 USG fsg F2" "refsL (F1 \<union>\<^sub>F F2)"]
       wf_ufs_refsL_partial
    by (simp add: fresolveSG_def )
next
  apply_end(rule conjI)
  show "ftotal_on (srcma (\<Odot>\<^sup>S\<^sup>G(F1 \<union>\<^sub>F F2))) (EsC (\<Odot>\<^sup>S\<^sup>G(F1 \<union>\<^sub>F F2)))
     MultC_set"
  using assms(1) assms(2) assms(3) wf_f_wf_fa[of F1]
       wf_fa_wf_fz[of F1] wf_fz_wf_sg[of F1]
       wf_f_wf_fa[of F2]
       wf_fa_wf_fz[of F2] wf_fz_wf_sg[of F2]
       disj_fs_imp_disj_Gs[of F1 F2]
       is_wf_sg_Un[of "fsg F1" "fsg F2"]
       ftotal_on_srcma_subsumeSG[of "fsg F1 USG fsg F2" "refsL (F1 \<union>\<^sub>F F2)"]
       wf_ufs_refsL_partial
  by (simp add: fresolveSG_def )
next
  apply_end(rule conjI)
  show "ftotal_on (tgtm (\<Odot>\<^sup>S\<^sup>G(F1 \<union>\<^sub>F F2))) (EsC (\<Odot>\<^sup>S\<^sup>G(F1 \<union>\<^sub>F F2)))
     MultC_set"
  using assms(1) assms(2) assms(3) wf_f_wf_fa[of F1]
       wf_fa_wf_fz[of F1] wf_fz_wf_sg[of F1]
       wf_f_wf_fa[of F2]
       wf_fa_wf_fz[of F2] wf_fz_wf_sg[of F2]
       disj_fs_imp_disj_Gs[of F1 F2]
       is_wf_sg_Un[of "fsg F1" "fsg F2"]
       ftotal_on_tgtm_subsumeSG[of "fsg F1 USG fsg F2" "refsL (F1 \<union>\<^sub>F F2)"]
       wf_ufs_refsL_partial
  by (simp add: fresolveSG_def )
next
  apply_end(rule conjI)
  show "dom (db (\<Odot>\<^sup>S\<^sup>G(F1 \<union>\<^sub>F F2))) = EsD (\<Odot>\<^sup>S\<^sup>G(F1 \<union>\<^sub>F F2))"
  using assms(1) assms(2) assms(3) wf_f_wf_fa[of F1]
       wf_fa_wf_fz[of F1] wf_fz_wf_sg[of F1]
       wf_f_wf_fa[of F2]
       wf_fa_wf_fz[of F2] wf_fz_wf_sg[of F2]
       disj_fs_imp_disj_Gs[of F1 F2]
       is_wf_sg_Un[of "fsg F1" "fsg F2"]
       dom_db_eq_EsD_subsumeSG[of "fsg F1 USG fsg F2" "refsL (F1 \<union>\<^sub>F F2)"]
       wf_ufs_refsL_partial
  by (simp add: fresolveSG_def )
next
  apply_end(rule conjI)
  show "multsOk (\<Odot>\<^sup>S\<^sup>G(F1 \<union>\<^sub>F F2))"
  using assms(1) assms(2) assms(3) wf_f_wf_fa[of F1]
       wf_fa_wf_fz[of F1] wf_fz_wf_sg[of F1]
       wf_f_wf_fa[of F2]
       wf_fa_wf_fz[of F2] wf_fz_wf_sg[of F2]
       disj_fs_imp_disj_Gs[of F1 F2]
       is_wf_sg_Un[of "fsg F1" "fsg F2"]
       multsOk_subsumeSG[of "fsg F1 USG fsg F2" "refsL (F1 \<union>\<^sub>F F2)"]
       wf_ufs_refsL_partial
  by (simp add: fresolveSG_def )
next
  
lemma wf_U_Frs_1: 
  assumes "wf_f F1" and "wf_f F2" and "disj_fs F1 F2" 
    and "F1 \<Rightarrow>\<^sup>r\<^sup>s F2"
  shows "wf_f (F1 \<union>\<^sub>F F2)"
proof (simp add: wf_f_def)
  apply_end(rule conjI)
  show " wf_fa (F1 \<union>\<^sub>F F2)"
    using assms by (simp add: wf_f_def wfa_UF)
next
  show "wf_sg (\<Odot>\<^sup>S\<^sup>G(F1 \<union>\<^sub>F F2))"  
qed*)



(*definition morphFr :: "Fr \<Rightarrow> Fr \<Rightarrow> Morph set"
where
  "morphFr F1 F2 \<equiv> {r. wf_f F1 \<and> is_wf_f F2
      \<and> ftotal_on (fV r) (Ns (sg F1)) (Ns (sg F2)) 
      \<and> ftotal_on (fE r) (Es (sg F1)) (Es (sg F2))  
      \<and> srcstF F1 O pfunToRel(fV r)  \<subseteq> pfunToRel(fE r) O srcstF F2
      \<and> tgtstF F1 O pfunToRel(fV r)  \<subseteq> pfunToRel(fE r) O tgtstF F2
      \<and> inhstF F1 O pfunToRel(fV r)  \<subseteq> pfunToRel(fV r) O inhstF F2}"
*)

end
