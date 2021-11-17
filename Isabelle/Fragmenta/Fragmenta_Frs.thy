(*  Title:       Fragmenta theory of Fragments (Frs)
    Description: 'Fragmenta' theory presented in the Models 2015 paper.
    Author:      Nuno Amálio
*)
theory Fragmenta_Frs
imports Fragmenta_SGs "../Extra/Rel_Extra" 
                    
begin

(*Fragments*)      
record Fr = 
  sg :: "SGr"
  tr :: "E \<rightharpoonup> V"

(*Set of all fragments*)
definition is_fr :: "Fr \<Rightarrow> bool"
where
  "is_fr F \<equiv> True"

definition fr_set :: "Fr set"
where
  "fr_set \<equiv> {F. is_fr F}"

(* Defines the empty Fr*)
definition emptyFr :: "Fr"
where
  "emptyFr \<equiv> \<lparr>sg = emptySG, tr = empty\<rparr>"

lemma Fr_eq: 
  shows "(F1 = F2) \<longleftrightarrow> sg F1 = sg F2 \<and> tr F1 = tr F2 \<and> Fr.more F1 = Fr.more F2"
    by (auto)

(*Target function with directed references*)
definition tgtr :: "'a Fr_scheme \<Rightarrow> E \<rightharpoonup> V"
where
  "tgtr F \<equiv> tgt (sg F) ++ (tr F)"

(*Yields the fragment's graph but filled with the references of proxies*)
definition withRsG :: "'a Fr_scheme \<Rightarrow> Gr"
where
  "withRsG F \<equiv> \<lparr>Ns = Ns (sg F) \<union> ran (tr F), Es = Es (sg F), src = src (sg F),
    tgt = tgtr F\<rparr>"

lemma Ns_withRsG[simp]: "Ns (withRsG F) = Ns (sg F) \<union> ran (tr F)"
  by (simp add: withRsG_def)

lemma Es_withRsG[simp]: "Es (withRsG F) = Es (sg F)"
  by (simp add: withRsG_def)

lemma src_withRsG[simp]: "src (withRsG F) = src (sg F)"
  by (simp add: withRsG_def)

lemma tgt_withRsG[simp]: "tgt (withRsG F) = tgtr F"
  by (simp add: withRsG_def)

(*Yields graph of proxies and their references*)
definition refsG :: "'a Fr_scheme \<Rightarrow> Gr"
where
  "refsG F \<equiv> restrict (withRsG F) (EsRP (sg F))"

lemma Ns_refsG[simp]: "Ns (refsG F) = rst_Ns (withRsG F) (EsRP (sg F))"
  by (auto simp add: refsG_def)

lemma Es_refsG[simp]: "Es (refsG F) = Es (sg F) \<inter> (EsRP (sg F))"
  by (simp add: refsG_def)

lemma src_refsG[simp]: "src (refsG F) = rst_fun (EsRP (sg F)) (src (sg F))"
  by (simp add: refsG_def)

lemma tgt_refsG[simp]: "tgt (refsG F) = rst_fun (EsRP (sg F)) (tgtr F)"
  by (simp add: refsG_def)

(*Yields inheritance graph together with proxies and their references*)
definition inhRefsG :: "'a Fr_scheme \<Rightarrow> Gr"
where
  "inhRefsG F \<equiv> inhG (sg F) UG refsG F"

lemma Ns_inhRefsG[simp]: "Ns (inhRefsG F) = rst_Ns (sg F) (EsI (sg F) - EsId (sg F)) 
  \<union> rst_Ns (withRsG F) (EsRP (sg F))"
  by (simp add: inhRefsG_def)

lemma Es_inhRefsG[simp]: "Es (inhRefsG F) = Es (sg F) \<inter> (EsRP (sg F) \<union> ((EsI (sg F)) - (EsId (sg F))))"
  by (auto simp add: inhRefsG_def)

(*The references relation*)
definition refs :: "'a Fr_scheme \<Rightarrow> (V\<times>V) set"
where
  "refs F \<equiv> relOfGr (refsG F)"

definition is_RP :: "E \<Rightarrow> Fr \<Rightarrow> bool"
where
  "is_RP e F \<equiv> e \<in> Es (sg F) \<and> ety (sg F) e = Some eref 
    \<and> nty (sg F) (the (src (sg F) e)) = Some nprxy"

lemma is_RP_eq_in_EsRP:
  assumes ha: "is_wf_g (sg F)"
  shows "is_RP e F = (e \<in> EsRP (sg F))"
  proof 
    assume hb: "is_RP e F"
    then have hc: "e \<in> dom (src (sg F))"
        using ha by (simp add: is_RP_def is_wf_g_def ftotal_on_def)
    from hb hc show "e \<in> EsRP (sg F)"
        by (simp add: is_RP_def EsRP_def NsP_def EsR_def NsTy_def EsTy_def dom_def)
          (rule exI[where x="the (src (sg F) e)"], simp)
  next
    assume "e \<in> EsRP (sg F)"
    then show "is_RP e F"
      using ha by (auto simp add: is_RP_def EsRP_def NsP_def EsR_def NsTy_def EsTy_def
         is_wf_g_def ftotal_on_def)
  qed


(*The 'refsOf' function*)
definition refsOf:: "'a Fr_scheme \<Rightarrow> V \<Rightarrow> V set"
where
  "refsOf F v \<equiv> ((refs F)\<^sup>+)``{v}"

(*The representatives relation*)
definition reps:: "Fr \<Rightarrow> (V\<times>V) set"
where
  "reps F \<equiv> (refs F \<union> (refs F)\<inverse>)"

lemma reps_sym: "\<And>a a'. (a, a') \<in> reps F \<Longrightarrow> (a', a) \<in> reps F"
  by (auto simp: reps_def)

lemma repsst_converse[simp]: "(reps F)^-1 = (reps F)"
  by (auto simp add: reps_def)

lemma repsst_unfold: "(reps F)\<^sup>* = (refs F \<union> (refs F)\<inverse>)\<^sup>*"
  by (simp add: reps_def)

(*The proofs that 'repsst' is an equivalence relation.*)
lemma repsst_reflexive: "(a, a) \<in> (reps F)\<^sup>*"
  by auto

lemma repsst_symmetric: "(a, b) \<in> (reps F)\<^sup>* \<Longrightarrow> (b, a) \<in> (reps F)\<^sup>*"
  proof -
    have h1: "sym (reps F)"
      by (simp add: reps_def reps_sym sym_def)
    have h2: "sym ((reps F)\<^sup>*)"
      using h1 by (simp add: sym_rtrancl)
    show "(a, b) \<in> (reps F)\<^sup>* \<Longrightarrow> (b, a) \<in> (reps F)\<^sup>*"
    using h1 h2 
    by (simp add: sym_def)
  qed

lemma repsst_transitive: "trans ((reps F)\<^sup>*)"
  by (rule trans_rtrancl)

(*The 'repsOf' function: gives equivalence classes*)
definition repsOf:: "V \<Rightarrow> Fr \<Rightarrow> V set"
where
  "repsOf v F \<equiv> ((reps F)\<^sup>*)``{v}"

lemma repsOf_unfold: "repsOf v F = (refs F \<union> (refs F)\<inverse>)\<^sup>*``{v}"
  by (simp add: repsOf_def repsst_unfold)

lemma repsOf_sym: "v2 \<in> repsOf v1 F \<Longrightarrow> v1 \<in> repsOf v2 F"
  proof -
    have h1: "sym (reps F)"
      by (simp add: reps_def reps_sym sym_def)
    have h2: "sym ((reps F)\<^sup>*)"
      using h1 by (simp add: sym_rtrancl)
    show "v2 \<in> repsOf v1 F \<Longrightarrow> v1 \<in> repsOf v2 F"
    using h2
    by (simp add: repsOf_unfold sym_def repsst_unfold)
  qed

(*Gets representative relation based on 'repsOf' function that gives equivalence classes*)
definition repsOf_rel:: "Fr \<Rightarrow> (V\<times>V) set"
where
  "repsOf_rel F \<equiv> {(x, y). y \<in> repsOf x F}"

(*Extension of inh to take references into account*)
definition inhF:: "Fr \<Rightarrow> (V\<times>V) set"
where
  "inhF F \<equiv> inh (sg F) \<union> reps F"
(* old"  "inhF F \<equiv> inh (sg F) \<union> refs F"*)

(*lemma inhF_conv_unfold: "(inhF F)\<inverse> = (inh (sg F))\<inverse> \<union> reps F"
  by (simp add: inhF_def converse_Un)*)

(*lemma inhsg_sub_inhF: "inh (sg F) \<subseteq> inhF F"
  by (simp add: inhF_def)*)

definition acyclic_fr :: "'a Fr_scheme \<Rightarrow> bool"
where
  "acyclic_fr F \<equiv> acyclic (inh (sg F) \<union> refs F)"

definition proxies_dont_inherit :: "'a Fr_scheme \<Rightarrow> bool"
where
  "proxies_dont_inherit F \<equiv> ran (src (sg F) |` EsI (sg F)) \<inter> NsP (sg F) = {}"

definition nonPRefsOf:: "'a Fr_scheme \<Rightarrow> V \<Rightarrow> V set"
where
  "nonPRefsOf F v1 \<equiv>  {v2. v2 \<in> refsOf F v1 \<and> v2 \<notin> NsP (sg F)}"

definition is_wf_fr :: "'a Fr_scheme \<Rightarrow> bool"
where
  "is_wf_fr F \<equiv> is_wf_sg (sg F) 
    \<and> ftotal_on (tr F) (EsRP (sg F)) (V_A) 
    \<and> inj_on (src (sg F)) (EsRP (sg F)) 
    \<and> ran(src (sg F)|`EsRP (sg F)) = NsP(sg F)
    \<and> (\<forall> v. v \<in> NsP (sg F) \<longrightarrow> nonPRefsOf F v \<noteq> {})
    \<and> acyclic_fr F \<and> proxies_dont_inherit F"

(*When a list of fragments is disjoint*)
definition disjFs :: "Fr list \<Rightarrow> bool"
where
  "disjFs Fs \<equiv> disjGsL (map sg Fs)"

(*Fragments union*)
definition cupF :: "Fr \<Rightarrow> Fr \<Rightarrow> Fr" (infixl "UF" 100)
where
  "F1 UF F2 \<equiv> \<lparr>sg =  (sg F1) USG (sg F2), tr = tr F1 ++ tr F2\<rparr>"

lemma tr_UF[simp]: "tr (F1 UF F2) = tr F1 ++ tr F2"
  by (simp add: cupF_def)

lemma sg_UF[simp]: "sg (F1 UF F2) = (sg F1) USG (sg F2)"
  by (simp add: cupF_def)

(*Above '++' equates to union because fragments are disjoint*)

lemma UF_sym: 
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
  shows "F1 UF F2 = F2 UF F1"
  proof -
    from h1 have h1a: "is_wf_sg (sg F1)" by (simp add: is_wf_fr_def)
    from h1 have h1b: "dom (tr F1) = EsRP (sg F1)"
      by (simp add: is_wf_fr_def ftotal_on_def)
    from h2 have h2a: "is_wf_sg (sg F2)" by (simp add: is_wf_fr_def)
    from h2 have h2b: "dom (tr F2) = EsRP (sg F2)"
      by (simp add: is_wf_fr_def ftotal_on_def)
    from h3 have h3a: "Es (sg F1) \<inter> Es (sg F2) = {}"
      by (simp add: disjGs_def)
    hence h3b: "dom (tr F1) \<inter> dom (tr F2) = {}" 
      using h1a h2a h1b h2b by (auto intro: in_EsRP_in_Es)
    show ?thesis
    proof (simp add: cupF_def, rule conjI)
      show "(sg F1) USG (sg F2) = (sg F2) USG (sg F1)"
        using h1a h2a h3 USG_sym[of "sg F1" "sg F2"] by (simp)
    next
      show "tr F1 ++ tr F2 = tr F2 ++ tr F1"
        using h3b map_add_comm[of "tr F1" "tr F2"] by (simp)
    qed
  qed

(* Fragment distributed union*)
primrec UFs :: "Fr list \<Rightarrow> Fr"
where
  "UFs [] = emptyFr"
  | "UFs (F#Fs) = F UF (UFs Fs)"

lemma in_refs: 
  assumes h1: "is_wf_fr F"
  shows "(v1, v2) \<in> refs F \<longleftrightarrow> v1 \<in> NsP (sg F) \<and> (\<exists> e. src (sg F) e = Some v1 
    \<and> e \<in> EsRP (sg F) \<and> tr F e = Some v2)"
  proof -
    from h1 have h1a: "dom (src (sg F)) = Es (sg F)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def) 
    from h1 have h1b: "dom (tr F) = EsRP(sg F)"
      by (simp add: is_wf_fr_def ftotal_on_def)
    show ?thesis
    proof
      assume "(v1, v2) \<in> refs F"
      then show "v1 \<in> NsP (sg F) \<and> (\<exists>e. src (sg F) e = Some v1 \<and> e \<in> EsRP (sg F) \<and> 
        tr F e = Some v2)"
      proof (simp add: refs_def refsG_def withRsG_def relOfGr_def adjacent_def rst_fun_def)
        apply_end(clarify)
        fix e
        assume h2a: "e \<in> Es (sg F)"
        assume h2b: "e \<in> EsRP (sg F)"
        assume h2c: "(src (sg F) |` (EsRP (sg F) \<inter> dom (src (sg F)))) e = Some v1"
        hence h2d: "src (sg F) e = Some v1" 
          using h2a h2b by (auto simp add: restrict_map_def split: if_splits)
        hence h2e: "v1 \<in> NsP (sg F)" 
          using h2b by (simp add: EsRP_def)
        assume h2f: "(tgtr F |` (EsRP (sg F) \<inter> dom (tgtr F))) e = Some v2"
        hence h2g: "tr F e = Some v2"
          using h2a h2b h1b by (auto simp add: restrict_map_def tgtr_def split: if_splits)
        show "v1 \<in> NsP (sg F) 
          \<and> (\<exists>e. src (sg F) e = Some v1 \<and> e \<in> EsRP (sg F) \<and> tr F e = Some v2)"
          using h2e h2d h2g h2b by (simp)(rule exI[where x="e"], simp add: EsRP_def)
      qed
    next
      apply_end(clarify)
      fix e
      assume h2a: "v1 \<in> NsP (sg F)"
      assume h2b: "src (sg F) e = Some v1"
      assume h2c: "e \<in> EsRP (sg F)"
      assume h2d: "tr F e = Some v2"
      show "(v1, v2) \<in> refs F"
        using h2a h2b h2c h2d h1a 
        by (simp add: refs_def refsG_def withRsG_def relOfGr_def adjacent_def rst_fun_def)
          (rule exI[where x="e"], auto simp add: EsRP_def restrict_map_def tgtr_def)
    qed
  qed

lemma refsOf_Nsp: 
  assumes h1: "is_wf_fr F" and h2: "v \<notin> NsP (sg F)" 
  shows "refsOf F v  = {}"
  proof
    show "refsOf F v \<subseteq> {}"
    proof (simp add: refsOf_def Image_def, clarify)
      fix x
      assume "(v, x) \<in> (refs F)\<^sup>+"
      then show "False"
      proof (induct)
        case base
        fix y
        assume "(v, y) \<in> refs F"
        then show "False" using assms by (auto simp add: in_refs)
      next
        case step 
        apply_end(simp)
      qed
    qed
  next
    show "{} \<subseteq> refsOf F v" by auto
  qed

lemma Domain_refs: 
  assumes h: "is_wf_fr F"
  shows "Domain (refs F) = NsP (sg F)"
  proof -
    from h have h1a: "ran(src (sg F)|`EsRP (sg F)) = NsP(sg F)"
      by (simp add: is_wf_fr_def)
    from h have h1b: "is_wf_sg (sg F)"
      by (simp add: is_wf_fr_def)
    from h1b have h1c: "dom (src (sg F)) = Es (sg F)"
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h have h1d: "dom (tr F) = EsRP(sg F)"
      by (simp add: is_wf_fr_def ftotal_on_def)
    from h have h1e: "dom (tgtr F) = Es (sg F)"
      using EsRP_sub_Es[where SG = "sg F"] 
      by (auto simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def tgtr_def ftotal_on_def)
    show ?thesis
    proof
      show "Domain (refs F) \<subseteq> NsP (sg F)"
        by (auto simp add: refs_def relOfGr_def refsG_def withRsG_def EsRP_def tgtr_def
          restrict_def NsP_def NsTy_def rst_fun_def EsR_def EsTy_def adjacent_def
          map_add_def restrict_map_def split: option.splits if_splits)
    next
      show "NsP (sg F) \<subseteq> Domain (refs F)"
      proof
        fix x
        assume h2: "x \<in> NsP (sg F)"
        from h2 h1a have h3: "x \<in> ran (src (sg F) |` EsRP (sg F))" by simp
        from h2 h3 have h4: "\<exists> e. e \<in> EsRP (sg F) \<and> src (sg F) e = Some x"
          by (simp add: restrict_map_def ran_def)(erule exE, auto split: if_splits)
        from h3 h4 have h3a: "x \<in> ran (src (sg F))"
          by (auto simp add: ran_def restrict_map_def split: if_splits)
        from h3 h1b h1c have h3a: "x \<in> ran (src (refsG F))"
          using EsRP_sub_Es[where SG="sg F"]
          by (simp)(subgoal_tac "EsRP (sg F) \<inter> Es (sg F) = EsRP (sg F)", auto)
        from h4 show "x \<in> Domain (refs F)"
        proof
          apply_end(erule conjE)
          fix e
          assume h5: "e \<in> EsRP (sg F)"
          from h5 h1d have h5a: "\<exists> v. tr F e = Some v"
            by (auto simp add: dom_def)
          assume h6: "src (sg F) e = Some x"
          from h5a show "x \<in> Domain (refs F)"
          proof
            fix v
            assume h7: "tr F e = Some v"
            from h h5 h6 h7 h1b h1c h1e show "x \<in> Domain (refs F)"
            using EsRP_sub_Es[where SG="sg F"]
            by (simp add: refs_def refsG_def relOfGr_def withRsG_def restrict_def
              rst_fun_def adjacent_def)(rule_tac exI[where x="v"], rule_tac exI[where x="e"],
              subgoal_tac "EsRP (sg F) \<inter> Es (sg F) = EsRP (sg F)",
              auto simp add: tgtr_def intro: in_EsRP_in_Es)
          qed
        qed
      qed
    qed
  qed

lemma Range_refs: 
  assumes h1: "is_wf_fr F"
  shows "Range (refs F) \<subseteq> Ns (sg F) \<union> ran (tr F)"
  proof -
    from h1 have h1a: "ran (tgt (sg F)) \<subseteq> Ns (sg F)"
      by (auto simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    show ?thesis
    using h1a
    by (auto simp add: refs_def relOfGr_def refsG_def withRsG_def EsRP_def tgtr_def
      restrict_def NsP_def NsTy_def rst_fun_def EsR_def EsTy_def adjacent_def 
      restrict_map_def map_add_def split: option.splits)(auto intro!: ranI)
qed

lemma single_valued_refs:
  assumes h1: "is_wf_fr F"
  shows "single_valued (refs F)"
  proof -
    from h1 have h1a: "inj_on (src (sg F)) (EsRP (sg F))" by (simp add: is_wf_fr_def)
    show ?thesis
    proof (simp add: single_valued_def)
      apply_end(clarify)
      fix x y1 y2
      assume h2a: "(x, y1) \<in> refs F"
      hence h2b: "x \<in> NsP (sg F) \<and> (\<exists> e. src (sg F) e = Some x 
        \<and> e \<in> EsRP (sg F) \<and> tr F e = Some y1)" using h1 by (simp add: in_refs)
      assume h2c: "(x, y2) \<in> refs F"
      hence h2d: "x \<in> NsP (sg F) \<and> (\<exists> e. src (sg F) e = Some x 
        \<and> e \<in> EsRP (sg F) \<and> tr F e = Some y2)" using h1 by (simp add: in_refs)
      from h2b h2d h1a show "y1 = y2"
      proof (clarsimp)
        fix e1 e2
        assume h3a: "inj_on (src (sg F)) (EsRP (sg F))"
        assume h3b: "x \<in> NsP (sg F)"
        assume h3c: "e1 \<in> EsRP (sg F)"
        assume h3d: "e2 \<in> EsRP (sg F)"
        assume h3e: "src (sg F) e1 = Some x"
        assume h3f: "src (sg F) e2 = Some x"
        from h3a h3c h3d h3e h3f have h3g: "e1 = e2" by (simp add: inj_on_def)
        assume h3h: "tr F e1 = Some y1"
        assume h3i: "tr F e2 = Some y2"
        from h3g h3h h3i show "y1 = y2" by auto
      qed
    qed
  qed

lemma in_refs_trcl:
  shows "(v1, v2) \<in> (refs F)\<^sup>+ \<longleftrightarrow> (v1, v2) \<in> (refs F) \<or> (\<exists> v3. (v1, v3) \<in> (refs F)\<^sup>+ 
    \<and> (v3, v2) \<in> (refs F))"
  proof
    assume h1: "(v1, v2) \<in> (refs F)\<^sup>+"
    then show "(v1, v2) \<in> refs F \<or> (\<exists>v3. (v1, v3) \<in> (refs F)\<^sup>+ \<and> (v3, v2) \<in> refs F)"
    proof (case_tac "(v1, v2) \<in> refs F")
      assume "(v1, v2) \<in> refs F"
      then show "(v1, v2) \<in> refs F \<or> (\<exists>v3. (v1, v3) \<in> (refs F)\<^sup>+ \<and> (v3, v2) \<in> refs F)"
        by simp
    next
      assume h2: "(v1, v2) \<notin> refs F"
      from h1 h2 have h3: "(v1, v2) \<in> (refs F)\<^sup>+ O (refs F)"
        using trancl_unfold[of "refs F"]
        by (auto)
      from h2 h3 show "(v1, v2) \<in> refs F \<or> (\<exists>v3. (v1, v3) \<in> (refs F)\<^sup>+ \<and> (v3, v2) \<in> refs F)"
        by (simp add: relcomp_unfold)
    qed
  next
    apply_end(erule disjE)
    assume "(v1, v2) \<in> refs F"
    then show "(v1, v2) \<in> (refs F)\<^sup>+" by simp
  next
    assume h1: "\<exists>v3. (v1, v3) \<in> (refs F)\<^sup>+ \<and> (v3, v2) \<in> refs F"
    then show "(v1, v2) \<in> (refs F)\<^sup>+" by auto
  qed

(*lemma refs_refs_trcl_eq: 
  assumes h1: "is_wf_fr F" and h2: "(v, v1) \<in> (refs F)" and h3: "v1 \<notin> NsP(sg F)"
    and h4: "(v, v2) \<in> (refs F)\<^sup>+" and h5: "v2 \<notin> NsP(sg F)"
  shows "v1 = v2"
  proof -
    from h1 have h1a: "inj_on (src (sg F)) (EsRP (sg F))" 
      by (simp add: is_wf_fr_def)
    from h4 have "(v, v2) \<in> (refs F)O(refs F)\<^sup>*" 
      by (simp add: trancl_unfold_left)
    hence "\<exists> v3. (v, v3) \<in> (refs F) \<and> (v3, v2) \<in> (refs F)\<^sup>*"
      by auto
    hence h6a: "(v1, v2) \<in> (refs F)\<^sup>*" 
    proof (clarify)
      fix v3
      assume h6b: "(v3, v2) \<in> (refs F)\<^sup>*"
      assume "(v, v3) \<in> refs F"
      hence "v \<in> NsP (sg F) \<and> (\<exists> e. src (sg F) e = Some v 
        \<and> e \<in> EsRP (sg F) \<and> tr F e = Some v3)" 
        using h1 by (simp add: in_refs nonPRefsOf_def)
      then show "(v1, v2) \<in> (refs F)\<^sup>*"
      proof (clarify)
        fix e
        assume h6c: "v \<in> NsP (sg F)"
        assume h6d: "src (sg F) e = Some v"
        assume h6e: "e \<in> EsRP (sg F)"
        assume h6f: "tr F e = Some v3"
        from h2 have "v \<in> NsP (sg F) \<and> (\<exists> e. src (sg F) e = Some v 
          \<and> e \<in> EsRP (sg F) \<and> tr F e = Some v1)" 
          using h1 by (simp add: in_refs)
        then show "(v1, v2) \<in> (refs F)\<^sup>*"
        proof (clarify)
          fix e2
          assume h6g: "src (sg F) e2 = Some v"
          assume "e2 \<in> EsRP (sg F)"
          hence h6h: "e = e2" using h6d h6e h6g h1a by (simp add: inj_on_def)
          assume h6i: "tr F e2 = Some v1"
          then show "(v1, v2) \<in> (refs F)\<^sup>*" using h6b h6h h6f h3 by auto
        qed
      qed
    qed
    have "v1 \<notin> Domain (refs F)" using h3 h1 Domain_refs by simp
    then  show ?thesis using h6a by (simp add: Not_Domain_rtrancl)
  qed*)

lemma is_single_valued_nonPRefsOf:
  assumes h1: "is_wf_fr F" and h2: "{v1, v2} \<subseteq> nonPRefsOf F v"
  shows "v1 = v2"
  proof -
    from h2 show ?thesis
    proof (simp add: nonPRefsOf_def refsOf_def)
      apply_end(clarify)
      assume h3a: "(v, v1) \<in> (refs F)\<^sup>+"
      assume h3b: "v1 \<notin> NsP (sg F)"
      hence h3c: "v1 \<notin> Domain (refs F)" using h1 Domain_refs[of "F"] by simp
      assume h3d: "(v, v2) \<in> (refs F)\<^sup>+"
      assume h3e: "v2 \<notin> NsP (sg F)"
      hence h3f: "v2 \<notin> Domain (refs F)" using h1 Domain_refs[of "F"] by simp
      from h3a h3c h3d h3f show ?thesis 
        using h1 single_valued_refs[of F] by (simp add: single_valued_rel_trcl_eq)
    qed
  qed

lemma nonPRefsOf_only_one:
  assumes h1: "is_wf_fr F" and h2: "v2 \<in> nonPRefsOf F v1"
  shows "nonPRefsOf F v1 = {v2}"
  proof -
    from h1 have h1a: "inj_on (src (sg F)) (EsRP (sg F))" 
      by (simp add: is_wf_fr_def)
    from h2 have h2a: "(v1, v2) \<in> (refs F)\<^sup>+"
      using h1 by (simp add: nonPRefsOf_def refsOf_def)
    from h2 have h2b: "v2 \<notin> NsP (sg F)" 
      by (simp add: nonPRefsOf_def refsOf_def)
    hence h2c: "v2 \<notin> Domain (refs F)" using h1 Domain_refs[of "F"] by simp
    show ?thesis
    proof
      show "nonPRefsOf F v1 \<subseteq> {v2}"
      proof
        fix x
        assume h3a: "x \<in> nonPRefsOf F v1"
        hence h3b: "(v1, x) \<in> (refs F)\<^sup>+" 
          by (simp add: nonPRefsOf_def refsOf_def)
        from h3a have h3c: "x \<notin> NsP(sg F)" by (auto simp add: nonPRefsOf_def)
        hence h3c: "x \<notin> Domain (refs F)" using h1 Domain_refs[of "F"] by simp
        then show "x \<in> {v2}" 
          using h2a h2c h3b h3c h1 single_valued_refs[of F] 
          by (simp add: single_valued_rel_trcl_eq)
      qed
      next
        from h2a h2b show "{v2} \<subseteq> nonPRefsOf F v1" 
          by (simp add: nonPRefsOf_def refsOf_def)
    qed
  qed

lemma in_nonPRefsOf_in_tr: 
  assumes h1: "is_wf_fr F" and h2: "nonPRefsOf F a = {x}"  
  shows "\<exists> e. tr F e = Some x"
  proof -
    from h2 have h2a: "x \<in> nonPRefsOf F a" by simp
    hence "(a, x) \<in> (refs F)\<^sup>+" by (simp add: nonPRefsOf_def refsOf_def)
    hence h2b: "(a, x) \<in> (refs F) \<or> (\<exists> v3. (a, v3) \<in> (refs F)\<^sup>+ \<and> (v3, x) \<in> (refs F))"
      using in_refs_trcl by (blast)
    from h2b show ?thesis
    proof
      assume "(a, x) \<in> refs F"
      then show "\<exists>e. tr F e = Some x" using h1 in_refs[of F] by (blast)
    next
      assume "\<exists>v3. (a, v3) \<in> (refs F)\<^sup>+ \<and> (v3, x) \<in> refs F"
      then show "\<exists>e. tr F e = Some x" using h1 in_refs[of F] by (blast)
    qed
  qed

lemma is_wf_withRsG: 
  assumes h1: "is_wf_fr F"
  shows "is_wf_g (withRsG F)"
  proof -
    from h1 have h1a: "is_wf_g (sg F)"
      by (simp add: is_wf_fr_def is_wf_sg_def)
    from h1 have h1b: "dom (tr F) \<subseteq> Es (sg F)"
      by (auto simp add: is_wf_fr_def is_wf_sg_def ftotal_on_def EsRP_def EsR_def EsTy_def)
    from h1 have h1c: "ran (tr F)\<subseteq> V_A"
      by (simp add: is_wf_fr_def ftotal_on_def)
    from h1a h1b h1c show ?thesis
      using ran_map_add_sub[where f= "tgt(sg F)" and g = "tr F"]
      by (auto simp add: is_wf_g_def withRsG_def ftotal_on_def tgtr_def) 
  qed

lemma is_wf_refsG: 
  assumes h1: "is_wf_fr F"
  shows "is_wf_g (refsG F)"
  proof -
    from h1 have h1a: "is_wf_g (sg F)"
      by (simp add: is_wf_fr_def is_wf_sg_def)
    from h1 have h1b: "dom (tr F) \<subseteq> Es (sg F)"
      by (auto simp add: is_wf_fr_def is_wf_sg_def ftotal_on_def EsRP_def EsR_def EsTy_def)
    from h1 have h1c: "ran (tr F) \<subseteq> V_A"
      by (simp add: is_wf_fr_def ftotal_on_def)
    from h1a h1c have h1d: "ran (tgtr F) \<subseteq> V_A"
      using ran_map_add_sub[where f= "tgt(sg F)" and g = "tr F"]
      by (auto simp add: is_wf_g_def tgtr_def ftotal_on_def)(frule subsetD, auto)
    from h1a have h1e: "dom (src (sg F)) = Es (sg F)"
      by (simp add: is_wf_g_def ftotal_on_def)
    from h1 have h1f: "dom (tgtr F) = Es (sg F)"
      using EsRP_sub_Es[where SG = "sg F"] 
      by (auto simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def tgtr_def ftotal_on_def)
    show ?thesis
      proof (simp add: is_wf_g_def, rule conjI)
        from h1a h1d show "rst_Ns (withRsG F) (EsRP (sg F)) \<subseteq> V_A"
          using ran_restrict_sub[of "src(sg F)" "EsRP (sg F)"]
            ran_restrict_sub[of "tgtr F" "EsRP (sg F)"]
          by (auto simp add: rst_Ns_def is_wf_g_def ftotal_on_def)
      next
        apply_end(rule conjI)
        from h1a show "Es (sg F) \<inter> EsRP (sg F) \<subseteq> E_A"
          by (auto simp add: is_wf_g_def)
      next
        apply_end(rule conjI)
        from h1 have ha: "(EsRP (sg F) \<inter> Es (sg F)) = EsRP (sg F)"
          by (auto simp add: is_wf_fr_def intro: in_EsRP_in_Es)
        show "ftotal_on (rst_fun (EsRP (sg F)) (src (sg F))) (Es (sg F) \<inter> EsRP (sg F))
          (rst_Ns (withRsG F) (EsRP (sg F)))"
          using h1e ha by (auto simp add: ftotal_on_def rst_Ns_def)
      next
        from h1 have ha: "is_wf_sg (sg F)"
          by (simp add: is_wf_fr_def)
        from ha have hb: "(EsRP (sg F) \<inter> Es (sg F)) = EsRP (sg F)"
          by (auto intro: in_EsRP_in_Es)
        show "ftotal_on (rst_fun (EsRP (sg F)) (tgtr F)) (Es (sg F) \<inter> EsRP (sg F))
          (rst_Ns (withRsG F) (EsRP (sg F)))"
          using h1e ha h1f hb
          by (auto simp add: ftotal_on_def rst_Ns_def intro: in_EsRP_in_Es)
      qed
  qed

lemma tgtr_fr_Un_dist:
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
  shows "tgtr (F1 UF F2) = tgtr (F1) ++  tgtr (F2)"
  proof -
    from h1 have h1a: "dom (tgt (sg F1)) = Es (sg F1)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1b: "dom (tr F1) \<subseteq> Es (sg F1)"
      by (auto simp add: is_wf_fr_def is_wf_sg_def ftotal_on_def EsRP_def EsR_def EsTy_def)
    from h2 have h2a: "dom (tgt (sg F2)) = Es (sg F2)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2b: "dom (tr F2) \<subseteq> Es (sg F2)"
      by (auto simp add: is_wf_fr_def is_wf_sg_def ftotal_on_def EsRP_def EsR_def EsTy_def)
    from h3 have h3a: "Es (sg F1) \<inter> Es (sg F2) = {}" 
      by (simp add: disjGs_def disjEsGs_def)
    show "?thesis"
    proof
      fix e
      show "tgtr (F1 UF F2) e = (tgtr F1 ++ tgtr F2) e"
      proof (case_tac "e \<in> Es (sg F1)")
        assume h4: "e \<in> Es (sg F1)"
        then show "tgtr (F1 UF F2) e = (tgtr F1 ++ tgtr F2) e"
        using h1a h1b h2a h2b h3a 
        by (auto simp add: cupF_def tgtr_def cupSG_def map_add_def split: option.splits)
      next
        assume h4: "e \<notin> Es (sg F1)"
        then show "tgtr (F1 UF F2) e = (tgtr F1 ++ tgtr F2) e"
        using h1a h1b h2a h2b h3a 
        by (auto simp add: cupF_def tgtr_def cupSG_def map_add_def split: option.splits)
      qed
    qed
  qed

lemma withRsG_fr_Un_dist:
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
  shows "withRsG (F1 UF F2) = withRsG (F1) UG  withRsG (F2)"
  proof -
    from h1 have h1a: "is_wf_sg (sg F1)"
      by (simp add: is_wf_fr_def)
    from h1 have h1b: "dom (tr F1) \<subseteq> Es (sg F1)"
      by (auto simp add: is_wf_fr_def is_wf_sg_def ftotal_on_def EsRP_def EsR_def EsTy_def)
    from h2 have h2a: "is_wf_sg (sg F2)"
      by (simp add: is_wf_fr_def)
    from h2 have h2b: "dom (tr F2) \<subseteq> Es (sg F2)"
      by (auto simp add: is_wf_fr_def is_wf_sg_def ftotal_on_def EsRP_def EsR_def EsTy_def)
    from h3 have h3a: "Es (sg F1) \<inter> Es (sg F2) = {}" 
      by (simp add: disjGs_def disjEsGs_def)
    have h4: "dom (tr F1) \<inter> dom (tr F2) = {}" 
      using h1b h2b h3a by (auto)
    show ?thesis
    using h1 h2 h3 h1a h2a h4 
    by (auto simp add: withRsG_def tgtr_fr_Un_dist cupSG_def cupG_def)
 qed

lemma refsG_fr_Un_dist:
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
  shows "refsG (F1 UF F2) = refsG (F1) UG  refsG (F2)"
  proof -
    from h1 have h1a: "is_wf_sg (sg F1)"
      by (simp add: is_wf_fr_def)
    from h1 have h1b: "dom (src (sg F1)) = Es (sg F1)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1c: "dom (tgt (sg F1)) = Es (sg F1)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1d: "is_wf_g(withRsG F1)"
      by (simp add: is_wf_withRsG)
    from h1d have h1e: "dom (src (withRsG F1)) = Es (withRsG F1)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1d have h1f: "dom (tgt (withRsG F1)) = Es (withRsG F1)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1g: "dom (tgtr F1) = Es (sg F1)"
      using EsRP_sub_Es[where SG = "sg F1"] 
      by (auto simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def tgtr_def ftotal_on_def)
    from h2 have h2a: "is_wf_sg (sg F2)"
      by (simp add: is_wf_fr_def)
    from h2 have h2b: "dom (src (sg F2)) = Es (sg F2)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2c: "dom (tgt (sg F2)) = Es (sg F2)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2d: "is_wf_g(withRsG F2)"
      by (simp add: is_wf_withRsG)
    from h2d have h2e: "dom (src (withRsG F2)) = Es (withRsG F2)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2d have h2f: "dom (tgt (withRsG F2)) = Es (withRsG F2)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2g: "dom (tgtr F2) = Es (sg F2)"
      using EsRP_sub_Es[where SG = "sg F2"] 
      by (auto simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def tgtr_def ftotal_on_def)
    from h3 have h3a: "Es (sg F1) \<inter> Es (sg F2) = {}" 
      by (simp add: disjGs_def disjEsGs_def)
    from h3a have h3b: "disjEsGs (withRsG F1) (withRsG F2)"
      by (simp add: disjEsGs_def)
    show ?thesis
      using h1 h2 h3 h1a h2a h3a h3b h1d h2d
      proof (simp add: refsG_def restrict_dist_cup withRsG_fr_Un_dist EsRP_disj_dist
        restrict_def rst_Ns_dist_UG Gr_eq)
        apply_end(rule conjI)
        have ha: "EsRP (sg F2) \<inter> Es (sg F1) = {}"
          using h1b h2a h2b h3a by (auto intro: in_EsRP_in_Es)
        have hb: "EsRP (sg F1) \<subseteq> Es (sg F1)"
          using h1a h1b by (auto intro: in_EsRP_in_Es)
        have hc: "rst_Ns (withRsG F1) (EsRP (sg F1) \<union> EsRP (sg F2))
          = rst_Ns (withRsG F1) (EsRP (sg F1))"
          using ha hb h1d by (simp add: rst_Ns_Un_neutral)
        have hd: "EsRP (sg F1) \<inter> Es (sg F2) = {}"
          using h1b h1a h2b h3a by (auto intro: in_EsRP_in_Es)
        have he: "EsRP (sg F2) \<subseteq> Es (sg F2)"
          using h2a h1b by (auto intro: in_EsRP_in_Es)
        have hf: "EsRP (sg F1) \<union> EsRP (sg F2) = EsRP (sg F2) \<union> EsRP (sg F1)"
          by auto
        have hg: "rst_Ns (withRsG F2) (EsRP (sg F1) \<union> EsRP (sg F2))
          = rst_Ns (withRsG F2) (EsRP (sg F2))"
          using hd he hf h2d by (simp add: rst_Ns_Un_neutral)
        show "rst_Ns (withRsG F1) (EsRP (sg F1) \<union> EsRP (sg F2)) \<union>
          rst_Ns (withRsG F2) (EsRP (sg F1) \<union> EsRP (sg F2)) =
          rst_Ns (withRsG F1) (EsRP (sg F1)) \<union> rst_Ns (withRsG F2) (EsRP (sg F2))"
          using hc hg by (simp add: rst_Ns_def)
      next
        apply_end(rule conjI)
        show "(Es (sg F1) \<union> Es (sg F2)) \<inter> (EsRP (sg F1) \<union> EsRP (sg F2)) =
          Es (sg F1) \<inter> EsRP (sg F1) \<union> Es (sg F2) \<inter> EsRP (sg F2)"
          using h3a h2a h1a by (auto intro: in_EsRP_in_Es)
      next
        apply_end(rule conjI)
        have ha: "EsRP (sg F2) \<inter> dom(src (sg F1)) = {}"
          using h3a h2a h1b by (auto intro: in_EsRP_in_Es)
        have hb: "EsRP (sg F1) \<subseteq> dom(src (sg F1))"
          using h3a h1a h1b by (auto intro: in_EsRP_in_Es)
        have hc: "EsRP (sg F1) \<inter> dom(src (sg F2)) = {}"
          using h3a h1a h2b by (auto intro: in_EsRP_in_Es)
        have hd: "EsRP (sg F2) \<subseteq> dom(src (sg F2))"
          using h3a h2a h2b by (auto intro: in_EsRP_in_Es)
        have he: "EsRP (sg F1) \<union> EsRP (sg F2) = EsRP (sg F2) \<union> EsRP (sg F1)"
          by auto
        show "rst_fun (EsRP (sg F1) \<union> EsRP (sg F2)) (src (sg F1) ++ src (sg F2)) =
          rst_fun (EsRP (sg F1)) (src (sg F1)) ++ rst_fun (EsRP (sg F2)) (src (sg F2))"
          using ha hb hc hd by (simp add: rst_fun_dist_map_add rst_fun_Un_neutral)
            (simp add: he rst_fun_Un_neutral)
    next
      have ha: "EsRP (sg F2) \<inter> dom(tgtr F1) = {}"
        using h3a h2a h1g by (auto intro: in_EsRP_in_Es)
      have hb: "EsRP (sg F1) \<subseteq> dom(tgtr F1)"
          using h3a h1a h1g by (auto intro: in_EsRP_in_Es)
        have hc: "EsRP (sg F1) \<inter> dom(tgtr F2) = {}"
          using h3a h1a h2g by (auto intro: in_EsRP_in_Es)
        have hd: "EsRP (sg F2) \<subseteq> dom(tgtr F2)"
          using h3a h2a h2g by (auto intro: in_EsRP_in_Es)
        have he: "EsRP (sg F1) \<union> EsRP (sg F2) = EsRP (sg F2) \<union> EsRP (sg F1)"
          by auto
      show "rst_fun (EsRP (sg F1) \<union> EsRP (sg F2)) (tgtr F1 ++ tgtr F2) =
        rst_fun (EsRP (sg F1)) (tgtr F1) ++ rst_fun (EsRP (sg F2)) (tgtr F2)"
        using ha hb hc hd by (simp add: rst_fun_dist_map_add rst_fun_Un_neutral)
        (simp add: he rst_fun_Un_neutral)
    qed
  qed

lemma refs_UF:
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
  shows "refs (F1 UF F2) = refs F1 \<union> refs F2"
  proof -
    from h1 have h1a: "is_wf_g (refsG F1)" by (simp add: is_wf_refsG)
    from h2 have h2a: "is_wf_g (refsG F2)" by (simp add: is_wf_refsG)
    from h3 have h3a: "disjEsGs (sg F1) (sg F2)" by (simp add: disjGs_def  disjEsGs_def)
    from h3a have h3b: "disjEsGs (refsG F1) (refsG F2)" 
      by (auto simp add: disjEsGs_def)
    show ?thesis
    using assms h1a h2a h3b by (simp add: refs_def refsG_fr_Un_dist relOfGr_UG)
  qed

lemma refs_trcl_UF:
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
    and h4: "Range (refs F1) \<inter> Ns (sg F2) = {}"
  shows "(refs (F1 UF F2))\<^sup>+ = (refs F1)\<^sup>+ \<union> (refs F2)\<^sup>+ \<union> ((refs F2)\<^sup>+ O Range (refs F2) \<lhd> (refs F1)\<^sup>+)"
  proof -
    from h1 have h1a: "is_wf_sg (sg F1)" by (simp add: is_wf_fr_def)
    from h1 have h1b: "dom (nty (sg F1)) = Ns (sg F1)"
      by (simp add: is_wf_fr_def is_wf_sg_def ftotal_on_def)
    from h2 have h2a: "is_wf_sg (sg F2)" by (simp add: is_wf_fr_def)
    from h2 have h2b: "dom (nty (sg F2)) = Ns (sg F2)"
      by (simp add: is_wf_fr_def is_wf_sg_def ftotal_on_def)
    from h3 have h3a: "Ns (sg F1) \<inter> Ns (sg F2) = {}" by (simp add: disjGs_def)
    have h5a:"Domain (refs F2) \<inter>  Domain (refs F1) = {}"
    proof
      show "Domain (refs F2) \<inter>  Domain (refs F1) \<subseteq> {}"
      proof
        fix x
        assume "x \<in> Domain (refs F2) \<inter>  Domain (refs F1)"
        then show "x \<in> {}"
          using h1b h2b h3a by (auto simp add: refs_def inh_def relOfGr_def refsG_def withRsG_def adjacent_def 
            EsRP_def rst_fun_def NsP_def NsTy_def EsR_def restrict_map_def EsI_def EsId_def 
            EsTy_def split: if_splits intro!: ranI domI)
      qed
    next
      show "{} \<subseteq> Domain (refs F2) \<inter>  Domain (refs F1)" by simp
    qed
    have h5b: "Range (refs F1) \<inter> Domain (refs F2) = {}"
    proof
      show "Range (refs F1) \<inter> Domain (refs F2) \<subseteq> {}"
      proof
        fix x
        assume h5c: "x \<in> Range (refs F1) \<inter> Domain (refs F2)"
        hence h5d: "x \<in> Range (refs F1)" by auto
        from h5c have h5e: "x \<in> Domain (refs F2)" by auto
        hence "x \<in> Ns (sg F2)" using h2 h2a by (auto simp add: Domain_refs intro: in_NsP_Ns)
        then show "x \<in> {}" using h5d h4 by auto
      qed
    next
      show "{} \<subseteq> Range (refs F1) \<inter> Domain (refs F2)" by auto
    qed
    have h5c: "refs F1 \<union> refs F2 = refs F2  \<union> refs F1" by auto
    have h5d: "(refs (F1 UF F2))\<^sup>+ = (refs F2)\<^sup>+ \<union> (refs F1)\<^sup>+ \<union> ((refs F2)\<^sup>+ O Range (refs F2) \<lhd> (refs F1)\<^sup>+)"
      using h5a h5b h1 h2 h3 
      by (simp add: refs_UF h5c)(simp add: trancl_disj_dist_Un_2)
    show ?thesis by (auto simp add: h5d)
  qed

lemma Dom_Un_refs_disjoint:
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
  shows "Domain (refs F1) \<inter> Domain (refs F2) = {}"
  proof -
    from h1 have h1a: "dom (src (sg F1)) = Es (sg F1)"
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1b: "dom (tgt (sg F1)) = Es (sg F1)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1c: "ran (src (sg F1)) \<subseteq> Ns (sg F1)"
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1d: "dom (nty (sg F1)) = Ns (sg F1)" 
      by (simp add: is_wf_fr_def is_wf_sg_def ftotal_on_def)
    from h1 have h1e: "dom (tgtr F1) = Es (sg F1)"
      using h1b EsRP_sub_Es[where SG = "sg F1"] 
      by (auto simp add: is_wf_fr_def tgtr_def ftotal_on_def)
    from h2 have h2a: "dom (src (sg F2)) = Es (sg F2)"
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2b: "dom (tgt (sg F2)) = Es (sg F2)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2c: "ran (src (sg F2)) \<subseteq> Ns (sg F2)"
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2d: "dom (nty (sg F2)) = Ns (sg F2)" 
      by (simp add: is_wf_fr_def is_wf_sg_def ftotal_on_def)
    from h2 have h2e: "dom (tgtr F2) = Es (sg F2)"
      using h2b EsRP_sub_Es[where SG = "sg F2"] 
      by (auto simp add: is_wf_fr_def tgtr_def ftotal_on_def)
    from h3 have h3a: "Ns (sg F1) \<inter> Ns (sg F2) = {}"
      by (simp add: disjGs_def)
    show ?thesis
    proof
      show "Domain (refs F1) \<inter> Domain (refs F2) \<subseteq> {}"
      proof
        fix x
        assume "x \<in> Domain (refs F1) \<inter> Domain (refs F2)"
        then show "x \<in> {}"
          using h1a h1c h1d h1e h2a h2c h2d h2e h3a
          by (auto simp add: refs_def relOfGr_def refsG_def withRsG_def adjacent_def 
            EsRP_def rst_fun_def NsP_def NsTy_def EsR_def restrict_map_def EsTy_def, blast)
      qed
    next
      show "{} \<subseteq> Domain (refs F1) \<inter> Domain (refs F2)"
        by (auto)
    qed
  qed

    
lemma in_RefsOf_CUPF_1:
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
   and h4: "Range (refs F1) \<inter> Ns (sg F2) = {}" and h5: "v \<in> NsP (sg F1)"
  shows "refsOf (F1 UF F2) v = refsOf F1 v"
  proof -
    from h1 have h1a: "is_wf_sg (sg F1)" by (simp add: is_wf_fr_def is_wf_sg_def)
    from h2 have h2a: "is_wf_sg (sg F2)" by (simp add: is_wf_fr_def is_wf_sg_def)
    from h3 have h3a: "Ns (sg F1) \<inter> Ns (sg F2) = {}" by (auto simp add: disjGs_def)
    from h5 have h5a: "v \<in> Domain (refs F1)"
      using h1 by (simp add: Domain_refs)
    from h5 have "v \<notin> NsP(sg F2)" using h3a h1a h2a by (auto intro!: in_NsP_Ns)
    hence h5b: "v \<notin> Domain (refs F2)" 
      using h1 h2 h3a by (auto simp add:Domain_refs)
    show ?thesis
    proof
      show "refsOf (F1 UF F2) v \<subseteq> refsOf F1 v"
      proof 
        fix x
        assume "x \<in> refsOf (F1 UF F2) v"
        hence "(v, x) \<in> (refs F1)\<^sup>+ \<or>
          (v, x) \<in> (refs F2)\<^sup>+ \<or> (v, x) \<in> (refs F2)\<^sup>+ O Range (refs F2) \<lhd> (refs F1)\<^sup>+"
          using h1 h2 h3 h4 by (simp add: refsOf_def refs_trcl_UF)
        then show "x \<in> refsOf F1 v"
        proof
          assume "(v, x) \<in> (refs F1)\<^sup>+"
          then show "x \<in> refsOf F1 v" by (simp add: refsOf_def)
        next
          apply_end(erule disjE)
          assume "(v, x) \<in> (refs F2)\<^sup>+"
          hence ha: "v \<in> Domain (refs F2)" by (auto simp add: Domain_unfold dest: tranclD)
          then show "x \<in> refsOf F1 v"
            using h5b by auto
        next
          assume "(v, x) \<in> (refs F2)\<^sup>+ O Range (refs F2) \<lhd> (refs F1)\<^sup>+"
          hence ha: "v \<in> Domain (refs F2)" by (auto simp add: Domain_unfold dest: tranclD)
          then show "x \<in> refsOf F1 v"
            using h5b by auto
        qed
      qed
    next
      show "refsOf F1 v \<subseteq> refsOf (F1 UF F2) v"
        using h1 h2 h3 h4 by (auto simp add: refsOf_def Image_def refs_trcl_UF)
    qed
  qed

lemma in_RefsOf_CUPF_2:
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
   and h4: "Range (refs F1) \<inter> Ns (sg F2) = {}" and h5: "v \<in> NsP (sg F2)"
  shows "refsOf (F1 UF F2) v = refsOf F2 v \<union> ((refs F2)\<^sup>+O Range (refs F2) \<lhd>(refs F1)\<^sup>+)``{v}"
  proof -
    from h1 have h1a: "is_wf_sg (sg F1)" by (simp add: is_wf_fr_def is_wf_sg_def)
    from h2 have h2a: "is_wf_sg (sg F2)" by (simp add: is_wf_fr_def is_wf_sg_def)
    from h3 have h3a: "Ns (sg F1) \<inter> Ns (sg F2) = {}" by (auto simp add: disjGs_def)
    from h5 have h5a: "v \<in> Domain (refs F2)"
      using h2 by (simp add: Domain_refs)
    from h5 have "v \<notin> NsP(sg F1)" using h3a h1a h2a by (auto intro!: in_NsP_Ns)
    hence h5b: "v \<notin> Domain (refs F1)" 
      using h1 h2 h3a by (auto simp add:Domain_refs)
    show ?thesis
    proof
      show "refsOf (F1 UF F2) v \<subseteq> refsOf F2 v \<union> ((refs F2)\<^sup>+O Range (refs F2) \<lhd> (refs F1)\<^sup>+)``{v}"
      proof 
        fix x
        assume "x \<in> refsOf (F1 UF F2) v"
        hence "(v, x) \<in> (refs F1)\<^sup>+ \<or>
          (v, x) \<in> (refs F2)\<^sup>+ \<or> (v, x) \<in> (refs F2)\<^sup>+ O Range (refs F2) \<lhd> (refs F1)\<^sup>+"
          using h1 h2 h3 h4 by (simp add: refsOf_def refs_trcl_UF)
        then show "x \<in> refsOf F2 v \<union> ((refs F2)\<^sup>+O Range (refs F2) \<lhd>(refs F1)\<^sup>+)``{v}"
        proof
          assume "(v, x) \<in> (refs F1)\<^sup>+"
          hence ha: "v \<in> Domain (refs F1)" by (auto simp add: Domain_unfold dest: tranclD)
          then show "x \<in> refsOf F2 v \<union> ((refs F2)\<^sup>+O Range (refs F2) \<lhd> (refs F1)\<^sup>+)``{v}" using h5b by auto
        next
          apply_end(erule disjE)
          assume "(v, x) \<in> (refs F2)\<^sup>+"
          then show "x \<in> refsOf F2 v \<union> ((refs F2)\<^sup>+O Range (refs F2) \<lhd>(refs F1)\<^sup>+)``{v}" by (simp add: refsOf_def)
        next
          assume "(v, x) \<in> (refs F2)\<^sup>+ O Range (refs F2) \<lhd> (refs F1)\<^sup>+"
          then show "x \<in> refsOf F2 v \<union> ((refs F2)\<^sup>+O Range (refs F2) \<lhd>(refs F1)\<^sup>+)``{v}"
            by (auto simp add: refsOf_def relcomp_unfold dres_def)
        qed
      qed
    next
      show "refsOf F2 v \<union> ((refs F2)\<^sup>+ O Range (refs F2) \<lhd> (refs F1)\<^sup>+) `` {v} \<subseteq> refsOf (F1 UF F2) v"
        using h1 h2 h3 h4 by (auto simp add: refsOf_def Image_def refs_trcl_UF dres_def 
            relcomp_unfold)
    qed
  qed

lemma in_nonPRefsOf_CUPF_1:
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
  and h4: "Range (refs F1) \<inter> Ns (sg F2) = {}" and h5: "v \<in> NsP (sg F1)"
  shows "nonPRefsOf (F1 UF F2) v = nonPRefsOf F1 v"
  proof -
    from h1 have h1a: "is_wf_sg (sg F1)" by (simp add: is_wf_fr_def is_wf_sg_def)
    from h2 have h2a: "is_wf_sg (sg F2)" by (simp add: is_wf_fr_def is_wf_sg_def)
    show ?thesis
    proof
      show "nonPRefsOf (F1 UF F2) v \<subseteq> nonPRefsOf F1 v"
      proof
        fix x
        assume "x \<in> nonPRefsOf (F1 UF F2) v"
        then show "x \<in> nonPRefsOf F1 v"
          using h1 h2 h3 h4 h5 h1a h2a
            by (auto simp add: nonPRefsOf_def in_RefsOf_CUPF_1 NsP_disj_dist)
      qed
    next
      show "nonPRefsOf F1 v \<subseteq> nonPRefsOf (F1 UF F2) v"
      proof
        fix x
        assume ha: "x \<in> nonPRefsOf F1 v"
        hence "x \<in> Range ((refs F1)\<^sup>+)"
          by (auto simp add: nonPRefsOf_def refsOf_def Range_def)
        hence hb: "x \<in> Range (refs F1)" by (simp)
        then show "x \<in> nonPRefsOf (F1 UF F2) v"
          using h1 h2 h3 h4 h5 h1a h2a ha 
          by (auto simp add: nonPRefsOf_def in_RefsOf_CUPF_1 NsP_disj_dist intro: in_NsP_Ns)
      qed
    qed
 qed

(*lemma in_nonPRefsOf_CUPF_2:
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
  and h4: "Range (refs F1) \<inter> Ns (sg F2) = {}" and h5: "v \<in> NsP (sg F2)"
  shows "nonPRefsOf (F1 UF F2) v = nonPRefsOf F2 v"
  proof -
    from h1 have h1a: "is_wf_sg (sg F1)" by (simp add: is_wf_fr_def is_wf_sg_def)
    from h2 have h2a: "is_wf_sg (sg F2)" by (simp add: is_wf_fr_def is_wf_sg_def)
    show ?thesis
    proof
      show "nonPRefsOf (F1 UF F2) v \<subseteq> nonPRefsOf F2 v"
      proof
        fix x
        assume "x \<in> nonPRefsOf (F1 UF F2) v"
        then show "x \<in> nonPRefsOf F2 v"
          using h1 h2 h3 h4 h5 h1a h2a
            by (auto simp add: nonPRefsOf_def in_RefsOf_CUPF_2 NsP_disj_dist)
      qed*)

lemma dist_cup_proxies_dont_inherit: 
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
  shows "proxies_dont_inherit (F1 UF F2)"
proof - 
  from h1 have h1a: "is_wf_sg (sg F1)" by (simp add: is_wf_fr_def)
  from h1a have h1b: "ftotal_on (src (sg F1)) (Es (sg F1)) (Ns (sg F1))" 
      by (simp add: is_wf_sg_def is_wf_g_def)
  from h1b have h1c: "dom (src (sg F1)) = Es (sg F1)" by (simp add: ftotal_on_def)
  from h1b have h1d: "ran (src (sg F1)) \<subseteq> Ns (sg F1)" by (simp add: ftotal_on_def)
  from h1a have h1e: "ftotal_on (ety (sg F1)) (Es (sg F1)) SGETy_set" 
      by (simp add: is_wf_sg_def)
  from h1e have h1f: "dom (ety (sg F1)) = Es (sg F1)" by (simp add: ftotal_on_def)
  from h1a have h1g: "ftotal_on (nty (sg F1)) (Ns (sg F1)) SGNTy_set" 
      by (simp add: is_wf_sg_def)
  from h1g have h1h: "dom (nty (sg F1)) = Ns (sg F1)" by (simp add: ftotal_on_def)
  have * : "None \<notin> {Some einh}" by simp
  from * h1f have h1i: "EsI (sg F1) \<subseteq> Es (sg F1)" 
    by (simp add: EsI_def EsTy_def vimage_in_dom)
  from * h1h have h1j: "NsP (sg F1) \<subseteq> Ns (sg F1)" 
    by (simp add: NsP_def NsTy_def vimage_in_dom)
  from h2 have h2a: "is_wf_sg (sg F2)" by (simp add: is_wf_fr_def)
  from h2a have h2b: "ftotal_on (src (sg F2)) (Es (sg F2)) (Ns (sg F2))" 
      by (simp add: is_wf_sg_def is_wf_g_def)
  from h2b have h2c: "dom (src (sg F2)) = Es (sg F2)" by (simp add: ftotal_on_def)
  from h2b have h2d: "ran (src (sg F2)) \<subseteq> Ns (sg F2)" by (simp add: ftotal_on_def)
  from h2a have h2e: "ftotal_on (ety (sg F2)) (Es (sg F2)) SGETy_set" 
      by (simp add: is_wf_sg_def)
  from h2e have h2f: "dom (ety (sg F2)) = Es (sg F2)" by (simp add: ftotal_on_def)
  from h2a have h2g: "ftotal_on (nty (sg F2)) (Ns (sg F2)) SGNTy_set" 
      by (simp add: is_wf_sg_def)
  from h2g have h2h: "dom (nty (sg F2)) = Ns (sg F2)" by (simp add: ftotal_on_def)
  from * h2f have h2g: "EsI (sg F2) \<subseteq> Es (sg F2)" 
    by (simp add: EsI_def EsTy_def vimage_in_dom)
  from * h2h have h2j: "NsP (sg F2) \<subseteq> Ns (sg F2)" 
    by (simp add: NsP_def NsTy_def vimage_in_dom)
  from h3 have h3a: "Es (sg F1) \<inter> Es (sg F2) = {}" 
    by (simp add: disjGs_def disjEsGs_def)
  from h3 have h3b: "Ns (sg F1) \<inter> Ns (sg F2) = {}" 
    by (simp add: disjGs_def)
  have h4: "src (sg F1) |` (EsI (sg F1) \<union> EsI (sg F2)) = src (sg F1) |` EsI (sg F1)"
    proof -
     from h1c h1g h2g h3a have *: "EsI (sg F2) \<inter> dom(src (sg F1)) = {}" by (auto)
     from * h1i h1c show "src (sg F1) |` (EsI (sg F1) \<union> EsI (sg F2)) = src (sg F1) |` EsI (sg F1)"
        by (simp add: disj_fun_vimage_Un)
    qed
  have h5: "src (sg F2) |` (EsI (sg F1) \<union> EsI (sg F2)) = src (sg F2) |` EsI (sg F2)"
    proof -
     from h2c h1i h2g h3a have *: "EsI (sg F1) \<inter> dom(src (sg F2)) = {}" by (auto)
     have hs: "EsI (sg F1) \<union> EsI (sg F2) = EsI (sg F2) \<union> EsI (sg F1)" by (auto)
     from * h2g h2c show "src (sg F2) |` (EsI (sg F1) \<union> EsI (sg F2)) = src (sg F2) |` EsI (sg F2)"
        by (simp add: hs disj_fun_vimage_Un)
    qed
  from h1c h2c h1f h2f h3a 
    have h6: "dom (src (sg F1) |` EsI (sg F1)) \<inter> dom (src (sg F2) |` EsI (sg F2)) = {}"
    by (auto)
  from h1 have h7: "proxies_dont_inherit F1" by (simp add: is_wf_fr_def)
  from h7 have h7a: "ran (src (sg F1) |` EsI (sg F1)) \<inter> NsP (sg F1) = {}" 
    by (simp add: proxies_dont_inherit_def)
  from h2 have h8: "proxies_dont_inherit F2" by (simp add: is_wf_fr_def)
  from h8 have h8a: "ran (src (sg F2) |` EsI (sg F2)) \<inter> NsP (sg F2) = {}" 
    by (simp add: proxies_dont_inherit_def)
  from h1a h1d h2a h2d h3 h6 h3b h7a h8a h1j h2j show "proxies_dont_inherit (F1 UF F2)"
  by (auto simp add: proxies_dont_inherit_def cupF_def NsP_disj_dist EsI_disj_dist 
    map_add_restrict_dist h4 h5, 
    insert ran_restrict_sub[where f="src (sg F1)" and A="EsI (sg F1)"],
    insert ran_restrict_sub[where f="src (sg F2)" and A="EsI (sg F2)"], auto)
    (subgoal_tac "x \<in> Ns (sg F1)", auto, subgoal_tac "x \<in> Ns (sg F2)", auto)
qed  

lemma tgtr_restrict_map_EsRP[simp]:
  assumes h: "is_wf_fr F"
  shows "tgtr F |` (EsRP (sg F)) = tr F"
  proof -
    from h have h1a: "dom (tr F) = EsRP (sg F)"
      by (simp add: is_wf_fr_def ftotal_on_def)
      show ?thesis
      proof
        fix x
        from h1a show "(tgtr F |` EsRP (sg F)) x = tr F x"
          by (auto simp add: tgtr_def restrict_map_def map_add_def split: option.splits)
      qed
  qed

lemma in_EsRP_and_in_tgtr_in_tr[simp]:
  assumes h1: "is_wf_fr F" and h2: "e \<in> EsRP (sg F)"
  shows "tgtr F e = tr F e"
  proof - 
    from h1 have h1a: "dom (tr F) = EsRP(sg F)"
      by (simp add: is_wf_fr_def ftotal_on_def)
    from h1a h2 show ?thesis
      by (auto simp add: tgtr_def map_add_def split: option.splits)
  qed

lemma disjEsGs_inhRefsG:
  assumes h1: "is_wf_fr F"
  shows "disjEsGs (inhG (sg F)) (refsG F)"
  proof -
    from h1 have h1a: "dom (src (sg F)) = Es (sg F)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    have h2: "Es (sg F) \<inter> (EsI (sg F) - EsId (sg F)) \<inter> (Es (sg F) \<inter> EsRP (sg F)) = 
        (EsI (sg F) - EsId (sg F)) \<inter> EsRP (sg F)"
        using h1a
        by (auto simp add: EsI_def EsId_def EsRP_def EsTy_def NsP_def NsTy_def)
    show ?thesis
    using h1a
    by (simp add: disjEsGs_def h2)
      (auto simp add: EsI_def EsId_def EsRP_def EsTy_def NsP_def NsTy_def EsR_def)
  qed

lemma is_wf_inhRefsG: 
  assumes h1: "is_wf_fr F"
  shows "is_wf_g (inhRefsG F)"
 proof -
    from h1 have h1a: "is_wf_g (sg F)"
      by (simp add: is_wf_fr_def is_wf_sg_def)
    from h1 have h1b: "dom (tr F) \<subseteq> Es (sg F)"
      by (auto simp add: is_wf_fr_def is_wf_sg_def ftotal_on_def EsRP_def EsR_def EsTy_def)
    from h1 have h1c: "ran (tr F) \<subseteq> V_A"
      by (simp add: is_wf_fr_def ftotal_on_def)
    from h1 have h2: "is_wf_g (refsG F)"
      by (simp add: is_wf_refsG)
    from h1 have h3: "is_wf_g (inhG (sg F))"
      by (simp add: is_wf_fr_def is_wf_g_inhG is_wf_sg_def)
    from h1a h1b h1c h2 h3 show ?thesis
      by (simp add: inhRefsG_def is_wf_g_Un)
  qed

lemma inh_refs_and_inhRefsG: 
  assumes h1: "is_wf_fr F"
  shows "inh (sg F) \<union> refs F = relOfGr(inhRefsG F)"
  proof -
    from h1 have h2: "is_wf_g (refsG F)"
      by (simp add: is_wf_refsG)
    from h1 have h3: "is_wf_g (inhG (sg F))"
      by (simp add: is_wf_fr_def is_wf_g_inhG is_wf_sg_def)
    from h1 have h4: "disjEsGs (inhG (sg F)) (refsG F)" 
      by (simp add: disjEsGs_inhRefsG)
    from h2 h3 h4 show ?thesis
      by (simp add: inhRefsG_def refs_def inh_def relOfGr_UG)
  qed

lemma inhRefsG_partitions:
  shows "inhRefsG F = inhG (sg F) UG refsG F"
    by (auto simp add: inhRefsG_def)

lemma is_acyclic_inhRefsG: 
  assumes h1: "is_wf_fr F"
  shows "acyclicGr (inhRefsG F)"
  proof -
    from h1 have h1a: "acyclic_fr F"
      by (simp add: is_wf_fr_def)
    from h1 h1a show ?thesis
      by (simp add: acyclic_fr_def acyclicGr_def inh_refs_and_inhRefsG)
  qed

definition consSubOfFr:: "Fr \<Rightarrow>(V \<rightharpoonup> V)"
where 
  "consSubOfFr F \<equiv> (\<lambda>v. if (\<exists> v2. nonPRefsOf F v = {v2}) then 
    Some (SOME v2. (nonPRefsOf F v) = {v2}) else None)"

lemma in_consSubOfFr:
  shows "(consSubOfFr F v = Some v2) \<longleftrightarrow> (nonPRefsOf F v) = {v2}"
  proof
    show "consSubOfFr F v = Some v2 \<Longrightarrow> nonPRefsOf F v = {v2}"
      by (simp add: consSubOfFr_def nonPRefsOf_def refsOf_def split: if_splits)
  next
    assume "nonPRefsOf F v = {v2}"
    then show "consSubOfFr F v = Some v2"
      by (simp add: consSubOfFr_def)
  qed

(*lemma in_consSubOfFr:
  assumes h1: "is_wf_fr F" and h2: "e1 \<in> EsRP (sg F)"
    and h3: "src (sg F) e1 = Some x" and h4: "(consSubOfFr F) x = Some v"
  shows "\<exists> e2. e2 \<in> EsRP (sg F) \<and> tr F e2 = Some v"
  proof -
    from h1 have h1a: "inj_on (src (sg F)) (EsRP (sg F))"
      by (simp add: is_wf_fr_def)
    from h1a h2 h3 have h5: "inv_into (EsRP (sg F)) (src (sg F)) (Some x) = e1"
      by (simp add: inv_into_f_eq)
    from h5 h4 show ?thesis
      by (auto simp add: consSubOfFr_def pick_elem_def Image_def split: if_splits)
  qed*)

lemma dom_consSubOfFr[simp]: 
  assumes h1: "is_wf_fr F"
  shows "dom (consSubOfFr F) = NsP (sg F)"
  proof -
    from h1 have h1a: "inj_on (src (sg F)) (EsRP (sg F))"
      by (simp add: is_wf_fr_def)
    from h1 have h1b: "ran (src (sg F)|`EsRP (sg F)) = NsP (sg F)"
      by (simp add: is_wf_fr_def)
    from h1 have h1c: "dom (tr F) = EsRP (sg F)" 
      by (simp add: is_wf_fr_def ftotal_on_def)
    from h1 have h1d: "(\<forall> v. v \<in> NsP (sg F) \<longrightarrow> nonPRefsOf F v \<noteq> {})"
      by (simp add: is_wf_fr_def)
    show ?thesis
    proof
      show "dom (consSubOfFr F) \<subseteq> NsP (sg F)"
      proof
        fix x
        assume "x \<in> dom (consSubOfFr F)"
        hence "\<exists> y. consSubOfFr F x = Some y" by (simp add: dom_def)
        hence "\<exists> y. y \<in> nonPRefsOf F x" by (simp add: consSubOfFr_def split: if_splits)
        hence "x \<in> Domain (refs F)" 
          using trancl_domain[of "refs F"] 
          by (auto simp add: nonPRefsOf_def refsOf_def Domain_def)
        then show "x \<in> NsP (sg F)"
          using h1 by (simp add: Domain_refs)
      qed
    next
      show "NsP (sg F) \<subseteq> dom (consSubOfFr F)"
      proof
        fix v
        assume h2: "v \<in> NsP (sg F)"
        hence h2a: "v \<in> ran (src (sg F)|`EsRP (sg F))" using h1b 
          by (auto simp add: ran_def split: if_splits)
        from h2a have h2b: "\<exists> e. e \<in> EsRP (sg F) \<and> src (sg F) e = Some v" 
          by (auto simp add: ran_def restrict_map_def split: if_splits)
        from h2b show "v \<in> dom (consSubOfFr F)"
        proof 
          apply_end(erule conjE)
          fix e 
          assume h3a: "e \<in> EsRP (sg F)"
          assume h3b: "src (sg F) e = Some v"
          from h3a h3b have h3c: "v \<in> NsP (sg F)" by (simp add: EsRP_def)
          from h3a h3b h1c have h3d: "\<exists> v2. tr F e = Some v2" 
            by auto
          from h1d h3c have h3e: "nonPRefsOf F v \<noteq> {}" by auto
          hence h3f: "\<exists> v2. v2 \<in> nonPRefsOf F v" by auto
          then show "v \<in> dom (consSubOfFr F)"
          proof
            fix v2
            assume h3f: "v2 \<in> nonPRefsOf F v"
            hence h3g: "v2 \<notin> NsP(sg F)" by (auto simp add: nonPRefsOf_def)
            then show "v \<in> dom (consSubOfFr F)"  
              using h1 h3c h3f by (auto simp add: consSubOfFr_def split: if_splits)
                (rule_tac exI[where x="v2"], auto simp add: is_single_valued_nonPRefsOf)
         qed
        qed
      qed
    qed
  qed

(*lemma consSubOfFr_reduce: (*HERE. NEED TRCL, right?*)
  assumes h1: "is_wf_fr F" and h2: "(consSubOfFr F) x = Some v"
  shows "\<exists> e. e \<in> EsRP (sg F) \<and> src (sg F) e = Some x \<and> tr F e = Some v"
  proof -
    from h1 have h1a: "inj_on (src (sg F)) (EsRP (sg F))"
      by (simp add: is_wf_fr_def)
    from h1 have h1b: "ran (src (sg F) |` EsRP (sg F)) = NsP (sg F)"
      by (simp add: is_wf_fr_def)
    from h1 h2 have h2a: "x \<in> NsP (sg F)" 
      using dom_def[of "consSubOfFr F"]
      by (auto)
    from h2a h1b have h2b: "x \<in> ran (src (sg F)|` EsRP (sg F))" 
      by (auto)
    hence h2c: "\<exists> e. src (sg F) e = Some x \<and> e \<in> EsRP (sg F)" 
      by (auto simp add: ran_def restrict_map_def split: if_splits)
    from h2c show ?thesis
    proof
      apply_end(erule conjE)
      fix e
      assume h3: "src (sg F) e = Some x"
      assume h4: "e \<in> EsRP (sg F)"
      from h1 h2 h3 h4 h1a show ?thesis
        by (rule_tac exI[where x="e"])
        (simp add: consSubOfFr_def inv_into_f_eq is_single_valued_nonPRefsOf split: if_splits)
    qed
  qed*)

lemma ran_consSubOfFr_sub_tr: 
  assumes h1: "is_wf_fr F"
  shows "ran (consSubOfFr F) \<subseteq> ran (tr F)"
    using h1 by (auto simp add: consSubOfFr_def ran_def in_nonPRefsOf_in_tr split: if_splits) 

lemma ran_consSubOfFr_in_nonPRefsOf: 
  assumes h1: "x \<in> ran (consSubOfFr F)"
  shows "\<exists> v. x \<in> nonPRefsOf F v"
  proof -
    from h1 have "\<exists>v. consSubOfFr F v = Some x" by (simp add: ran_def)
    hence "\<exists>v. nonPRefsOf F v = {x}" by (simp add: in_consSubOfFr)
    hence "\<exists>v. x \<in> nonPRefsOf F v" by auto
    then show ?thesis by (simp)
  qed

lemma disj_dom_ran_consSubOfFr: 
  assumes h: "is_wf_fr F"
  shows "dom (consSubOfFr F) \<inter> ran (consSubOfFr F) = {}"
  proof -
    show ?thesis
    proof
      show "dom (consSubOfFr F) \<inter> ran (consSubOfFr F) \<subseteq> {}"
      proof
        fix x
        assume h2a: "x \<in> dom (consSubOfFr F) \<inter> ran (consSubOfFr F)"
        hence h2b: "x \<in> NsP(sg F)" using h by auto
        from h2a have h2c: "\<exists>v. x \<in> nonPRefsOf F v" by (simp add: ran_consSubOfFr_in_nonPRefsOf)
        hence "x \<notin> NsP (sg F)"by (simp add: nonPRefsOf_def)
        then show "x \<in> {}" using h2b by auto
      qed
    next
      show "{} \<subseteq> dom (consSubOfFr F) \<inter> ran (consSubOfFr F)" by simp
    qed
  qed

lemma disjoint_dom_ran_inhG_partitions:
  assumes h1: "is_wf_fr F" 
  and h2: "G1 = inhGWithoutNsP (sg F)"
  and h3: "G2 = inhGRestrictedToNsP (sg F)"
  shows "Domain (relOfGr G1) \<inter> Range (relOfGr G2) = {}"
  proof -
    from h1 have h1a: "dom (src (sg F)) = Es (sg F)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1b: "ran (src (sg F) |` EsI (sg F)) \<inter> NsP (sg F) = {}" 
      by (simp add: is_wf_fr_def proxies_dont_inherit_def)
    from h1 have h4: "(Es (sg F) \<inter> (EsI (sg F) - EsId (sg F)) - EsP (sg F)) 
      =  (EsI (sg F) - EsId (sg F)) - EsP (sg F)"
      by (auto simp add: EsI_def is_wf_fr_def is_wf_sg_def ftotal_on_def EsTy_def)
    have h5: "ran (src (G1)) \<inter> ran (tgt (G2)) = {}"
      proof 
        show "ran (src G1) \<inter> ran (tgt G2) \<subseteq> {}"
        proof
          fix x
          from h1 have ha: "Es (sg F) \<inter> (EsI (sg F) - EsId (sg F)) - EsP (sg F)
            = (EsI (sg F) - EsId (sg F)) - EsP (sg F)"
            by (auto simp add: is_wf_fr_def intro: in_EsI_in_Es)
          assume h5a: "x \<in> ran (src G1) \<inter> ran (tgt G2)"
          hence "x \<in> ran (src G1)"  by simp
          hence h5b: "x \<in> ran (rst_fun ((EsI (sg F) - EsId (sg F)) - EsP (sg F)) 
            (src (inhG (sg F))))"
            using ha by (auto simp add: h2 h3 inhGRestrictedToNsP_def inhGWithoutNsP_def)
          hence h5c: "x \<in> ran (src (inhG (sg F))) \<and> x \<notin> NsP (sg F)" 
            using h1a 
            by (auto simp add: rst_fun_def restrict_map_def ran_def EsP_def 
              split: if_splits intro: ranI)
          from h5a have h5d: "x \<in> ran (rst_fun (EsP (sg F)) (tgt (inhG (sg F))))"
            by (simp add: rst_fun_def h2 h3 inhGRestrictedToNsP_def inhGWithoutNsP_def)
          from h5d h1b have h5e: "x \<in> ran (tgt (inhG (sg F))) \<and> x \<in> NsP (sg F)"
            by (auto simp add: rst_fun_def restrict_map_def ran_def EsP_def 
              split: if_splits intro: ranI)
          from h5c h5e show "x \<in> {}" 
            by (auto simp add: rst_fun_def restrict_map_def ran_def split: if_splits)
        qed
      next
        show "{} \<subseteq> ran (src G1) \<inter> ran (tgt G2)"
          by auto
      qed
      show ?thesis
       using h5 Domain_relOfGr[of G1] Range_relOfGr[of G2]
        by (simp only: h2 h3 h4)(auto)   
  qed

lemma replace_in_trcl_inhRefsG:
  assumes h1: "is_wf_fr F"
  shows "relOfGr(replaceGr(inhG (sg F)) (consSubOfFr F)) \<subseteq> (relOfGr(inhRefsG F))\<^sup>+"
  proof -
    from h1 have h1a: "is_wf_sg (sg F)"
      by (simp add: is_wf_fr_def)
    from h1a have h1b: "is_wf_g (sg F)"
      by (simp add: is_wf_sg_def)
    from h1b have h1c: "dom(src (sg F)) = Es (sg F)"
      by (simp add: is_wf_g_def ftotal_on_def)
    from h1 have h1d: "proxies_dont_inherit F"
      by (simp add: is_wf_fr_def)
    (*from h1 have h1e: "ran (tr F) \<inter> NsP (sg F) = {}"
      by (simp add: is_wf_fr_def)*)
    from h1 have h1f: "dom (tr F) = EsRP (sg F)"
      by (simp add: is_wf_fr_def ftotal_on_def)
    from h1a have h2a: "is_wf_g (inhG (sg F))"
      by (simp add: is_wf_g_inhG is_wf_sg_def)
    from h2a have h2b: "is_wf_g (inhGWithoutNsP (sg F))"
      by (simp add: inhGWithoutNsP_def is_wf_restrict)
    from h2a have h2c:  "is_wf_g (inhGRestrictedToNsP (sg F))"
      by (simp add: is_wf_restrict inhGRestrictedToNsP_def)
    from h1 have h2d: "is_wf_g (refsG F)"
      by (simp add: is_wf_refsG)
    have h2e: "disjEsGs (inhG (sg F)) (refsG F)" 
      by (auto simp add: inhG_def refsG_def disjEsGs_def EsI_def EsRP_def EsTy_def EsR_def)
    from h1 have h3a: "dom (consSubOfFr F) \<inter> Ns (inhGWithoutNsP (sg F)) = {}"
      using No_NsP_in_inhGWithoutNsP[of "sg F"]
      by (auto simp add: rst_Ns_def rst_fun_def inhGWithoutNsP_def)
    from h1 h1a h1b have h3b: "dom (consSubOfFr F) \<subseteq> V_A"
      by (auto simp add: is_wf_g_def intro: in_NsP_Ns)
    from h1 have h3c: "ran (consSubOfFr F) \<subseteq> V_A"
      using ran_consSubOfFr_sub_tr[of F]
      by (auto simp add: is_wf_fr_def ftotal_on_def)
    from h1 have h3d: "dom (consSubOfFr F) \<inter> ran (consSubOfFr F) = {}"
      by (simp only: disj_dom_ran_consSubOfFr)
    from h2c h3b h3c h3d
      have h4: "is_wf_g (replaceGr (inhGRestrictedToNsP (sg F)) (consSubOfFr F))"
      by (auto simp add: is_wf_replace)
    have h5: "disjEsGs (inhGWithoutNsP (sg F))
      (replaceGr (inhGRestrictedToNsP (sg F)) (consSubOfFr F))"
      by (auto simp add: inhGRestrictedToNsP_def inhGWithoutNsP_def disjEsGs_def)
    show ?thesis
    proof (rule subrelI)
      fix x y
      assume "(x, y) \<in> relOfGr (replaceGr (inhG (sg F)) (consSubOfFr F))"
      hence "(x, y) \<in> relOfGr (inhGWithoutNsP (sg F) 
          UG replaceGr (inhGRestrictedToNsP (sg F)) (consSubOfFr F))"
        using inhG_partition_NsP h1a h2b h3a
        by (simp add: replace_neutral)
      hence "(x, y) \<in> relOfGr (inhGWithoutNsP (sg F)) 
        \<or> (x, y) \<in> relOfGr (replaceGr (inhGRestrictedToNsP (sg F)) (consSubOfFr F))"
        using h2b h4 h5 by (simp add: relOfGr_UG)
      then show "(x, y) \<in> (relOfGr (inhRefsG F))\<^sup>+"
      proof
        have ha: "disjEsGs (inhG (sg F)) (refsG F)"
          by (auto simp add: disjEsGs_def EsI_def EsRP_def EsTy_def EsR_def)
        have hb: "disjEsGs (inhGWithoutNsP (sg F))
          (inhGRestrictedToNsP (sg F))"
          by (auto simp add: inhGRestrictedToNsP_def inhGWithoutNsP_def disjEsGs_def)
        assume "(x, y) \<in> relOfGr (inhGWithoutNsP (sg F))"
        hence "(x, y) \<in> relOfGr (inhRefsG F)"
          using h2d h2a ha h1a inhG_partition_NsP[of "sg F"] hb h2b h2c
          by (simp add: inhRefsG_partitions relOfGr_UG)
        then show "(x, y) \<in> (relOfGr (inhRefsG F))\<^sup>+" by auto
      next
        assume "(x, y) \<in> relOfGr (replaceGr (inhGRestrictedToNsP (sg F)) (consSubOfFr F))"
        hence "\<exists> e. e \<in> Es (inhGRestrictedToNsP (sg F)) 
          \<and> replace_emap (src (inhGRestrictedToNsP (sg F))) (consSubOfFr F) e = Some x 
          \<and> replace_emap (tgt (inhGRestrictedToNsP (sg F))) (consSubOfFr F) e = Some y"
          by (simp add: relOfGr_replace)
        then show "(x, y) \<in> (relOfGr (inhRefsG F))\<^sup>+"
        proof
          apply_end(clarify)
          fix e
          assume h6a: "e \<in> Es (inhGRestrictedToNsP (sg F))" 
          assume h6b: "replace_emap (src (inhGRestrictedToNsP (sg F))) (consSubOfFr F) e = Some x"
          hence h6c: "(\<exists> v. consSubOfFr F v = Some x \<and> src (inhGRestrictedToNsP (sg F)) e = Some v) 
            \<or> the (src (inhGRestrictedToNsP (sg F)) e) \<notin> dom (consSubOfFr F) \<and> 
              src (inhGRestrictedToNsP (sg F)) e = Some x"
            by (simp add: replace_emap_reduce)
          from h1 h1c h1d have h6d: "ran(src (inhGRestrictedToNsP (sg F))) \<inter> NsP (sg F) = {}"
            by (auto simp add: proxies_dont_inherit_def inhGRestrictedToNsP_def rst_fun_def 
              restrict_map_def ran_def split: if_splits)
          hence h6e: "src (inhGRestrictedToNsP (sg F)) e = Some x"
              using h1 h6c by (auto)(subgoal_tac "v \<in> NsP (sg F)", 
                insert dom_def[of "consSubOfFr F"], auto intro: domI ranI)
          assume h6f: "replace_emap (tgt (inhGRestrictedToNsP (sg F))) (consSubOfFr F) e = Some y"
          hence h6g: "(\<exists> v. consSubOfFr F v = Some y 
              \<and> tgt (inhGRestrictedToNsP (sg F)) e = Some v) 
            \<or> (the (tgt (inhGRestrictedToNsP (sg F)) e) \<notin> dom (consSubOfFr F) 
              \<and> tgt (inhGRestrictedToNsP (sg F)) e = Some y)"
            by (auto simp add: replace_emap_reduce)
          from h6g have h6h: "\<exists> v. consSubOfFr F v = Some y \<and> tgt (inhGRestrictedToNsP (sg F)) e = Some v"
          proof 
            apply_end(simp, clarify)
            have ha: "ran (tgt (inhGRestrictedToNsP (sg F))) \<subseteq> NsP (sg F)"
              using h1d by (auto simp add: inhGRestrictedToNsP_def proxies_dont_inherit_def 
                rst_fun_def restrict_map_def ran_def EsP_def
                split: if_splits)
            assume hb: "tgt (inhGRestrictedToNsP (sg F)) e = Some y"
            hence hc: "y \<in> NsP (sg F)" using ha by (auto intro: ranI)
            from h1 hc have hd: "y \<in> dom(consSubOfFr F)" by auto
            assume he: "\<not> (\<exists>v. consSubOfFr F v = Some y \<and> tgt (inhGRestrictedToNsP (sg F)) e = Some v)"
            from hb hc hd he show 
              "\<exists>y. consSubOfFr F (the (tgt (inhGRestrictedToNsP (sg F)) e)) = Some y"
              by (auto)
          qed
          from h6h show "(x, y) \<in> (relOfGr (inhRefsG F))\<^sup>+"
          proof
            apply_end(erule conjE)
            fix v
            assume h7a: "consSubOfFr F v = Some y"
            assume h7b: "tgt (inhGRestrictedToNsP (sg F)) e = Some v"
            hence h7c: "tgt (sg F) e = Some v" 
              using h6a by (auto simp add: inhGRestrictedToNsP_def rst_fun_def
                restrict_map_def split: if_splits)
            from h6e have h7d: "src (sg F) e = Some x" 
              using h6a by (auto simp add: inhGRestrictedToNsP_def rst_fun_def
                restrict_map_def split: if_splits)
            have "(x, y) \<in> (relOfGr (inhRefsG F)) O (relOfGr (inhRefsG F))\<^sup>+"
            proof (simp add: relcomp_unfold)
              apply_end(rule exI[where x="v"]) apply_end(rule conjI)
              show "(x, v) \<in> relOfGr (inhRefsG F)"
                using h1 h2a h2d h6a h7c h7d disjEsGs_inhRefsG[of F] 
                by (simp add: inhRefsG_def relOfGr_UG)
                (rule disjI1, auto simp add: relOfGr_def adjacent_def rst_fun_def,
                  rule exI[where x="e"], auto simp add: inhGRestrictedToNsP_def restrict_map_def)
            next
              from h7a have "nonPRefsOf F v = {y}" by (simp add: consSubOfFr_def split: if_splits)
              hence "y \<in> nonPRefsOf F v" by simp
              hence h8a: "(v, y) \<in> (refs F)\<^sup>+" by (simp add: nonPRefsOf_def refsOf_def)
              then show "(v, y) \<in> (relOfGr (inhRefsG F))\<^sup>+"
                using h1 h2d h2a h2e 
                  trcl_parts_in_whole[of "relOfGr (inhG (sg F))" "relOfGr (refsG F)"]
                by (auto simp add: refs_def inhRefsG_def relOfGr_UG)
            qed
            then show "(x, y) \<in> (relOfGr (inhRefsG F))\<^sup>+"
              by auto
          qed
        qed
      qed
    qed
  qed

(*Shows that given current local contraints of fragments, 
  underlying graph is inheritance-acyclic*)
lemma is_acyclic_replaces_inhG:
  assumes h1: "is_wf_fr F" 
  shows "acyclicGr (replaceGr(inhG (sg F)) (consSubOfFr F))"
  proof -
    have h2: "acyclic (relOfGr (replaceGr (inhG (sg F)) (consSubOfFr F)))" 
      using h1 replace_in_trcl_inhRefsG[of F] is_acyclic_inhRefsG[of F]
      by (auto simp add: acyclicGr_def rel_subset_acyclic_trcl)
    show ?thesis
      by (simp add: acyclicGr_def h2)
  qed


lemma disjEsGs_disjEs_refsG: 
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjEsGs (sg F1) (sg F2)"
  shows "disjEsGs (refsG F1) (refsG F2)"
  proof -
    from h1 have h1a: "is_wf_sg (sg F1)" by (simp add: is_wf_fr_def)
    from h2 have h2a: "is_wf_sg (sg F2)" by (simp add: is_wf_fr_def)
    from h3 have h3a: "Es (sg F1) \<inter> Es (sg F2) = {}" by (simp add: disjEsGs_def)
    from assms h1a h2a h3a show ?thesis
      by (auto simp add: disjEsGs_def intro!: in_EsRP_in_Es)
  qed

lemma reps_UF:
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
  shows "reps (F1 UF F2) = reps (F1) \<union> reps (F2)"
  proof 
    show "reps (F1 UF F2) \<subseteq> reps F1 \<union> reps F2"      
    proof (rule subrelI)
      fix x y
      assume "(x, y) \<in> reps (F1 UF F2)"
      then show "(x, y) \<in> reps F1 \<union> reps F2"
        using h1 h2 h3 by (auto simp add: reps_def refs_UF)
    qed
  next
    show "reps F1 \<union> reps F2 \<subseteq> reps (F1 UF F2)"
    proof (rule subrelI)
      fix x y
      assume "(x, y) \<in> reps F1 \<union> reps F2"
      then show "(x, y) \<in> reps (F1 UF F2)"
        using h1 h2 h3 by (auto simp add: reps_def refs_UF)
    qed
 qed

(*lemma repsst_UnF_dist:
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
    and h4: "Range (refs F1) \<inter> Ns (sg F2) = {}"
  shows "(reps (F1 UF F2))\<^sup>* = (reps (F1))\<^sup>* \<union> (reps (F2))\<^sup>*"
  proof -
    show ?thesis
    proof
      show "(reps (F1 UF F2))\<^sup>* \<subseteq> (reps F1)\<^sup>* \<union> (reps F2)\<^sup>*"
      proof (rule subrelI)
        fix x y
        assume "(x, y) \<in> (reps (F1 UF F2))\<^sup>*"
        then show "(x, y) \<in> (reps F1)\<^sup>* \<union> (reps F2)\<^sup>*"
        proof (induct)
          show "(x, x) \<in> (reps F1)\<^sup>* \<union> (reps F2)\<^sup>*" by auto
        next
          fix y z
          assume h5: "(x, y) \<in> (reps (F1 UF F2))\<^sup>*"
          assume h6: "(y, z) \<in> reps (F1 UF F2)"
          hence h6a: "(y, z) \<in> reps F1 \<or> (y, z) \<in> reps F2"
            using h1 h2 h3 by (simp add: reps_UnF_dist)
          assume h7: "(x, y) \<in> (reps F1)\<^sup>* \<union> (reps F2)\<^sup>*"
          then show "(x, z) \<in> (reps F1)\<^sup>* \<union> (reps F2)\<^sup>*"
          proof
            assume h8: "(x, y) \<in> (reps F1)\<^sup>*"
            from h6a show "(x, z) \<in> (reps F1)\<^sup>* \<union> (reps F2)\<^sup>*"
            proof
              assume h9a: "(y, z) \<in> reps F1"
              then show "(x, z) \<in> (reps F1)\<^sup>* \<union> (reps F2)\<^sup>*"
                using h8 by auto
            next
              assume h9a: "(y, z) \<in> reps F2"
              from h8 have h8a: "x = y \<or> x\<noteq> y \<and> (x, y) \<in> (reps F1)\<^sup>+"
                by (simp add: rtrancl_eq_or_trancl)
              then show "(x, z) \<in> (reps F1)\<^sup>* \<union> (reps F2)\<^sup>*"
              proof
                assume "x=y"
                then show "(x, z) \<in> (reps F1)\<^sup>* \<union> (reps F2)\<^sup>*"
                  using h9a by auto
              next
                assume "x\<noteq> y \<and> (x, y) \<in> (reps F1)\<^sup>+"
                then show "(x, z) \<in> (reps F1)\<^sup>* \<union> (reps F2)\<^sup>*"
                  using h9a by auto
  qed*)
(*lemma disjGs_withRsG:
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
  shows "disjGs (withRsG F1) (withRsG F2)"
  proof -
    from h1 have h1a: "is_wf_g (sg F1)" 
      by (simp add: is_wf_fr_def is_wf_sg_def)
    from h1 have h1b: "is_wf_g (withRsG F1)"
      by (simp add: is_wf_withRsG)
    from h2 have h2a: "is_wf_g (sg F2)" 
      by (simp add: is_wf_fr_def is_wf_sg_def)
    from h2 have h2b: "is_wf_g (withRsG F2)"
      by (simp add: is_wf_withRsG)
    show ?thesis
    proof (simp add: disjGs_def, rule conjI)
      show "(Ns (sg F1) \<union> ran (tr F1)) \<inter> (Ns (sg F2) \<union> ran (tr F2)) = {}"
        by (simp add: rst_Ns_disj)
  qed

lemma disjGs_refsG:
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
  shows "disjGs (refsG F1) (refsG F2)"
  proof -
    from h1 have h1a: "is_wf_g (sg F1)" 
      by (simp add: is_wf_fr_def is_wf_sg_def)
    from h1 have h1b: "is_wf_g (withRsG F1)"
      by (simp add: is_wf_withRsG)
    from h2 have h2a: "is_wf_g (sg F2)" 
      by (simp add: is_wf_fr_def is_wf_sg_def)
    from h2 have h2b: "is_wf_g (withRsG F2)"
      by (simp add: is_wf_withRsG)
    from h3 have h3b: "Es (sg F1) \<inter> Es (sg F2) = {}"
      by (simp add: disjGs_def)
    from h3 have h3c: "disjGs (withRsG F1) (withRsG F2)"
      by (simp add: disjGs_def withRsG_def)
    show ?thesis
    proof (simp add: disjGs_def, rule conjI)
      show "rst_Ns (withRsG F1) (EsRP (sg F1)) \<inter> rst_Ns (withRsG F2) (EsRP (sg F2)) = {}"
        using h3 h1b h2b by (simp add: rst_Ns_disj)
    qed
  qed*)


(*
lemma repsOf_fr_Un_dist:
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
    and h4: "Range (refs F1) \<inter> Ns (sg F2) = {}"
  shows "repsOf v (F1 UF F2) \<subseteq> repsOf v F1 \<union> repsOf v F2"
  proof -
    from h1 have h1a: "is_wf_sg (sg F1)"
      by (simp add: is_wf_fr_def)
    from h2 have h2a: "is_wf_sg (sg F2)"
      by (simp add: is_wf_fr_def)
    from h3 have h3a: "Ns (sg F1) \<inter> Ns (sg F2) = {}"
      by (simp add: disjGs_def)
(*    have h5: "Domain (reps F1) \<inter> Domain (reps F2) = {}"
    proof
      show "Domain (reps F1) \<inter> Domain (reps F2) \<subseteq> {}"       
        using h4 h1 h2 h3a h1a h2a Range_refs[of F2] Range_refs[of F1]
        by (auto simp add: reps_def Domain_Un_eq Domain_refs intro: in_NsP_Ns)*)
    show ?thesis
      using h1 h2 h3 
      by (simp add: repsOf_def reps_fr_Un_dist Un_Image)   
  qed*)

(*lemma in_repsOf_UnF_dist:
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
    and h4: "Range (refs F1) \<inter> Ns (sg F2) = {}" 
  shows "y \<in> repsOf x (F1 UF F2) = (y \<in> repsOf x F1 \<or> y \<in> repsOf x F2)"
  proof-
    show ?thesis
    proof (simp add: repsOf_def)
      assume "y \<in> repsOf x (F1 UF F2)"
      then show " y \<in> repsOf x F1 \<or> y \<in> repsOf x F1"
  qed

lemma repsOf_rel_UnF_dist:
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
    and h4: "Range (refs F1) \<inter> Ns (sg F2) = {}"
  shows "repsOf_rel (F1 UF F2) = repsOf_rel (F1) \<union> repsOf_rel (F2)"
  proof -
    from h1 have h1a: "is_wf_sg (sg F1)"
      by (simp add: is_wf_fr_def)
    from h2 have h2a: "is_wf_sg (sg F2)"
      by (simp add: is_wf_fr_def)
    show ?thesis
    proof
      show "repsOf_rel (F1 UF F2) \<subseteq> repsOf_rel F1 \<union> repsOf_rel F2"
      proof (rule subrelI)
        fix x y
        assume "(x, y) \<in> repsOf_rel (F1 UF F2)"
        then show "(x, y) \<in> repsOf_rel F1 \<union> repsOf_rel F2"        
          using h1 h2 h3 h4 h1a h2a 
          by (auto simp add: repsOf_rel_def NsP_disj_dist)
      qed
    next
      show "repsOf_rel F1 \<union> repsOf_rel F2 \<subseteq> repsOf_rel (F1 UF F2)"
      proof (rule subrelI)
        fix x y
        assume "(x, y) \<in> repsOf_rel F1 \<union> repsOf_rel F2"
        hence "(x, y) \<in> repsOf_rel F1 \<or> (x, y) \<in> repsOf_rel F2" by simp
        then show "(x, y) \<in> repsOf_rel (F1 UF F2)"
        proof
          assume "(x, y) \<in> repsOf_rel F1"
          then show "(x, y) \<in> repsOf_rel (F1 UF F2)"
          using h1 h2 h3 h4 h1a h2a 
          by (auto simp add: repsOf_rel_def repsOf_fr_Un_dist NsP_disj_dist) 
    proof
      show "repsOf_rel (F1 UF F2) \<subseteq> repsOf_rel F1 \<union> repsOf_rel F2"
        using h1 h2 h3 h1a h2a by (simp add: repsOf_rel_def )
  qed*)

(*lemma inhF_fr_Un_dist:
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
    and h4: "Range (refs F1) \<inter> Ns (sg F2) = {}"
  shows "inhF (F1 UF F2) = inhF (F1) \<union>  inhF (F2)"
  proof -
    from h1 have h1a: "is_wf_sg (sg F1)"
      by (simp add: is_wf_fr_def)
    from h2 have h2a: "is_wf_sg (sg F2)"
      by (simp add: is_wf_fr_def)
    from h3 have h3a: "Ns (sg F1) \<inter> Ns (sg F2) = {}" 
      by (simp add:disjGs_def) 
   (* have "inh (sg F1) O repsOf_rel (F1 UF F2) = inh (sg F1) O repsOf_rel F1"
    proof
      show "inh (sg F1) O repsOf_rel (F1 UF F2) \<subseteq> inh (sg F1) O repsOf_rel F1"
      proof (rule subrelI)
        fix x y
        assume "(x, y) \<in> inh (sg F1) O repsOf_rel (F1 UF F2)"
        hence "\<exists> z. (x, z) \<in> inh (sg F1) \<and> (z, y) \<in> repsOf_rel (F1 UF F2)"
          by (simp add: relcomp_unfold)
        then show "(x, y) \<in> inh (sg F1) O repsOf_rel F1"
        proof
          apply_end(erule conjE)
          fix z
          assume h5a: "(x, z) \<in> inh (sg F1)"
          assume h5b: "(z, y) \<in> repsOf_rel (F1 UF F2)"
          show "(x, y) \<in> inh (sg F1) O repsOf_rel F1"
          proof (case_tac "z = y")
            assume "z = y"
            then show "(x, y) \<in> inh (sg F1) O repsOf_rel F1" 
              using h5a h5b by (auto simp: relcomp_unfold repsOf_rel_def repsOf_def)
          next
            assume h6a: "z \<noteq> y"
            from h5b have h6b: "z \<in> Domain (reps F1 \<union> reps F2)"
            proof (simp add: repsOf_rel_def repsOf_def)
              assume "(z, y) \<in> (reps (F1 UF F2))\<^sup>*"
              hence "(z, y) \<in> (reps F1 \<union> reps F2)\<^sup>*"
                using h1 h2 h3 by (simp add: reps_UnF_dist)
              then show "z \<in> Domain (reps F1 \<union> reps F2)" 
                using h6a by (auto simp add: rtrancl_eq_or_trancl Domain_unfold)
                  (blast dest: tranclD)
            qed
            from h5a have h6c: "z \<in> Ns (sg F1)"
              using h1a Range_inh[of "sg F1"] by auto
            from h6b show "(x, y) \<in> inh (sg F1) O repsOf_rel F1"
            proof (simp add: Domain_Un_eq)
              apply_end(rule disjE)
              assume h7a: "z \<in> Domain (reps F1)"
              show "(x, y) \<in> inh (sg F1) O repsOf_rel F1"
              proof (case_tac "z \<notin> Domain (reps F2)")
                assume h7b: "z \<notin> Domain (reps F1)"
                hence "(z, y) \<in> (reps F1)"
                  using h7a h7b by (simp add: repsOf_rel_def)
                show "(x, y) \<in> inh (sg F1) O repsOf_rel F1"
                  by (simp add: repsOf_rel_def relcomp_unfold)
            proof (simp add: Domain_Un_eq)
              apply_end(erule disjE)
              assume "z \<in> Domain (reps F1)"
              then show "z \<in> Domain (reps F1)" by auto
            next
              assume "z \<in> Domain (reps F2)"
              then show "z \<in> Domain (reps F1)"
              using h5a h6c h2 h3a h2a h1 Range_refs[of F2] Range_refs[of F1]
                by (auto simp add: reps_def Domain_Un_eq Domain_refs intro!: in_NsP_Ns)
              using h1 h1a h2 h2a h5a Range_inh[of "sg F1"] h4 h6b h3a Range_refs[of F2]
                by (auto simp add: reps_def Domain_Un_eq Domain_refs intro: in_NsP_Ns)
            show "(x, y) \<in> inh (sg F1) O repsOf_rel F1"

            
          hence h5a: "z \<in> Ns (sg F1)"
            using h1a Range_inh[of "sg F1"] by (auto)
          hence h5c: "z \<in> Domain (reps F1)" 
            using h1 h1a Range_refs[of F1] h4
            by (auto simp add: reps_def Domain_refs Domain_Un_eq)
          hence h5c: "z \<in> Domain (reps F1)" 
            using h5a h1 h2 h3 by (simp add: repsOf_rel_def repsOf_def reps_UnF_dist)
          hence "(z, y) \<in> repsOf_rel F1"
            using h5a h4 h1 h2 h3 by (simp add: repsOf_rel_def repsOf_def reps_UnF_dist)
          from h5 h6 show "(x, y) \<in> inh (sg F1) O repsOf_rel F1"
            by (simp add: relcomp_unfold)
      qed
    qed*)
    show ?thesis
    proof
      show "inhF (F1 UF F2) \<subseteq> inhF F1 \<union> inhF F2"
      proof (rule subrelI)
        fix x y
        assume "(x, y) \<in> inhF (F1 UF F2)"
        then show "(x, y) \<in> inhF F1 \<union> inhF F2"
          using h1 h2 h1a h2a h3 
          by (simp add: inhF_def inhsg_Un_dist)
      qed
    next
      show "inhF F1 \<union> inhF F2 \<subseteq> inhF (F1 UF F2)"
      proof (rule subrelI)
        fix x y
        assume "(x, y) \<in> inhF F1 \<union> inhF F2"
        then show "(x, y) \<in> inhF (F1 UF F2)"
          using h1 h2 h1a h2a h3 
          by (auto simp add: inhF_def inhsg_Un_dist refs_UF)
      qed
    qed
 qed*)

lemma Dom_inh_Un_refs_disjoint:
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
  shows "(Domain (inh (sg F1)) \<union> Domain (refs F1)) 
  \<inter> (Domain (inh (sg F2)) \<union> Domain (refs F2)) = {}"
  proof -
    from h1 have h1b: "dom (tgt (sg F1)) = Es (sg F1)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1c: "ran (src (sg F1)) \<subseteq> Ns (sg F1)"
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1e: "dom (tgtr F1) = Es (sg F1)"
      using h1b EsRP_sub_Es[where SG = "sg F1"] 
      by (auto simp add: is_wf_fr_def tgtr_def ftotal_on_def)
    from h2 have h2b: "dom (tgt (sg F2)) = Es (sg F2)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2c: "ran (src (sg F2)) \<subseteq> Ns (sg F2)"
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2e: "dom (tgtr F2) = Es (sg F2)"
      using h2b EsRP_sub_Es[where SG = "sg F2"] 
      by (auto simp add: is_wf_fr_def tgtr_def ftotal_on_def)
    from h3 have h3a: "Ns (sg F1) \<inter> Ns (sg F2) = {}"
      by (simp add: disjGs_def)
    show ?thesis
    proof
      show "(Domain (inh (sg F1)) \<union> Domain (refs F1)) \<inter> (Domain (inh (sg F2)) \<union> Domain (refs F2)) \<subseteq> {}"
      proof 
        fix x
        assume "x \<in> (Domain (inh (sg F1)) \<union> Domain (refs F1)) \<inter>
             (Domain (inh (sg F2)) \<union> Domain (refs F2))"
        then show "x \<in> {}"
          using h1c h1e h2c h2e h3a
          by (auto simp add: refs_def inh_def relOfGr_def refsG_def withRsG_def adjacent_def 
            EsRP_def rst_fun_def NsP_def NsTy_def EsR_def restrict_map_def EsI_def EsId_def 
            EsTy_def split: if_splits intro!: ranI)
      qed
    next
      show "{} \<subseteq> (Domain (inh (sg F1)) \<union> Domain (refs F1)) \<inter> (Domain (inh (sg F2)) \<union> Domain (refs F2))"
        by auto
    qed
  qed

lemma Range_inh_Un_refs_not_in_fields:
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
     and h4: "Range (refs F1) \<inter> Ns (sg F2) = {}" 
  shows "Range (inh (sg F1) \<union> refs F1) \<inter> (Domain (inh (sg F2) \<union> refs F2)) = {}"
  proof -
    from h1 have h1a: "is_wf_sg (sg F1)" 
      by (simp add: is_wf_fr_def)
    from h1 have h1b: "dom (tgt (sg F1)) = Es (sg F1)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1c: "ran (src (sg F1)) \<subseteq> Ns (sg F1)"
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1d: "ran (tgt (sg F1)) \<subseteq> Ns (sg F1)"
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2a: "is_wf_sg (sg F2)" 
      by (simp add: is_wf_fr_def)
    from h2 have h2b: "dom (tgt (sg F2)) = Es (sg F2)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2c: "ran (src (sg F2)) \<subseteq> Ns (sg F2)"
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2d: "ran (tgt (sg F2)) \<subseteq> Ns (sg F2)"
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h3 have h3a: "Ns (sg F1) \<inter> Ns (sg F2) = {}"
      by (simp add: disjGs_def)
    show ?thesis
    proof
      show "Range (inh (sg F1) \<union> refs F1) \<inter> Domain (inh (sg F2) \<union> refs F2) \<subseteq> {}"
      proof
        fix x
        assume "x \<in> Range (inh (sg F1) \<union> refs F1) \<inter> Domain (inh (sg F2) \<union> refs F2)"
        then show "x \<in> {}"
        proof
          assume h5: "x \<in> Range (inh (sg F1) \<union> refs F1)"
          from h5 h1 h1d h1a have h5a: "x \<in> Ns (sg F1) \<union> Range(refs F1)"
            using Range_refs[of F1] Range_inh[where SG="sg F1"]
            by (simp add: Range_Un_eq)(erule disjE, rule disjI1, auto)
          assume h6: "x \<in> Domain (inh (sg F2) \<union> refs F2)"
          from h6 h2a h2 have h6a: "x \<in> Ns (sg F2)" 
            using Domain_refs[of F2] Domain_inh[where SG="sg F2"] 
            NsP_sub_Ns[where SG="sg F2"] Range_inh[where SG="sg F2"]
            by (auto simp add: Domain_Un_eq)
          from h5a h6a have h7: "x \<in> (Ns (sg F1) \<union> Range(refs F1)) \<inter> Ns (sg F2)"
            by auto
          from h7 h3a h4 h1a show "x \<in> {}"
            using Range_inh[where SG="sg F1"]  
            by (simp add: Range_Un_eq)(auto)
        qed
      qed
    next
      show "{} \<subseteq> Range (inh (sg F1) \<union> refs F1) \<inter> Domain (inh (sg F2) \<union> refs F2)"
        by auto
    qed
qed

(*lemma disj_Fr_Refs_disj_Fields:
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
    and h4: "Field (refs F1) \<inter> Field (refs F2) = {}"
  shows "Field (inh (sg F1) \<union> refs F1) \<inter> Field (inh (sg F2)\<union> refs F2) = {}"
  proof -
    from h1 have h1b: "dom (src (sg F1)) = Es (sg F1)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1c: "dom (tgt (sg F1)) = Es (sg F1)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1d: "ran (src (sg F1)) \<subseteq> Ns (sg F1)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1e: "ran (tgt (sg F1)) \<subseteq> Ns (sg F1)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1f: "is_wf_sg (sg F1)" 
      by (simp add: is_wf_fr_def)
    from h1f have h1g: "Es (sg F1) \<subseteq> E_A" 
      by (simp add: is_wf_sg_def is_wf_g_def)
    from h2 have h2b: "dom (src (sg F2)) = Es (sg F2)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2c: "dom (tgt (sg F2)) = Es (sg F2)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2d: "ran (src (sg F2)) \<subseteq> Ns (sg F2)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2e: "ran (tgt (sg F2)) \<subseteq> Ns (sg F2)" 
      by (simp add: is_wf_fr_def is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2f: "ran (tr F2) \<subseteq> V_A" 
      by (simp add: is_wf_fr_def ftotal_on_def)
    from h3 have h3a: "Ns(sg F1) \<inter> Ns(sg F2) = {}" 
      by (simp add: disjGs_def)
    from h3 have h3b: "Ns(sg F2) \<inter> Es(sg F1) = {}" 
      by (simp add: disjGs_def)
    show ?thesis
    proof
      show "Field (inh (sg F1) \<union> refs F1) \<inter> Field (inh (sg F2)\<union> refs F2) \<subseteq> {}"
      proof
        fix x 
        assume h5: "x \<in> Field (inh (sg F1) \<union> refs F1) \<inter> Field (inh (sg F2) \<union> refs F2)"
        from h5 have h5a1: "x \<in> Field (inh (sg F1) \<union> refs F1)"
          by (simp)
        from h5a1 have h5a2: "x \<in> Ns (sg F1)  \<union> Field (refs F1)"
        proof (simp)
          apply_end(erule disjE, rule disjI1)
          assume "x \<in> Field (inh (sg F1))"
          then show "x \<in> Ns (sg F1)"
            using h1d h1e by (auto simp add: inh_def relOfGr_def restrict_def adjacent_def rst_fun_def 
              EsI_def EsTy_def EsId_def vimage_def restrict_map_def Field_def 
              split: if_splits intro!: ranI)
        next
          apply_end(rule disjI2, simp)
        qed
        from h5 have h5b1: "x \<in> Field (inh (sg F2) \<union> refs F2)"
          by (simp)
        from h5b1 have h5b2: "x \<in> Ns (sg F2)  \<union> Field (refs F2)"
        proof (simp)
          apply_end(erule disjE, rule disjI1)
          assume "x \<in> Field (inh (sg F2))"
          then show "x \<in> Ns (sg F2)"
            using h2d h2e by (auto simp add: inh_def relOfGr_def restrict_def adjacent_def rst_fun_def 
              EsI_def EsTy_def EsId_def vimage_def restrict_map_def Field_def 
              split: if_splits intro!: ranI )
        next
          apply_end(rule disjI2, simp)
        qed
        from h4 h5a2 h5b2 h3a h1g show "x \<in> {}"
          by auto
          using disj_V_E
          by (auto simp add: disjGs_def rst_Ns_def Field_def split: if_splits)
      qed
    next
      show "{} \<subseteq> Field (inh (sg F1) \<union> refs F1) \<inter> Field (inh (sg F2) \<union> refs F2)"
        by (simp)
    qed
qed*)


(*Below, h4 captures a constraint coming from above (top level) that has to due with imports*)
lemma acyclic_fr_Un:
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
    and h4: "Range (refs F1) \<inter> Ns (sg F2) = {}"
  shows "acyclic_fr (F1 UF F2)"
  proof -
    from h1 have h1a: "is_wf_sg (sg F1)"
      by (simp add: is_wf_fr_def)
    from h1 have h1b: "acyclic_fr F1"
      by (simp add: is_wf_fr_def)
    from h1b have h1c: "acyclic (inh (sg F1) \<union> refs F1)"
      by (simp add: acyclic_fr_def)
    from h2 have h2a: "is_wf_sg (sg F2)"
      by (simp add: is_wf_fr_def)
    from h2 have h2b: "acyclic_fr F2"
      by (simp add: is_wf_fr_def)
    from h2b have h2c: "acyclic (inh (sg F2) \<union> refs F2)"
      by (simp add: acyclic_fr_def)
    from h3 have h3a: "disjGs (sg F2) (sg F1)" by (simp add: disjGs_sym)
    have h5: "inh (sg F1) \<union> inh (sg F2) \<union> (refs F1 \<union> refs F2) 
         = (inh (sg F1) \<union> refs F1) \<union> (inh (sg F2)\<union> refs F2)"
         by (auto)
    show ?thesis
    proof (simp add: acyclic_fr_def)
      have h7:"Domain (inh (sg F2) \<union> refs F2) \<inter> Domain (inh (sg F1) \<union> refs F1) = {}"
        using h1 h2 h3a by (simp add: Domain_Un_eq Dom_inh_Un_refs_disjoint)
      have h8: "Range (inh (sg F1) \<union> refs F1) \<inter> Domain (inh (sg F2) \<union> refs F2) = {}"
        using h1 h2 h3 h4 
        Range_inh_Un_refs_not_in_fields[of F1 F2]
        by (simp)
      have h9: "inh (sg F2) \<union> refs F2 \<union> (inh (sg F1) \<union> refs F1)
        = inh (sg F1) \<union> refs F1 \<union> (inh (sg F2) \<union> refs F2)" by auto
      have h10: "acyclic ((inh (sg F1) \<union> refs F1)\<union>(inh (sg F2) \<union> refs F2))"
        using  h1c h2c h7 h8 h9
          acyclic_Un[where s="inh (sg F1) \<union> refs F1" and r="inh (sg F2) \<union> refs F2"]
        by simp
      from h4 h7 show "acyclic (inh (sg F1 USG sg F2) \<union> refs (F1 UF F2))"
        using h1a h2a h3 h1 h2 
        by (simp add: acyclic_Un inhsg_Un_dist refs_UF h5 h10)
    qed
  qed

lemma UF_proxies_have_NonP_ref: 
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
    and h4: "Range (refs F1) \<inter> Ns (sg F2) = {}" and h5: "v \<in> NsP (sg F1 USG sg F2)"
  shows "nonPRefsOf (F1 UF F2) v \<noteq> {}"
  proof -
    from h1 have h1a: "is_wf_sg (sg F1)" by (simp add: is_wf_fr_def)
    from h2 have h2a: "is_wf_sg (sg F2)" by (simp add: is_wf_fr_def)
    from h1 have h6a: "\<forall>v. v \<in> NsP (sg F1) \<longrightarrow> nonPRefsOf F1 v \<noteq> {}"
      by (simp add: is_wf_fr_def)
    from h2 have h6b: "\<forall>v. v \<in> NsP (sg F2) \<longrightarrow> nonPRefsOf F2 v \<noteq> {}"
      by (simp add: is_wf_fr_def)
    from h5 have h5c: "v \<in> NsP (sg F1) \<or> v \<in> NsP (sg F2)"
      using h1a h2a h3 by (simp add: NsP_disj_dist)
    from h5c show ?thesis
    proof
      assume "v \<in> NsP (sg F1)"
      then show "nonPRefsOf (F1 UF F2) v \<noteq> {}"
        using h1 h2 h3 h4 by (simp add: in_nonPRefsOf_CUPF_1 is_wf_fr_def)
    next
      assume ha: "v \<in> NsP (sg F2)"
      hence hb: "nonPRefsOf F2 v \<noteq> {}" using h6b by (auto)
      from ha hb show "nonPRefsOf (F1 UF F2) v \<noteq> {}"
      proof (simp add: nonPRefsOf_def)
        apply_end(erule exE)
        fix x
        assume hc: "x \<in> refsOf F2 v \<and> x \<notin> NsP (sg F2)"
        then show "\<exists>x. x \<in> refsOf (F1 UF F2) v \<and> x \<notin> NsP (sg F1 USG sg F2)"
        proof (case_tac "x \<notin> NsP (sg F1)")
          assume hd: "x \<notin> NsP (sg F1)"
          from hc hd show "\<exists>x. x \<in> refsOf (F1 UF F2) v \<and> x \<notin> NsP (sg F1 USG sg F2)"
            using h1a h2a h1 h2 h3 h4 ha
              by (simp add: nonPRefsOf_def NsP_disj_dist in_RefsOf_CUPF_2)
                (rule exI[where x="x"], simp)
        next
          apply_end(simp)
          assume hd: "x \<in> NsP (sg F1)"
          hence "nonPRefsOf F1 x \<noteq> {}" using h6a by (auto)
          hence "\<exists> z. z \<in> refsOf F1 x \<and> z \<notin> NsP (sg F1)" by (simp add: nonPRefsOf_def)
          then show "\<exists>x. x \<in> refsOf (F1 UF F2) v \<and> x \<notin> NsP (sg F1 USG sg F2)"
          proof
            apply_end(clarsimp)
            fix z
            assume he: "z \<in> refsOf F1 x"
            hence "(x, z) \<in> (refs F1)\<^sup>+" by (simp add: refsOf_def)
            hence "z \<in> Range ((refs F1)\<^sup>+)" by (blast)
            hence "z \<in> Range (refs F1)" by (simp)
            hence hf: "z \<notin> NsP (sg F2)" using h4 h2a by (auto intro: in_NsP_Ns)
            assume hg: "z \<notin> NsP (sg F1)"
            from hc have "(v, x) \<in> (refs F2)\<^sup>+" by (simp add: refsOf_def)
            hence "x \<in> Range ((refs F2)\<^sup>+)" by (blast)
            hence hh: "x \<in> Range (refs F2)" by (simp)
            show "\<exists>x. x \<in> refsOf (F1 UF F2) v \<and> x \<notin> NsP (sg F1 USG sg F2)"
            using h1 h2 h3 h4 hd ha h1a h2a hf hc he hg hh
            by (simp add: in_RefsOf_CUPF_2)
              (simp add: refsOf_def NsP_disj_dist relcomp_unfold, 
                rule_tac exI[where x="z"], simp, rule disjI2, rule_tac exI[where x="x"], 
                auto simp add: dres_def)
          qed
        qed
      qed
   qed
  qed

lemma is_wf_fr_Un: 
  assumes h1: "is_wf_fr F1" and h2: "is_wf_fr F2" and h3: "disjGs (sg F1) (sg F2)"
    and h4: "Range (refs F1) \<inter> Ns (sg F2) = {}" 
    and h5: "ran (tr (F1 UF F2)) \<inter> NsP (sg (F1 UF F2)) = {}"
  shows "is_wf_fr (F1 UF F2)"
  proof -
    from h1 have h1a: "is_wf_sg (sg F1)" by (simp add: is_wf_fr_def)
    from h1 have h1b: "dom (tr F1) = EsRP (sg F1)" 
      by (simp add: is_wf_fr_def ftotal_on_def)
    from h1 have h1c: "proxies_dont_inherit F1" 
      by (simp add: is_wf_fr_def)
    from h1a have h1d: "dom (src (sg F1)) = Es (sg F1)" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1e: "ran (tr F1) \<subseteq> V_A"
      by (simp add: is_wf_fr_def ftotal_on_def)
    from h1a have h1f: "ran (src (sg F1)) \<subseteq> Ns (sg F1)"
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1g: "dom (tr F1) = EsRP (sg F1)"
      by (simp add: is_wf_fr_def ftotal_on_def)
    from h2 have h2a: "is_wf_sg (sg F2)" by (simp add: is_wf_fr_def)
    from h2 have h2b: "dom (tr F2) = EsRP (sg F2)" 
      by (simp add: is_wf_fr_def ftotal_on_def)
    from h2 have h2c: "proxies_dont_inherit F2" by (simp add: is_wf_fr_def)
    from h2a have h2d: "dom (src (sg F2)) = Es (sg F2)" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2e: "ran (tr F2) \<subseteq> V_A"
      by (simp add: is_wf_fr_def ftotal_on_def)
    from h2a have h2f: "ran (src (sg F2)) \<subseteq> Ns (sg F2)"
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2g: "dom (tr F2) = EsRP (sg F2)"
      by (simp add: is_wf_fr_def ftotal_on_def)
    from h3 have h3a: "Es (sg F1) \<inter> Es (sg F2) = {}" by (simp add: disjGs_def disjEsGs_def)
    from h3 have h3b: "Ns (sg F1) \<inter> Ns (sg F2) = {}" by (simp add: disjGs_def)
    from h3a have h3c: "dom (src (sg F1)) \<inter> dom (src (sg F2)) = {}"
        using h1d h2d by (auto)
    show "is_wf_fr (F1 UF F2)" 
    proof (simp add: is_wf_fr_def, rule conjI)
      from h1a h2a h3 show "is_wf_sg (sg F1 USG sg F2)"
        by (simp add: cupF_def is_wf_sg_Un)
    next
      apply_end (rule conjI)
      from h1a h2a h1b h2b h3 h1e h2e 
        show "ftotal_on (tr F1 ++ tr F2) (EsRP (sg F1 USG sg F2)) V_A"
        using ran_map_add_sub[where f="tr F1" and g="tr F2"]
        by (auto simp add: ftotal_on_def EsRP_disj_dist)
    next
      apply_end (rule conjI)
      have hb: "ran (src (sg F1)) \<inter> ran (src (sg F2)) = {}"
        using h3b h1f h2f by (auto)
      have hc: "EsRP (sg F1) \<subseteq> dom (src (sg F1))"
        using h1a h1d by (auto intro: in_EsRP_in_Es)
      have hd: "EsRP (sg F2) \<subseteq> dom (src (sg F2))"
        using h2a h2d by (auto intro: in_EsRP_in_Es)
      show "inj_on (src (sg F1) ++ src (sg F2)) (EsRP (sg F1 USG sg F2))"
        using h1a h2a h3 h3c hb hc hd h1 h2
        by (simp add: EsRP_disj_dist inj_on_map_dist_on_disj_doms is_wf_fr_def)
    next
      apply_end (rule conjI)
      from h3c have ha: "dom (src (sg F1) |` (EsRP (sg F1) \<union> EsRP (sg F2))) 
        \<inter> dom (src (sg F2) |` (EsRP (sg F1) \<union> EsRP (sg F2))) = {}"
        by auto
      have hb: "src (sg F1) |` (EsRP (sg F1) \<union> EsRP (sg F2)) = src (sg F1) |` (EsRP (sg F1))"
        using h1d h2d h3a h2a
        by (auto simp add: restrict_map_def fun_eq_iff intro: in_EsRP_in_Es domI 
          split: if_splits)
      have hc: "src (sg F2) |` (EsRP (sg F1) \<union> EsRP (sg F2)) = src (sg F2) |` (EsRP (sg F2))"
        using h1d h2d h3a h1a
        by (auto simp add: restrict_map_def fun_eq_iff intro: in_EsRP_in_Es domI 
          split: if_splits)
      show "ran ((src (sg F1) ++ src (sg F2)) |` EsRP (sg F1 USG sg F2)) = NsP (sg F1 USG sg F2)"
        using h1a h2a h3 ha hb hc h1 h2
        by (simp add: EsRP_disj_dist map_add_restrict_dist NsP_disj_dist is_wf_fr_def)
    next
      apply_end (rule conjI)
      show "\<forall>v. v \<in> NsP (sg F1 USG sg F2) \<longrightarrow> nonPRefsOf (F1 UF F2) v \<noteq> {}"
        using h1 h2 h3 h4 by (simp add: UF_proxies_have_NonP_ref)
    next
      apply_end (rule conjI)
      show "acyclic_fr (F1 UF F2)"
        using h1 h2 h3 h4 by (simp add: acyclic_fr_Un) 
    next
      from h1 h2 h3 show "proxies_dont_inherit (F1 UF F2)" 
        by (simp add: dist_cup_proxies_dont_inherit)
    qed
  qed

(*Extension of inhst to take references into account*)
definition inhstF:: "Fr \<Rightarrow> (V\<times>V) set"
where
  "inhstF F = (inhF F)\<^sup>*"

lemma inhstF_rtrancl_unfold: "inhstF F = Id \<union> (inhF F)\<^sup>* O inhF F"
  using rtrancl_unfold[where r="(inhF F)"]
  by (auto simp: inhstF_def) 

lemma inhstF_rtrancl_unfold_idemp: "inhstF F = (inhF F)\<^sup>* O (inhF F)\<^sup>*"
  by (simp add: inhstF_def)

lemma inh_inhstF_reflex[simp]: "(a, a) \<in> inhstF F"
  by (simp add: inhstF_def)

lemma inhstsg_sub_inhstF: "inhst (sg F) \<subseteq> inhstF F"
  proof (rule subrelI)
    fix x y
    assume "(x, y) \<in> inhst (sg F)"
    then show "(x, y) \<in> inhstF F"
      using rtrancl_cpm_of_Un_in_Un[where r="inh (sg F)" and s = "inh (sg F) \<union> reps F"] 
      by (auto simp add: inhF_def inhstF_def inhst_def)
  qed

lemma repsst_sub_inhstF: "(refs F)^* \<subseteq> inhstF F"
  proof - 
    have h1: "refs F \<union> (inh (sg F) \<union> (refs F)\<inverse>) = inh (sg F) \<union> (refs F \<union> (refs F)\<inverse>)"
      by auto
    show ?thesis
      using rtrancl_cpm_of_Un_in_Un[where r="refs F" and s = "inh(sg F) \<union> (refs F)\<inverse>"] 
      by (auto simp add: inhstF_def inhF_def rtrancl_Un_sym reps_def h1)
  qed

lemma inh_in_inhstF: "(a, b) \<in> inh (sg F) \<Longrightarrow> (a, b) \<in> inhstF F"
   apply (simp add: inhstF_rtrancl_unfold relcomp_unfold)
   apply (rule disjI2)
   by (rule_tac exI[where x = "a"], simp add: inhF_def)

lemma inhst_in_inhstF: "(a, b) \<in> inhst (sg F) \<Longrightarrow> (a, b) \<in> inhstF F"
  proof -
    have h1: "(inh (sg F))\<^sup>* \<subseteq> (inh (sg F) \<union> reps F)\<^sup>*"
    using rtrancl_Un_subset[where R="inh (sg F)" and S="reps F"]
    by (simp)
    show "(a, b) \<in> inhst (sg F) \<Longrightarrow> (a, b) \<in> inhstF F"
      using h1
      by (auto simp add: inhst_def inhstF_def inhF_def)
 qed
  
lemma inhF_in_inhstF: "(a, b) \<in> inhF F \<Longrightarrow> (a, b) \<in> inhstF F"
  by (simp add: inhstF_rtrancl_unfold relcomp_unfold, rule disjI2, 
    rule_tac exI[where x = "a"], auto)

lemma refs_in_inhstF: "(a, a') \<in> refs F \<Longrightarrow> (a, a') \<in> inhstF F"
  apply (simp add: inhstF_rtrancl_unfold relcomp_unfold)
  apply (rule disjI2)
  apply (rule_tac exI[where x = "a"])
  by (simp add: inhF_def reps_def)

lemma refsst_in_inhstF: "(a, b) \<in> (refs F)\<^sup>* \<Longrightarrow> (a, b) \<in> inhstF F"
  proof (induct rule:rtrancl.induct, simp add: inhstF_def)
    fix a b c
    assume h1: "(a, b) \<in> inhstF F "
    then have h2 : "(a, b) \<in> (inhF F)\<^sup>*"
      by (simp add: inhstF_def)
    assume h3: "(b, c) \<in> refs F"
    then have h4: "(b, c) \<in> inhF F"
      by (simp add: inhF_def reps_def)
    show "(a, c) \<in> inhstF F"
       proof (simp add: inhstF_rtrancl_unfold relcomp_unfold, rule disjI2,
         rule_tac exI[where x = "b"])
       show "(a, b) \<in> (inhF F)\<^sup>* \<and> (b, c) \<in> inhF F"
       using h2 h4 by simp
      qed
  qed
  
lemma inhstF_trans_reps1: "(a, b) \<in> inhst (sg F)  \<Longrightarrow> (b, b') \<in> refs F \<Longrightarrow> (a, b') \<in> inhstF F"
  apply (simp add: inhstF_rtrancl_unfold relcomp_unfold)
  apply (rule disjI2)
  apply (rule_tac x = "b" in exI, simp add: inhF_def)
  apply (insert inhstF_def[where F = "F"], erule ssubst, 
    insert inhst_in_inhstF[where F ="F" and a="a" and b="b"])
  by (simp add: inhstF_def inhF_def reps_def)

(*lemma inhstF_trans_reps2:"(a, b) \<in> inh (sg F)  \<Longrightarrow> (a, a') \<in> refs F \<Longrightarrow> (a', b) \<in> inhstF F"
  apply (simp add: inhstF_rtrancl_unfold relcomp_unfold)
  apply (rule disjI2)
  apply (rule_tac x = "a" in exI)
  apply (insert inhstF_def[where F="F"], erule subst)
  using inhsg_sub_inhF[where F="F"] by (auto simp add: refs_in_inhstF)*)

lemma inhstF_trans_reps3:"(a, b) \<in> inh (sg F)  \<Longrightarrow> (a', a) \<in> (refs F)\<^sup>* \<Longrightarrow> (a', b) \<in> inhstF F"
  proof -
    assume h1: "(a, b) \<in> inh (sg F)"
    assume h2: "(a', a) \<in> (refs F)\<^sup>*"
    have h3: "(a', a) \<in> (inhF F)\<^sup>*"
      using h2 inhstF_def[where F = "F", THEN sym] 
      by (simp add: refsst_in_inhstF)
    show "(a', b) \<in> inhstF F"
    proof (simp add: inhstF_rtrancl_unfold relcomp_unfold, rule disjI2, 
       rule_tac exI[where x = "a"])
      show "(a', a) \<in> (inhF F)\<^sup>* \<and> (a, b) \<in> inhF F"
      using h1 h3 by (simp add: inhF_def)
    qed
  qed

lemma inhstF_trans_reps4: "(b, a) \<in> inhstF F  \<Longrightarrow> (c, b) \<in> inh (sg F) \<Longrightarrow> (c, a) \<in> inhstF F"
  proof -
    fix a b c 
    assume h1: "(b, a) \<in> inhstF F"
    assume h2: "(c, b) \<in> inh (sg F)" 
    have h3: "(c, b) \<in> inhstF F"
      using h2
      by (simp add: inh_in_inhstF)
    show "(c, a) \<in> inhstF F"
      using h1 h3
      by (simp add: inhstF_def)
  qed

lemma inhstF_trans_repsst1: "(b, c) \<in> (refs F)\<^sup>* \<Longrightarrow> (a, b) \<in> inh (sg F)  \<Longrightarrow>  (a, c) \<in> inhstF F"
  proof (induct rule:rtrancl.induct, simp add: inh_in_inhstF)
    fix aa a b c 
    assume h1: "(aa, b) \<in> (refs F)\<^sup>*"
    assume h2: "(a, aa) \<in> inh (sg F)"
    assume h3: "(b, c) \<in> (refs F)"
    assume h4: "(a, aa) \<in> inh (sg F) \<Longrightarrow>(a, b) \<in> inhstF F"
    then have h5: "(a, b) \<in> (inh (sg F) \<union> reps F)\<^sup>*"
      using h2 by (simp add: inhstF_def inhF_def)
    show "(a, c) \<in> inhstF F"
    proof (simp add: inhstF_rtrancl_unfold relcomp_unfold, rule disjI2, 
      rule_tac exI[where x = "b"], simp add: inhF_def)
      show "(a, b) \<in> (inh (sg F) \<union> reps F)\<^sup>* \<and> ((b, c) \<in> inh (sg F) \<or> (b, c) \<in> reps F)"
        using h5 h3 by (simp add: reps_def)
    qed
  qed 

(*lemma inhstF_trans_repsst2: "(b, ra) \<in> inh (sg F) \<Longrightarrow> (ra, a) \<in> (refs F)\<^sup>* \<Longrightarrow> (b, rb) \<in> refs F 
  \<Longrightarrow> (rb, a) \<in> inhstF F"
  proof -
    fix a ra b rb
    assume h1: "(b, ra) \<in> inh (sg F)"
    assume h2: "(ra, a) \<in> (refs F)\<^sup>*"
    assume h4: "(b, rb) \<in> refs F"
    have h5: "(rb, ra) \<in> (inhF F)\<^sup>*"
      using h1 h4 inhstF_trans_refs2 by (simp add: inhstF_def)
    have h6: "(ra, a) \<in> (inhF F)\<^sup>*"
      using h2 refsst_in_inhstF by (simp add: inhstF_def)
    show "(rb, a) \<in> inhstF F"
    by (insert inhstF_rtrancl_unfold_idemp[where F = "F"], erule ssubst, 
      simp add: relcomp_unfold, rule_tac exI[where x = "ra"], simp add: h5 h6)
  qed
 *)

lemma inhstF_def_simp: "((inhF F)\<^sup>*)\<inverse> = ((inhF F)\<inverse>)\<^sup>*"
proof -
  show "((inhF F)\<^sup>*)\<inverse> = ((inhF F)\<inverse>)\<^sup>*" by (simp add: rtrancl_converse)
qed

(*lemma inhstF: "(x, y) \<in> (inh (sg F))^* \<Longrightarrow> (x, y) \<in> inhstF F"
proof (simp add: inhstF_def)
  fix x y
  have h1: "(inhF F)\<^sup>* = Id \<union> (inhF F)\<^sup>* O (inhF F)"
    using rtrancl_unfold[where r= "(inhF F)"] by simp
  assume h2: "(x, y) \<in> (inh (sg F))\<^sup>*"
  then show "(x, y) \<in> (inhF F)\<^sup>*"
  using h1 by (simp add: inhF_def)
  qed*)

(*Clan of fragments, extends 'clan' to take 'refs' into account*)
definition clanF :: "V \<Rightarrow> Fr \<Rightarrow> V set"
where
  "clanF v F = (inhstF F)\<inverse>``{v}"

(*clan (repsOf vs F) (sg F)"*)

lemma clanF_reflex[simp]: "v \<in> clanF v F"
  by (simp add: clanF_def inhstF_def)

lemma clanF_of_inh: "(v1, v2) \<in> inh (sg F) \<Longrightarrow> v1 \<in> clanF v2 F"
  by (auto simp: clanF_def inhstF_def inhF_def)

lemma clansg_sub_clanF: "clan v (sg F) \<subseteq> clanF v F"
  by (auto simp add: clanF_def clan_def inhst_in_inhstF)

lemma clanF_of_clan: "v1 \<in> clan v2 (sg F) \<Longrightarrow> v1 \<in> clanF v2 F"
  using clansg_sub_clanF[where v="v2"] by (auto)

definition srcstF :: "Fr \<Rightarrow> (E\<times>V) set"
where
  "srcstF F = {(e, v). e \<in> EsA (sg F) \<and> (\<exists>v2. v \<in> clanF v2 F \<and> (e, v2) \<in> srcst (sg F))}"

lemma srcst_sub_srcstF: "srcst (sg F) \<subseteq> srcstF F"
  proof (rule subrelI)
    fix x y
    assume h1: "(x, y) \<in> srcst (sg F)"
    then show "(x, y) \<in> srcstF F"
    proof (simp add: srcstF_def)
      apply_end(rule conjI)
      from h1 show "x \<in> EsA (sg F)" by (simp add: srcst_def)
    next
      from h1 show "\<exists>v2. y \<in> clanF v2 F \<and> (x, v2) \<in> srcst (sg F)"
        by (rule_tac exI[where x="y"], simp)
    qed
  qed

lemma srcst_in_srcstF: "(e, v) \<in> srcst (sg F) \<Longrightarrow> (e, v) \<in> srcstF F"
  using srcst_sub_srcstF[where F="F"] by auto

lemma refsrc_in_srcstF: "\<lbrakk>(e, v1) \<in> srcst (sg F); v2 \<in> clanF v1 F\<rbrakk> \<Longrightarrow> (e, v2) \<in> srcstF F"
  proof -
    assume h1: "(e, v1) \<in> srcst (sg F)"
    assume h2: "v2 \<in> clanF v1 F"
    show "(e, v2) \<in> srcstF F"
    proof (simp add: srcstF_def)
      apply_end(rule conjI)
      from h1 h2 show "e \<in> EsA (sg F)" by (simp add: srcst_def)
    next
      from h1 h2 show "\<exists>v2a. v2 \<in> clanF v2a F \<and> (e, v2a) \<in> srcst (sg F)"
        by (rule_tac exI[where x="v1"], simp)
    qed
  qed

lemma the_src_clanF:
  assumes "(e, v1) \<in> srcst (sg F)" and "v2 \<in> clanF v1 F"
  shows "v2 \<in> clanF (the (src (sg F) e)) F"
  proof -
    have h1: "(inh (sg F))\<^sup>* \<subseteq> (inh (sg F) \<union> reps F)\<^sup>*"
      by (simp add: rtrancl_cpm_of_Un_in_Un)
    show ?thesis
    using assms h1 
    by (auto simp add: srcst_def clanF_def clan_def inhstF_def inhF_def inhst_def)
  qed

definition tgtstF :: "Fr \<Rightarrow> (E\<times>V) set"
where
  "tgtstF F = {(e, v). e \<in> EsA (sg F) \<and> (\<exists>v2. v \<in> clanF v2 F \<and> (e, v2) \<in>  tgtst (sg F))}"

lemma tgtst_sub_tgtstF: "tgtst (sg F) \<subseteq> tgtstF F"
  proof (rule subrelI)
    fix x y
    assume h1: "(x, y) \<in> tgtst (sg F)"
    then show "(x, y) \<in> tgtstF F"
    proof (simp add: tgtstF_def)
      apply_end(rule conjI)
      from h1 show "x \<in> EsA (sg F)" by (simp add: tgtst_def)
    next
      from h1 show "\<exists>v2. y \<in> clanF v2 F \<and> (x, v2) \<in> tgtst (sg F)"
        by (rule_tac exI[where x="y"], simp)
    qed
  qed

lemma tgtst_in_tgtstF: "(e, v) \<in> tgtst (sg F) \<Longrightarrow> (e, v) \<in> tgtstF F"
  using tgtst_sub_tgtstF[where F="F"] by auto

lemma reftgt_in_tgtstF: "\<lbrakk>(e, v1) \<in> tgtst (sg F); v2 \<in> clanF v1 F\<rbrakk> \<Longrightarrow> (e, v2) \<in> tgtstF F"
  proof -
    assume h1: "(e, v1) \<in> tgtst (sg F)"
    assume h2: "v2 \<in> clanF v1 F"
    show "(e, v2) \<in> tgtstF F"
    proof (simp add: tgtstF_def)
      apply_end(rule conjI)
      from h1 h2 show "e \<in> EsA (sg F)" by (simp add: tgtst_def)
    next
      from h1 h2 show "\<exists>v2a. v2 \<in> clanF v2a F \<and> (e, v2a) \<in> tgtst (sg F)"
        by (rule_tac exI[where x="v1"], simp)
    qed
  qed

lemma the_tgt_clanF:
  assumes "(e, v1) \<in> tgtst (sg F)" and "v2 \<in> clanF v1 F"
  shows "v2 \<in> clanF (the (tgt (sg F) e)) F"
  proof -
    have h1: "(inh (sg F))\<^sup>* \<subseteq> (inh (sg F) \<union> reps F)\<^sup>*"
      by (simp add: rtrancl_cpm_of_Un_in_Un)
    show ?thesis
    using assms h1 
    by (auto simp add: tgtst_def clanF_def clan_def inhstF_def inhF_def inhst_def)
  qed

definition morphFr :: "Fr \<Rightarrow> Fr \<Rightarrow> Morph set"
where
  "morphFr F1 F2 \<equiv> {r. is_wf_fr F1 \<and> is_wf_fr F2
      \<and> ftotal_on (fV r) (Ns (sg F1)) (Ns (sg F2)) 
      \<and> ftotal_on (fE r) (Es (sg F1)) (Es (sg F2))  
      \<and> srcstF F1 O pfunToRel(fV r)  \<subseteq> pfunToRel(fE r) O srcstF F2
      \<and> tgtstF F1 O pfunToRel(fV r)  \<subseteq> pfunToRel(fE r) O tgtstF F2
      \<and> inhstF F1 O pfunToRel(fV r)  \<subseteq> pfunToRel(fV r) O inhstF F2}"

end
