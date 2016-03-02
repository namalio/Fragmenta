(*  Title:       Fragmenta theory of Fragments (Frs), list version
    Description: 'Fragmenta' theory presented in the Models 2015 paper.
    Author:      Nuno Amálio
*)
theory Fragmenta_FrsL
imports Fragmenta_Frs Fragmenta_SGsL "Extra/List_Extra" 
  "Extra/Finite_Transitive_Closure_Simprocs"
                    
begin

(*The list version of Fragments*)      
record Fr_ls = 
  sg_ls :: "SGr_ls"
  tr_ls :: "(E \<times> V) list"

(* Defines the empty FrL*)
definition emptyFrL :: "Fr_ls"
where
  "emptyFrL \<equiv> \<lparr>sg_ls = emptySGL, tr_ls = []\<rparr>"

(*Conversion function from list to plain fragment form*)
definition toFr :: "Fr_ls \<Rightarrow> Fr"
where
  "toFr FL \<equiv> \<lparr>sg = toSGr (sg_ls FL), tr = map_of(tr_ls FL)\<rparr>"

definition consRefsE:: "Fr \<Rightarrow> E \<Rightarrow> (V\<times>V) list"
where
  "consRefsE F e \<equiv> (if is_RP e F
    then [(the (src (sg F) e), the (tr F e))] else [])"

primrec consRefs0:: "Fr \<Rightarrow> E list \<Rightarrow> (V\<times>V) list"
where
  "consRefs0 F [] = []"
  | "consRefs0 F (e#es) = (consRefsE F e)@(consRefs0 F es)"

lemma in_consRefs0_insertls: 
  "(x, y) \<in> set(consRefs0 F (e # es)) \<longleftrightarrow> (x, y) \<in> set(consRefsE F e) \<union> set(consRefs0 F es)"
  by simp

lemma in_consRefs0:
  fixes x y es 
  assumes ha: "set es \<subseteq> Es (sg F)" and hb: "is_wf_sg (sg F)"
    and hc: "ftotal_on (tr F) (EsRP (sg F)) (V_A)"
  shows "(x, y) \<in> set(consRefs0 F es) \<longleftrightarrow> 
    (\<exists> e. e \<in> (set es) \<and> is_RP e F  \<and> (src (sg F)) e  = Some x 
      \<and> tr F e = Some y)"
  proof
    assume hd: "(x, y) \<in> set(consRefs0 F es)"
    then show "\<exists>e. e \<in> set es  \<and> is_RP e F 
      \<and> src (sg F) e = Some x \<and> tr F e = Some y"
    proof (induct es, simp)
      fix a es'
      assume he: "((x, y) \<in> set(consRefs0 F es') \<Longrightarrow>
        \<exists>e. e \<in> set es' \<and>
             is_RP e F \<and> src (sg F) e = Some x \<and> tr F e = Some y)"
      assume hf: "(x, y) \<in> set(consRefs0 F (a # es'))"
      show "\<exists>e. e \<in> set (a # es') \<and>
                 is_RP e F \<and> src (sg F) e = Some x \<and> tr F e = Some y"
      proof (case_tac "is_RP a F")
        assume hg: "is_RP a F"
        from hf hg have hh: "(x, y) \<in> {(the (src (sg F) a), the (tr F a))} \<union> set(consRefs0 F es')"
          by (auto simp add: consRefsE_def)
        then show "\<exists>e. e \<in> set (a # es')  \<and> is_RP e F \<and> src (sg F) e = Some x 
          \<and> tr F e = Some y"
        proof (case_tac "(x, y) \<in> set(consRefs0 F es')")
          assume "(x, y) \<in> set(consRefs0 F es')"
          then show "\<exists>e. e \<in> set (a # es') \<and> is_RP e F 
            \<and> src (sg F) e = Some x \<and> tr F e = Some y"
            using hh he by (auto)
        next
          have hi: "a \<in> dom (src (sg F))"
            using hg hb by (simp add: is_RP_def)
            (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
          from hg hb hc have hj: "a \<in> dom (tr F)"
            by (simp add: is_RP_eq_in_EsRP is_wf_sg_def ftotal_on_def)
          assume "(x, y) \<notin> set(consRefs0 F es')"
          then have "(x, y) \<in> {(the (src (sg F) a), the (tr F a))}"
            using hh by simp
          then have "src (sg F) a = Some x \<and> tr F a = Some y"
            using hi hj by (simp add: domD)
          then show "\<exists>e. e \<in> set (a # es') \<and> is_RP e F \<and> src (sg F) e = Some x \<and> tr F e = Some y"
            using hh hg by (auto)
        qed
      next
        assume hg: "\<not>is_RP a F"
        from hf hg have hg: "(x, y) \<in> set(consRefs0 F es')" 
          by (auto simp add: consRefsE_def)
        then have "\<exists>e. e \<in> set es' \<and> is_RP e F \<and> src (sg F) e = Some x 
          \<and> tr F e = Some y"
          using he by simp
        then show "\<exists>e. e \<in> set (a # es') \<and> is_RP e F \<and> src (sg F) e = Some x 
          \<and> tr F e = Some y"
          by (auto)
      qed
    qed
  next
    assume hd: "\<exists>e. e \<in> set es \<and> is_RP e F \<and> src (sg F) e = Some x \<and> tr F e = Some y"
    then show "(x, y) \<in> set(consRefs0 F es)"
    proof (clarify)
      fix a
      assume he: "a \<in> set es"
      assume hf: "is_RP a F"
      assume hg: "src (sg F) a = Some x"
      assume hh: "tr F a = Some y"
      from he show "(x, y) \<in> set(consRefs0 F es)"
      proof (induct es, simp)
        fix a' es'
        assume hj: "(a \<in> set es' \<Longrightarrow> (x, y) \<in> set(consRefs0 F es'))"
        assume hk: "a \<in> set (a' # es')"
        show "(x, y) \<in> set(consRefs0 F (a' # es'))"
        proof (simp add: in_consRefs0_insertls, case_tac "a=a'")
          assume "a = a'"
          then show "(x, y) \<in> set(consRefsE F a') \<or> (x, y) \<in> set(consRefs0 F es')"
            using ha he hf hg hh by (auto simp add: consRefsE_def)
        next
          assume hl: "a \<noteq> a'"
          show "(x, y) \<in> set(consRefsE F a') \<or> (x, y) \<in> set(consRefs0 F es')"
          proof (rule disjI2)
            from hk hl have "a \<in> set es'"
              by simp
            then have "(x, y) \<in> set(consRefs0 F es')"
              using hj by simp
            then show "(x, y) \<in> set(consRefs0 F es')"
              by simp
          qed
        qed
      qed
    qed
  qed


definition consRefs:: "Fr_ls \<Rightarrow> (V\<times>V) list"
where
  "consRefs FL = consRefs0 (toFr FL) (EsG (sg_ls FL))"

lemma in_consRefs: 
  fixes x y
  assumes ha: "is_wf_sg (sg (toFr FL))" 
    and hb: "ftotal_on (tr (toFr FL)) (EsRP (sg (toFr FL))) (V_A)"
  shows "(x, y) \<in> set(consRefs FL)  \<longleftrightarrow> 
    (\<exists> e. e \<in> set (EsG (sg_ls FL)) \<and> is_RP e (toFr FL)  
      \<and> src (sg (toFr FL)) e  = Some x \<and> tr (toFr FL) e = Some y)"
    proof -
      have hc: "set (EsG (sg_ls FL)) \<subseteq> Es (sg (toFr FL))" 
        by (auto simp add: toFr_def toSGr_def)
      show ?thesis
      proof
        assume "(x, y) \<in> set(consRefs FL)"
        then have "(x, y) \<in> set(consRefs0 (toFr FL) (EsG (sg_ls FL)))"
          by (simp add: consRefs_def)
        then have "(\<exists> e. e \<in> set (EsG (sg_ls FL)) \<and> is_RP e (toFr FL) 
          \<and> src (sg (toFr FL)) e  = Some x 
          \<and> tr (toFr FL)  e = Some y)"
          using ha hb hc 
          by (simp add: in_consRefs0)
        then 
        show "(\<exists>e. e \<in> set (EsG (sg_ls FL)) \<and>
         is_RP e (toFr FL) \<and> src (sg (toFr FL)) e = Some x \<and> tr (toFr FL) e = Some y)"
          by simp
      next
        assume "\<exists>e. e \<in> set (EsG (sg_ls FL)) \<and> is_RP e (toFr FL)
           \<and> src (sg (toFr FL)) e = Some x \<and> tr (toFr FL) e = Some y"
        then have "(x, y) \<in> set(consRefs0 (toFr FL) (EsG (sg_ls FL)))"
          using ha hb hc 
          by (simp add: in_consRefs0)
        then show "(x, y) \<in> set(consRefs FL)"
          by (simp add: consRefs_def)
      qed
    qed

lemma refs_eq_consRefs:
  assumes ha: "is_wf_sg (sg (toFr FL))" 
    and hb: "ftotal_on (tr (toFr FL)) (EsRP (sg (toFr FL))) (V_A)"
  shows "refs (toFr FL) = set(consRefs FL)"
  proof
    show "refs (toFr FL) \<subseteq> set(consRefs FL)"
    proof (rule subrelI)
      fix x y
      assume "(x, y) \<in> refs (toFr FL)"
      then have "\<exists>e. e \<in> set (EsG (sg_ls FL)) \<and> is_RP e (toFr FL) 
        \<and> src (sg (toFr FL)) e  = Some x \<and> tr (toFr FL) e = Some y"
        using ha hb by (auto simp add: refs_def relOfGr_def adjacent_def rst_fun_def 
          restrict_map_def EsRP_def EsR_def
          EsTy_def is_wf_sg_def is_wf_g_def ftotal_on_def is_RP_def)
          (rule exI, auto simp add: in_set_EsG toFr_def tgtr_def NsP_def NsTy_def)
      then show "(x, y) \<in> set(consRefs FL)"
        using ha hb by (simp add: in_consRefs)
    qed
  next
    show "set(consRefs FL) \<subseteq> refs (toFr FL)"
    proof (rule subrelI)
      fix x y
      assume "(x, y) \<in> set(consRefs FL)"
      then have "\<exists> e. e \<in> set (EsG (sg_ls FL)) \<and> is_RP e (toFr FL) 
        \<and> src (sg (toFr FL)) e  = Some x \<and> tr (toFr FL) e = Some y" 
        using ha hb by (simp add: in_consRefs)
      then show "(x, y) \<in> refs (toFr FL)"
      proof (clarify)
        fix e 
        assume "e \<in> set (EsG (sg_ls FL))"
        then have hc: "e \<in> Es (sg (toFr FL))"
          by (simp add: toFr_def in_set_EsG)
        assume hd: "is_RP e (toFr FL)"
        assume he: "src (sg (toFr FL)) e = Some x"
        assume hf: "tr (toFr FL) e = Some y"
        show "(x, y) \<in> refs (toFr FL)"
        using hb hc hd he hf ha
        by (simp add: refs_def refsG_def relOfGr_def adjacent_def restrict_def rst_fun_def)
         (rule exI[where x="e"], 
        auto simp add: is_wf_sg_def is_wf_g_def ftotal_on_def restrict_map_def tgtr_def)
      qed
    qed
  qed

definition consReps :: "Fr_ls \<Rightarrow> (V\<times>V) list"
where
  "consReps FL \<equiv> (let lrefs = consRefs FL in
    lrefs@(zip(map snd lrefs)(map fst lrefs)))"

lemma reps_eq_consReps:
  assumes "is_wf_sg (sg (toFr FL))" 
    and "ftotal_on (tr (toFr FL)) (EsRP (sg (toFr FL))) (V_A)"
  shows "reps (toFr FL) = set(consReps FL)"
  using assms by (simp add: consReps_def Let_def reps_def refs_eq_consRefs set_list_inv_eq)

(*A construction for the 'inhF' relation*)
definition consInhF:: "Fr_ls \<Rightarrow> (V\<times>V) list"
where
  "consInhF FL \<equiv> (consInh (sg_ls FL))@(consReps FL)"

lemma inhF_eq_consInhF: 
  assumes ha: "is_wf_sg (sg (toFr FL))" 
    and "ftotal_on (tr (toFr FL)) (EsRP (sg (toFr FL))) (V_A)"
  shows "inhF (toFr FL) = set(consInhF FL)"
  proof -
    from ha have h1: "is_wf_g (toSGr (sg_ls FL))"
      by (simp add: toFr_def is_wf_sg_def)
    have h2: "inh (sg (toFr FL)) = inh (toSGr (sg_ls FL))"
      by (simp add: toFr_def)
    from assms show ?thesis
    using h1 
      by (simp add: inhF_def consInhF_def reps_eq_consReps h2 inh_eq_consInh)
  qed

definition consClanF::"V \<Rightarrow> Fr_ls \<Rightarrow> V list"
where
  "consClanF v FL \<equiv> 
    (let consInhF = consInhF FL in
      rtrancl_list_impl (zip(map snd consInhF)(map fst consInhF)) [v])"

lemma consClanF_eq_clanF: 
  assumes ha: "is_wf_sg (sg (toFr FL))" 
    and "ftotal_on (tr (toFr FL)) (EsRP (sg (toFr FL))) (V_A)"
  shows "clanF v (toFr FL) = set(consClanF v FL)"
  proof -
    have h1: "((inhF (toFr FL))\<^sup>*)\<inverse> = ((inhF (toFr FL))\<inverse>)\<^sup>*"
      by (simp add: rtrancl_converse)
    from assms show ?thesis
    by (simp add: clanF_def consClanF_def Let_def inhstF_def h1)
      (simp add: inhF_eq_consInhF set_list_inv_eq rtrancl_Image_eq)
  qed

fun consSrcStFE::"Fr_ls \<Rightarrow> E \<Rightarrow> (E\<times>V) list" 
where
  "consSrcStFE FL e = (if ety (sg (toFr FL)) e \<in> {Some ecompbi, Some ecompuni, Some erelbi, Some ereluni, Some elnk}
      then map (Pair e) (consClanF (the(src (sg (toFr FL)) e)) FL)
      else [])"

primrec consSrcStF0::"Fr_ls \<Rightarrow> E list \<Rightarrow> (E\<times>V) list" 
where
  "consSrcStF0 FL [] = []" |
  "consSrcStF0 FL (e#es) = (consSrcStFE FL e)@(consSrcStF0 FL es)"

lemma in_consSrcStF0: 
  "(e', v) \<in> set(consSrcStF0 FL (e # es)) \<longleftrightarrow> 
    (e', v) \<in> set(consSrcStFE FL e) \<or> (e', v) \<in> set(consSrcStF0 FL es)"
  by (simp)

lemma in_consSrcStF0_hd: 
  "(e, v) \<in> set(consSrcStF0 FL (e # es)) \<longleftrightarrow> (e, v) \<in> set(consSrcStFE FL e)"
  by (induct es, auto)

lemma in_consSrcStF0_nothd: 
  assumes "e' \<noteq> e"
  shows "(e', v) \<in> set(consSrcStF0 FL (e # es)) 
    \<longleftrightarrow> (e', v) \<in> set(consSrcStF0 FL es)"
  using assms by (induct es, auto)

lemma in_consSrcStF0_iff:
  fixes e v es 
  assumes ha: "set es \<subseteq> set(EsG (sg_ls FL))" and hb: "is_wf_sg (sg (toFr FL))" 
    and hc: "ftotal_on (tr (toFr FL)) (EsRP (sg (toFr FL))) (V_A)"
  shows "(e, v) \<in> set(consSrcStF0 FL es) \<longleftrightarrow> 
    (e \<in> set(es) \<and> e \<in> EsA (sg (toFr FL)) 
      \<and> (\<exists>v2. v \<in> clanF v2 (toFr FL) \<and> (e, v2) \<in> srcst (sg (toFr FL))))"
  proof -
    from hb have hb1: "is_wf_g (sg (toFr FL))"
      by (simp add: is_wf_sg_def)
    show ?thesis
    proof
      assume "(e, v) \<in> set (consSrcStF0 FL es)"
      then show "e \<in> set es \<and>
        e \<in> EsA (sg (toFr FL)) \<and> (\<exists>v2. v \<in> clanF v2 (toFr FL) 
        \<and> (e, v2) \<in> srcst (sg (toFr FL)))"
      proof (induct es, simp)
        fix a es'
        assume hd: "(e, v) \<in> set (consSrcStF0 FL es') \<Longrightarrow>
             e \<in> set es' \<and>
             e \<in> EsA (sg (toFr FL)) \<and>
             (\<exists>v2. v \<in> clanF v2 (toFr FL) \<and> (e, v2) \<in> srcst (sg (toFr FL)))"
        and he: "(e, v) \<in> set (consSrcStF0 FL (a # es')) "
        then show "e \<in> set (a # es') \<and> e \<in> EsA (sg (toFr FL)) 
          \<and> (\<exists>v2. v \<in> clanF v2 (toFr FL) \<and> (e, v2) \<in> srcst (sg (toFr FL)))"
        proof (case_tac "e=a")
          assume hf: "e=a"
          then have hg: "(a, v) \<in> set(consSrcStFE FL e)"
            using he by (simp only: in_consSrcStF0_hd)
          then have "a \<in> EsA (sg (toFr FL))" by (simp add: image_def EsA_def EsTy_def)
          then show "e \<in> set (a # es') \<and> e \<in> EsA (sg (toFr FL))   
            \<and> (\<exists>v2. v \<in> clanF v2 (toFr FL) \<and> (e, v2) \<in> srcst (sg (toFr FL)))"
            using hf hb1 hb hc hg
              by (simp add: image_def)
              (rule exI[where x="the(src (sg (toFr FL)) a)"], 
                auto simp add: consClanF_eq_clanF is_wf_g_def ftotal_on_def 
                the_src_in_srcst)
        next
          assume hf: "e\<noteq>a"
          then have "(e, v) \<in> set (consSrcStF0 FL es')"
            using he in_consSrcStF0_nothd by (simp)
          then show "e \<in> set (a # es') \<and> e \<in> EsA (sg (toFr FL))
            \<and>  (\<exists>v2. v \<in> clanF v2 (toFr FL) \<and> (e, v2) \<in> srcst (sg (toFr FL)))"
            using hd by simp
        qed
      qed
    next
      assume "e \<in> set es \<and> e \<in> EsA (sg (toFr FL)) 
        \<and> (\<exists>v2. v \<in> clanF v2 (toFr FL) \<and> (e, v2) \<in> srcst (sg (toFr FL)))"
      then show "(e, v) \<in> set (consSrcStF0 FL es)"
      proof (clarify)
        fix v2
        assume h1: "e \<in> set es"
        and h2: "e \<in> EsA (sg (toFr FL))"
        and h3: "v \<in> clanF v2 (toFr FL)"
        and h4: "(e, v2) \<in> srcst (sg (toFr FL))"
        from h1 show "(e, v) \<in> set (consSrcStF0 FL es)"
        proof (induct es, simp)
          fix a es
          assume h5: "e \<in> set es \<Longrightarrow> (e, v) \<in> set (consSrcStF0 FL es)"
            and h6: "e \<in> set (a # es)"
          then show "(e, v) \<in> set (consSrcStF0 FL (a # es))"
          proof (case_tac "e=a")
            assume "e=a"
            then show "(e, v) \<in> set (consSrcStF0 FL (a # es))"
              using h2 h3 h4 hb1 hb hc the_src_clanF[where e="a" and F="toFr FL"] 
              by (simp only: in_consSrcStF0_hd)
              (simp add: image_def consClanF_eq_clanF EsA_def EsTy_def)
          next
            assume "e\<noteq>a"
            then show "(e, v) \<in> set (consSrcStF0 FL (a # es))"
              using in_consSrcSt0_nothd h5 h6
              by (simp)
          qed
        qed
      qed
    qed
  qed

definition consSrcStF:: "Fr_ls \<Rightarrow> (E\<times>V) list"
where
  "consSrcStF FL \<equiv> consSrcStF0 FL (EsG (sg_ls FL))"

lemma in_consSrcStF: 
  fixes e v
  assumes ha: "is_wf_sg (sg (toFr FL))"
    and hb: "ftotal_on (tr (toFr FL)) (EsRP (sg (toFr FL))) (V_A)"
  shows "(e, v) \<in> set(consSrcStF FL)  \<longleftrightarrow> 
     (e \<in> EsA (sg (toFr FL)) 
     \<and> (\<exists>v2. v \<in> clanF v2 (toFr FL) \<and> (e, v2) \<in> srcst (sg (toFr FL))))"
  proof -
      from ha have ha1: "is_wf_sg (toSGr (sg_ls FL))"
        by (simp add: toFr_def)
      have hc: "set (EsG (sg_ls FL)) \<subseteq> Es (sg (toFr FL))" 
        by (simp add: toFr_def toSGr_def)
      have hd: "e \<in> EsA (sg(toFr FL)) \<Longrightarrow> e \<in> set (EsG (sg_ls FL))"
        by (simp add: Fragmenta_SGsL.in_set_EsG ha1 in_EsA_in_ES toFr_def)
      show ?thesis
      using ha hb hd ha1 by (auto simp add: consSrcStF_def in_consSrcStF0_iff hc)
  qed

lemma srcstF_eq_consSrcStF: 
  assumes ha: "is_wf_sg (sg (toFr FL))"
    and hb: "ftotal_on (tr (toFr FL)) (EsRP (sg (toFr FL))) (V_A)"
  shows "srcstF (toFr FL) = set(consSrcStF FL)"
  using assms by (auto simp add: srcstF_def in_consSrcStF)

fun consTgtStFE::"Fr_ls \<Rightarrow> E \<Rightarrow> (E\<times>V) list" 
where
  "consTgtStFE FL e = (if ety (sg (toFr FL)) e \<in> {Some ecompbi, Some ecompuni, Some erelbi, Some ereluni, Some elnk}
      then map (Pair e) (consClanF (the(tgt (sg (toFr FL)) e)) FL)
      else [])"

primrec consTgtStF0::"Fr_ls \<Rightarrow> E list \<Rightarrow> (E\<times>V) list" 
where
  "consTgtStF0 FL [] = []" |
  "consTgtStF0 FL (e#es) = (consTgtStFE FL e)@(consTgtStF0 FL es)"

lemma in_consTgtStF0: 
  "(e', v) \<in> set(consTgtStF0 FL (e # es)) \<longleftrightarrow> 
    (e', v) \<in> set(consTgtStFE FL e) \<or> (e', v) \<in> set(consTgtStF0 FL es)"
  by (simp)

lemma in_consTgtStF0_hd: 
  "(e, v) \<in> set(consTgtStF0 FL (e # es)) \<longleftrightarrow> (e, v) \<in> set(consTgtStFE FL e)"
  by (induct es, auto)

lemma in_consTgtStF0_nothd: 
  assumes "e' \<noteq> e"
  shows "(e', v) \<in> set(consTgtStF0 FL (e # es)) 
    \<longleftrightarrow> (e', v) \<in> set(consTgtStF0 FL es)"
  using assms by (induct es, auto)

lemma in_consTgtStF0_iff:
  fixes e v es 
  assumes ha: "set es \<subseteq> set(EsG (sg_ls FL))" and hb: "is_wf_sg (sg (toFr FL))" 
    and hc: "ftotal_on (tr (toFr FL)) (EsRP (sg (toFr FL))) (V_A)"
  shows "(e, v) \<in> set(consTgtStF0 FL es) \<longleftrightarrow> 
    (e \<in> set(es) \<and> e \<in> EsA (sg (toFr FL)) 
      \<and> (\<exists>v2. v \<in> clanF v2 (toFr FL) \<and> (e, v2) \<in> tgtst (sg (toFr FL))))"
  proof -
    from hb have hb1: "is_wf_g (sg (toFr FL))"
      by (simp add: is_wf_sg_def)
    show ?thesis
    proof
      assume "(e, v) \<in> set (consTgtStF0 FL es)"
      then show "e \<in> set es \<and>
        e \<in> EsA (sg (toFr FL)) \<and> (\<exists>v2. v \<in> clanF v2 (toFr FL) 
        \<and> (e, v2) \<in> tgtst (sg (toFr FL)))"
      proof (induct es, simp)
        fix a es'
        assume hd: "(e, v) \<in> set (consTgtStF0 FL es') \<Longrightarrow>
             e \<in> set es' \<and>
             e \<in> EsA (sg (toFr FL)) \<and>
             (\<exists>v2. v \<in> clanF v2 (toFr FL) \<and> (e, v2) \<in> tgtst (sg (toFr FL)))"
        and he: "(e, v) \<in> set (consTgtStF0 FL (a # es')) "
        then show "e \<in> set (a # es') \<and> e \<in> EsA (sg (toFr FL)) 
          \<and> (\<exists>v2. v \<in> clanF v2 (toFr FL) \<and> (e, v2) \<in> tgtst (sg (toFr FL)))"
        proof (case_tac "e=a")
          assume hf: "e=a"
          then have hg: "(a, v) \<in> set(consTgtStFE FL e)"
            using he by (simp only: in_consTgtStF0_hd)
          then have "a \<in> EsA (sg (toFr FL))" by (simp add: image_def EsA_def EsTy_def)
          then show "e \<in> set (a # es') \<and> e \<in> EsA (sg (toFr FL))   
            \<and> (\<exists>v2. v \<in> clanF v2 (toFr FL) \<and> (e, v2) \<in> tgtst (sg (toFr FL)))"
            using hf hb1 hb hc hg
              by (simp add: image_def)
              (rule exI[where x="the(tgt (sg (toFr FL)) a)"], 
                auto simp add: consClanF_eq_clanF is_wf_g_def ftotal_on_def 
                the_tgt_in_tgtst)
        next
          assume hf: "e\<noteq>a"
          then have "(e, v) \<in> set (consTgtStF0 FL es')"
            using he in_consTgtStF0_nothd by (simp)
          then show "e \<in> set (a # es') \<and> e \<in> EsA (sg (toFr FL))
            \<and>  (\<exists>v2. v \<in> clanF v2 (toFr FL) \<and> (e, v2) \<in> tgtst (sg (toFr FL)))"
            using hd by simp
        qed
      qed
    next
      assume "e \<in> set es \<and> e \<in> EsA (sg (toFr FL)) 
        \<and> (\<exists>v2. v \<in> clanF v2 (toFr FL) \<and> (e, v2) \<in> tgtst (sg (toFr FL)))"
      then show "(e, v) \<in> set (consTgtStF0 FL es)"
      proof (clarify)
        fix v2
        assume h1: "e \<in> set es"
        and h2: "e \<in> EsA (sg (toFr FL))"
        and h3: "v \<in> clanF v2 (toFr FL)"
        and h4: "(e, v2) \<in> tgtst (sg (toFr FL))"
        from h1 show "(e, v) \<in> set (consTgtStF0 FL es)"
        proof (induct es, simp)
          fix a es
          assume h5: "e \<in> set es \<Longrightarrow> (e, v) \<in> set (consTgtStF0 FL es)"
            and h6: "e \<in> set (a # es)"
          then show "(e, v) \<in> set (consTgtStF0 FL (a # es))"
          proof (case_tac "e=a")
            assume "e=a"
            then show "(e, v) \<in> set (consTgtStF0 FL (a # es))"
              using h2 h3 h4 hb1 hb hc the_tgt_clanF[where e="a" and F="toFr FL"] 
              by (simp only: in_consTgtStF0_hd)
              (simp add: image_def consClanF_eq_clanF EsA_def EsTy_def)
          next
            assume "e\<noteq>a"
            then show "(e, v) \<in> set (consTgtStF0 FL (a # es))"
              using in_consTgtStF0_nothd h5 h6
              by (simp)
          qed
        qed
      qed
    qed
  qed

definition consTgtStF:: "Fr_ls \<Rightarrow> (E\<times>V) list"
where
  "consTgtStF FL \<equiv> consTgtStF0 FL (EsG (sg_ls FL))"

lemma in_consTgtStF: 
  fixes e v
  assumes ha: "is_wf_sg (sg (toFr FL))"
    and hb: "ftotal_on (tr (toFr FL)) (EsRP (sg (toFr FL))) (V_A)"
  shows "(e, v) \<in> set(consTgtStF FL)  \<longleftrightarrow> 
     (e \<in> EsA (sg (toFr FL)) 
     \<and> (\<exists>v2. v \<in> clanF v2 (toFr FL) \<and> (e, v2) \<in> tgtst (sg (toFr FL))))"
  proof -
      from ha have ha1: "is_wf_sg (toSGr (sg_ls FL))"
        by (simp add: toFr_def)
      have hc: "set (EsG (sg_ls FL)) \<subseteq> Es (sg (toFr FL))" 
        by (simp add: toFr_def toSGr_def)
      have hd: "e \<in> EsA (sg(toFr FL)) \<Longrightarrow> e \<in> set (EsG (sg_ls FL))"
        by (simp add: Fragmenta_SGsL.in_set_EsG ha1 in_EsA_in_ES toFr_def)
      show ?thesis
      using ha hb hd ha1 by (auto simp add: consTgtStF_def in_consTgtStF0_iff hc)
  qed

lemma tgtstF_eq_consTgtStF: 
  assumes ha: "is_wf_sg (sg (toFr FL))"
    and hb: "ftotal_on (tr (toFr FL)) (EsRP (sg (toFr FL))) (V_A)"
  shows "tgtstF (toFr FL) = set(consTgtStF FL)"
  using assms by (auto simp add: tgtstF_def in_consTgtStF)

definition consUF:: "Fr_ls \<Rightarrow> Fr_ls \<Rightarrow> Fr_ls"
where
  "consUF FL1 FL2 = \<lparr>sg_ls = (consUSG (sg_ls FL1)(sg_ls FL2)), 
    tr_ls = (tr_ls FL2)@(tr_ls FL1)\<rparr>"

primrec consUFs:: "Fr_ls list \<Rightarrow> Fr_ls"
where
  "consUFs [] = emptyFrL"
  | "consUFs (FL#FLs) = consUF FL (consUFs FLs)"

(*Theorem that shows that they are the same*)
lemma UFEqConsUF: "(toFr FL1) UF (toFr FL2) = toFr (consUF FL1 FL2)"
  proof (simp add: Fr_eq, rule conjI)
    show "sg (toFr FL1) USG sg(toFr FL2) = sg (toFr (consUF FL1 FL2))"
      by (simp add: toFr_def cupF_def consUF_def USGEqconsUSG)
  next
    show "tr (toFr FL1) ++ tr (toFr FL2) = tr (toFr (consUF FL1 FL2))"
      by (simp add: cupF_def consUF_def toFr_def)
  qed

lemma UFsEqConsUFs: "UFs (map toFr FLs) = toFr (consUFs FLs)"
  proof (simp add: Fr_eq, rule conjI)
    show "sg (UFs (map toFr FLs)) = sg (toFr (consUFs FLs))"
    proof (induct FLs)
      show "sg (UFs (map toFr [])) = sg (toFr (consUFs []))"
        by (simp add: emptyFr_def toFr_def emptyFrL_def toSGr_def emptySG_def
          emptySGL_def)
    next
      apply_end(simp)
      fix F FLs
      have ha: "toFr (consUF F (consUFs FLs)) = toFr F UF toFr (consUFs FLs)"
        by (simp add: UFEqConsUF)
      assume "sg (UFs (map toFr FLs)) = sg (toFr (consUFs FLs))"
      then show "sg (toFr F) USG sg (toFr (consUFs FLs)) = sg (toFr (consUF F (consUFs FLs)))"
        using ha by (simp)
    qed
  next
    show "tr (UFs (map toFr FLs)) = tr (toFr (consUFs FLs))"
    proof (induct FLs)
      show "tr (UFs (map toFr [])) = tr (toFr (consUFs []))"
        by (simp add: emptyFr_def toFr_def emptyFrL_def toSGr_def emptySG_def
          emptySGL_def)
    next
      apply_end(simp)
      fix F FLs
      have ha: "toFr (consUF F (consUFs FLs)) = toFr F UF toFr (consUFs FLs)"
        by (simp add: UFEqConsUF)
      assume "tr (UFs (map toFr FLs)) = tr (toFr (consUFs FLs))"
      then show "tr (toFr F) ++ tr (toFr (consUFs FLs)) = tr (toFr (consUF F (consUFs FLs)))"
        using ha by (simp)
    qed
  qed

lemma set_Nsg_concat: "set(NsG (sg_ls (consUFs FLs))) = set (concat(map (NsG \<circ> sg_ls) FLs))"
  proof (induct FLs)
    show "set (NsG (sg_ls (consUFs []))) = set (concat (map (NsG \<circ> sg_ls) []))"
      by (simp add: consUFs_def emptyFrL_def emptySGL_def)
  next
    fix a FLs
    assume "set (NsG (sg_ls (consUFs FLs))) = set (concat (map (NsG \<circ> sg_ls) FLs))"
    then show "set (NsG (sg_ls (consUFs (a # FLs)))) = set (concat (map (NsG \<circ> sg_ls) (a # FLs)))"
      by (simp add: consUF_def consUSG_def)
  qed

lemma Ns_Ufs_Eq: "Ns (sg (UFs Fs)) = fold union (map (Ns\<circ> sg) Fs) {}"
  proof (induct Fs)
    show "Ns (sg (UFs [])) = fold op \<union> (map (Ns \<circ> sg) []) {}"
      by (simp add: UFs_def emptyFr_def emptySG_def)
  next
    fix a Fs
    assume "Ns (sg (UFs Fs)) = fold op \<union> (map (Ns \<circ> sg) Fs) {}"
    then show "Ns (sg (UFs (a # Fs))) = fold op \<union> (map (Ns \<circ> sg) (a # Fs)) {}"
      using fold_union[of "map (Ns \<circ> sg) Fs" "Ns (sg a)"]
      by (simp add: cupSG_def)
  qed

end