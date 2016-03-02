(*  Title:      Fragmenta theory of structural graphs (SGs)
    Description: 'Fragmenta' theory presented in the Models 2015 paper.
    Author:     Nuno Amálio
*)
theory Fragmenta_SGsL
imports Fragmenta_SGs Fragmenta_GraphsL "Extra/Finite_Transitive_Closure_Simprocs"

begin

(* An alternative representation of SGs based on lists*)
record SGr_ls = Gr_ls +
  ntyG :: "(V \<times> SGNTy) list"
  etyG :: "(E \<times> SGETy) list" 
  srcmG  :: "(E \<times> MultVal) list"
  tgtmG  :: "(E \<times> MultVal) list"

(* Defines the empty SG*)
definition emptySGL :: "SGr_ls"
where
  "emptySGL \<equiv> \<lparr>NsG = [], EsG = [], srcG = [], tgtG = [], 
    ntyG = [], etyG = [], srcmG = [], tgtmG = []\<rparr>"

(*A function that converts the list-based representation to the set-based one*)
definition toSGr :: "SGr_ls \<Rightarrow> SGr"
where
  "toSGr SGL \<equiv> \<lparr>Ns = set (NsG SGL), Es = set (EsG SGL), 
    src = map_of (srcG SGL), tgt = map_of (tgtG SGL),
    nty = map_of (ntyG SGL), ety = map_of (etyG SGL), 
    srcm  = map_of (srcmG SGL), tgtm = map_of (tgtmG SGL)\<rparr>"

lemma in_set_EsG: "e \<in> set (EsG SGL) \<longleftrightarrow> e \<in> Es (toSGr SGL)"
  by (simp add: toSGr_def)

definition consInhE:: "SGr \<Rightarrow> E \<Rightarrow> (V\<times>V) list"
where
  "consInhE SG e \<equiv> (if e \<in> Es SG - EsId SG \<and> ety SG e = Some einh then 
      [(the (src SG e),  the (tgt SG e))] 
      else [])"

primrec consInh0:: "SGr \<Rightarrow> E list \<Rightarrow> (V\<times>V) list"
where
  "consInh0 SG [] = []"
  | "consInh0 SG (e#es) = (consInhE SG e)@(consInh0 SG es)"

lemma in_consInh0_insertls: 
  "(x, y) \<in> set(consInh0 SG (e # es)) \<longleftrightarrow> (x, y) \<in> set(consInhE SG e) \<union> set(consInh0 SG es)"
  by simp
    
lemma in_consInh0:
  fixes x y es 
  assumes ha: "set es \<subseteq> Es SG" and hb: "is_wf_g SG"
  shows "(x, y) \<in> set(consInh0 SG es) \<longleftrightarrow> 
    (\<exists> e. e \<in> (set es) \<and> e \<notin> EsId SG \<and> ety SG e = Some einh  \<and> (src SG) e  = Some x 
      \<and> (tgt SG) e = Some y)"
  proof
    assume hc: "(x, y) \<in> set(consInh0 SG es)"
    then show "\<exists>e. e \<in> set es \<and> e \<notin> EsId SG \<and> ety SG e = Some einh \<and> src SG e = Some x 
      \<and> tgt SG e = Some y"
    proof (induct es, simp)
      fix a es'
      assume hd: "(x, y) \<in> set(consInh0 SG es') \<Longrightarrow>
        \<exists>e. e \<in> set es' \<and> e \<notin> EsId SG \<and> ety SG e = Some einh \<and> src SG e = Some x \<and> tgt SG e = Some y"
      assume he: "(x, y) \<in> set(consInh0 SG (a # es'))"
      show "\<exists>e. e \<in> set (a # es') \<and> e \<notin> EsId SG \<and> ety SG e = Some einh \<and> src SG e = Some x \<and> tgt SG e = Some y"
      proof (case_tac "a \<in> Es SG - EsId SG \<and> ety SG a = Some einh")
        assume hf: "a \<in> Es SG- EsId SG \<and> ety SG a = Some einh"
        from he hf have hg: "(x, y) \<in> {(the (src SG a), the (tgt SG a))} \<union> set(consInh0 SG es')"
          by (auto simp add: consInhE_def)
        then show "\<exists>e. e \<in> set (a # es') \<and> e \<notin> EsId SG \<and> ety SG e = Some einh \<and> src SG e = Some x 
          \<and> tgt SG e = Some y"
        proof (case_tac "(x, y) \<in> set(consInh0 SG es')")
          assume "(x, y) \<in> set(consInh0 SG es')"
          then show "\<exists>e. e \<in> set (a # es') \<and> e \<notin> EsId SG \<and> ety SG e = Some einh \<and> src SG e = Some x \<and> tgt SG e = Some y"
            using hg hd by (auto)
        next
          from ha hf hb have hh: "a \<in> dom (src SG)"
            by (simp add: is_wf_g_def ftotal_on_def EsI_def)
          from hf hb have hi: "a \<in> dom (tgt SG)"
            by (simp add: is_wf_g_def ftotal_on_def)
          assume "(x, y) \<notin> set(consInh0 SG es')"
          then have "(x, y) \<in> {(the (src SG a), the (tgt SG a))}"
            using hg by simp
          then have "src SG a = Some x \<and> tgt SG a = Some y"
            using hh hi by (simp add: domD)
          then show "\<exists>e. e \<in> set (a # es') \<and> e \<notin> EsId SG \<and> ety SG e = Some einh \<and> src SG e = Some x \<and> tgt SG e = Some y"
            using hf by (auto)
        qed
      next
        assume hf: "\<not>(a \<in> Es SG - EsId SG \<and> ety SG a = Some einh)"
        from he hf have hg: "(x, y) \<in> set(consInh0 SG es')" 
          by (auto simp add: consInhE_def)
        then have "\<exists>e. e \<in> set es' \<and> e \<notin> EsId SG \<and> ety SG e = Some einh \<and> src SG e = Some x \<and> tgt SG e = Some y"
          using hd by simp
        then show "\<exists>e. e \<in> set (a # es') \<and> e \<notin> EsId SG \<and> ety SG e = Some einh \<and> src SG e = Some x \<and> tgt SG e = Some y"
          by (auto)
      qed
    qed
  next
    assume hd: "\<exists>e. e \<in> set es \<and> e \<notin> EsId SG \<and> ety SG e = Some einh \<and> src SG e = Some x \<and> tgt SG e = Some y"
    then show "(x, y) \<in> set(consInh0 SG es)"
    proof (clarify)
      fix a
      assume he: "a \<in> set es"
      assume hf: "ety SG a = Some einh"
      assume hg: "a \<notin> EsId SG"
      assume hh: "src SG a = Some x"
      assume hi: "tgt SG a = Some y"
      from he show "(x, y) \<in> set(consInh0 SG es)"
      proof (induct es, simp)
        fix a' es'
        assume hj: "(a \<in> set es' \<Longrightarrow> (x, y) \<in> set(consInh0 SG es'))"
        assume hk: "a \<in> set (a' # es')"
        show "(x, y) \<in> set(consInh0 SG (a' # es'))"
        proof (simp add: in_consInh0_insertls, case_tac "a=a'")
          assume "a = a'"
          then show "(x, y) \<in> set(consInhE SG a') \<or> (x, y) \<in> set(consInh0 SG es')"
            using ha he hf hg hh hi by (auto simp add: consInhE_def)
        next
          assume hl: "a \<noteq> a'"
          show "(x, y) \<in> set(consInhE SG a') \<or> (x, y) \<in> set(consInh0 SG es')"
          proof (rule disjI2)
            from hk hl have "a \<in> set es'"
              by simp
            then have "(x, y) \<in> set(consInh0 SG es')"
              using hj by simp
            then show "(x, y) \<in> set(consInh0 SG es')"
              by simp
          qed
        qed
      qed
    qed
  qed
        
definition consInh:: "SGr_ls \<Rightarrow> (V\<times>V) list"
where
  "consInh SG \<equiv> consInh0 (toSGr SG) (EsG SG)"

lemma in_consInh: 
  fixes x y
  assumes ha: "is_wf_g (toSGr SGL)"
  shows "(x, y) \<in> set(consInh SGL)  \<longleftrightarrow> 
    (\<exists> e. e \<in> set (EsG SGL) \<and> e \<notin> EsId (toSGr SGL) \<and> ety (toSGr SGL) e = Some einh
      \<and> src (toSGr SGL) e  = Some x \<and> tgt (toSGr SGL) e = Some y)"
    proof -
      have hb: "set (EsG SGL) \<subseteq> Es (toSGr SGL)" 
        by (auto simp add: toSGr_def)
      show ?thesis
      using ha hb by (simp add: consInh_def in_consInh0)
    qed

lemma inh_eq_consInh:
  assumes ha: "is_wf_g (toSGr SGL)" 
  shows "inh (toSGr SGL) = set(consInh SGL)"
  proof
    show "set(consInh SGL) \<subseteq> inh (toSGr SGL)"
    proof (rule subrelI)
      fix x y
      assume "(x, y) \<in> set(consInh SGL)"
      then have "\<exists> e. e \<in> set (EsG SGL) \<and> e \<notin> EsId (toSGr SGL) 
        \<and> ety (toSGr SGL) e = Some einh
        \<and> (src (toSGr SGL))e  = Some x \<and> (tgt (toSGr SGL)) e = Some y" 
        using ha by (simp add: in_consInh)
      then show "(x, y) \<in> inh (toSGr SGL)"
      proof (clarify)
        fix e 
        assume "e \<in> set (EsG SGL)"
        then have hb: "e \<in> Es (toSGr SGL)"
          by (simp add: in_set_EsG)
        assume hc: "ety (toSGr SGL) e = Some einh"
        assume hd: "e \<notin> EsId (toSGr SGL)"
        assume he: "src (toSGr SGL) e = Some x"
        assume hf: "tgt (toSGr SGL) e = Some y"
        show "(x, y) \<in> inh (toSGr SGL)"
        using hb hc hd he hf ha
        by (simp add: inh_def relOfGr_def adjacent_def rst_fun_def restrict_map_def EsId_def
          EsI_def EsTy_def in_set_EsG)(rule exI[where x="e"], 
        auto simp add: is_wf_g_def ftotal_on_def)
      qed
    qed
  next
    show "inh (toSGr SGL) \<subseteq> set(consInh SGL)"
    proof (rule subrelI)
      fix x y
      assume "(x, y) \<in> inh (toSGr SGL)"
      then have "\<exists>e. e \<in> set (EsG SGL) \<and>
        e \<notin> EsId (toSGr SGL) \<and>
        ety (toSGr SGL) e = Some einh \<and>
        src (toSGr SGL) e = Some x \<and> tgt (toSGr SGL) e = Some y"
        using ha by (auto simp add: inh_def relOfGr_def adjacent_def rst_fun_def 
          restrict_map_def EsId_def
          EsI_def EsTy_def is_wf_g_def ftotal_on_def)(rule exI, auto simp add: in_set_EsG)
      then show "(x, y) \<in> set(consInh SGL)"
        using ha by (simp add: in_consInh)
    qed
  qed

definition consClan::"V \<Rightarrow> SGr_ls \<Rightarrow> V list"
where
  "consClan v SGL \<equiv> 
    (let consInh = consInh SGL in
      rtrancl_list_impl (zip(map snd consInh)(map fst consInh)) [v])"

lemma clan_eq_consClan:
  assumes "is_wf_g (toSGr SGL)" 
  shows "clan v (toSGr SGL) = set(consClan v SGL)"
  proof - 
    have h1: "((inh (toSGr SGL))\<^sup>*)\<inverse> = ((inh (toSGr SGL))\<inverse>)\<^sup>*"
      by (simp add: rtrancl_converse)
    from assms show ?thesis
      by (simp add: clan_def consClan_def inhst_def h1 Let_def)
      (simp add: inh_eq_consInh set_list_inv_eq rtrancl_Image_eq)
  qed

(*primrec consSrcStVs::"SGr_ls \<Rightarrow> V list \<Rightarrow> V list" 
where
  "consSrcStVs SGL [] = []" |
  "consSrcStVs SGL (v#vs) = (consClan v SGL)@(consSrcStVs SGL vs)"*)

fun consSrcStE::"SGr_ls \<Rightarrow> E \<Rightarrow> (E\<times>V) list" 
where
  "consSrcStE SGL e = (if e \<in> EsA (toSGr SGL) 
      then map (Pair e) (consClan (the(src (toSGr SGL) e)) SGL)
      else [])"

primrec consSrcSt0::"SGr_ls \<Rightarrow> E list \<Rightarrow> (E\<times>V) list" 
where
  "consSrcSt0 SGL [] = []" |
  "consSrcSt0 SGL (e#es) = (consSrcStE SGL e)@(consSrcSt0 SGL es)"

(*lemma in_consSrcStVs: 
  "v1 \<in> set(consSrcStVs SGL (v # vs)) \<longleftrightarrow> v1 \<in> set(consClan v SGL) \<union> set (consSrcStVs SGL vs)"
  by (simp)*)

(*lemma in_consSrcStE: 
  shows "(e', v) \<in> set(consSrcStE SGL e) \<longleftrightarrow> e' = e"
  proof
    assume "(e', v) \<in> set (consSrcStE SGL e)"
    then show "e' = e"
      by (simp add: image_def)
  next
    assume "e' = e"
    then show "(e', v) \<in> set (consSrcStE SGL e)"
    by (rule ccontr)
  by (simp add: image_def)*)

lemma in_consSrcSt0: 
  "(e', v) \<in> set(consSrcSt0 SGL (e # es)) \<longleftrightarrow> 
    (e', v) \<in> set(consSrcStE SGL e) \<or> (e', v) \<in> set(consSrcSt0 SGL es)"
  by (simp)

lemma in_consSrcSt0_hd: 
  "(e, v) \<in> set(consSrcSt0 SGL (e # es)) \<longleftrightarrow> (e, v) \<in> set(consSrcStE SGL e)"
  by (induct es, auto)

lemma in_consSrcSt0_nothd: 
  assumes "e' \<noteq> e"
  shows "(e', v) \<in> set(consSrcSt0 SGL (e # es)) \<longleftrightarrow> (e', v) \<in> set(consSrcSt0 SGL es)"
  using assms by (induct es, auto)

(*lemma in_consSrcStVs_in_clan:
  "v \<in> set (consSrcStVs SGL [v\<leftarrow>NsG SGL . src (toSGr SGL) a = Some v]) 
  \<longleftrightarrow> v \<in> clan (the(src (toSGr SGL) a)) (toSGr SGL)"
  proof
    assume "v \<in> set (consSrcStVs SGL [v\<leftarrow>NsG SGL . src (toSGr SGL) a = Some v])"
    then have "(let vs = [v\<leftarrow>NsG SGL . src (toSGr SGL) a = Some v] in
      v \<in> set (consSrcStVs SGL vs))" by auto
    then show "v \<in> clan (the (src (toSGr SGL) a)) (toSGr SGL)"
    by (simp)*)

lemma in_consSrcSt0_iff:
  fixes e v es 
  assumes ha: "set es \<subseteq> set(EsG SGL)" and hb: "is_wf_sg (toSGr SGL)" 
  shows "(e, v) \<in> set(consSrcSt0 SGL es) \<longleftrightarrow> 
    (e \<in> set(es) \<and> e \<in> EsA (toSGr SGL) \<and> (\<exists>v2. v \<in> clan v2 (toSGr SGL) \<and> src (toSGr SGL) e = Some v2))"
  proof -
    from hb have hb1: "is_wf_g (toSGr SGL)"
      by (simp add: is_wf_sg_def)
    show ?thesis
    proof
      assume "(e, v) \<in> set (consSrcSt0 SGL es)"
      then show "e \<in> set(es) \<and> e \<in> EsA (toSGr SGL) 
        \<and> (\<exists>v2. v \<in> clan v2 (toSGr SGL) \<and> src (toSGr SGL) e = Some v2)"
      proof (induct es, simp)
        fix a es'
        assume hd: "(e, v) \<in> set (consSrcSt0 SGL es') \<Longrightarrow> e \<in> set es' \<and>
          e \<in> EsA (toSGr SGL) \<and> (\<exists>v2. v \<in> clan v2 (toSGr SGL) \<and> src (toSGr SGL) e = Some v2)"
        and he: "(e, v) \<in> set (consSrcSt0 SGL (a # es')) "
        then show "e \<in> set (a # es') \<and> e \<in> EsA (toSGr SGL) \<and> (\<exists>v2. v \<in> clan v2 (toSGr SGL) \<and> src (toSGr SGL) e = Some v2)"
        proof (case_tac "e=a")
          assume hf: "e=a"
          then have "(a, v) \<in> set(consSrcStE SGL e)"
            using he by (simp only: in_consSrcSt0_hd)
          then show "e \<in> set (a # es') \<and>e \<in> EsA (toSGr SGL) \<and> (\<exists>v2. v \<in> clan v2 (toSGr SGL) \<and> src (toSGr SGL) e = Some v2)"
            using hf hb1 hb in_EsA_in_ES[of "(toSGr SGL)" "a"] by (simp add: image_def )
              (rule exI[where x="the(src (toSGr SGL) a)"], 
                auto simp add: clan_eq_consClan is_wf_g_def ftotal_on_def domD)
        next
          assume hf: "e\<noteq>a"
          then have "(e, v) \<in> set (consSrcSt0 SGL es')"
            using he in_consSrcSt0_nothd by (simp)
          then show "e \<in> set (a # es') \<and> e \<in> EsA (toSGr SGL) 
            \<and> (\<exists>v2. v \<in> clan v2 (toSGr SGL) \<and> src (toSGr SGL) e = Some v2)"
            using hd by simp
        qed
      qed
    next
      assume "e \<in> set es \<and> e \<in> EsA (toSGr SGL) \<and> (\<exists>v2. v \<in> clan v2 (toSGr SGL) \<and> src (toSGr SGL) e = Some v2)"
      then show "(e, v) \<in> set (consSrcSt0 SGL es)"
      proof (clarify)
        fix v2
        assume h1: "e \<in> set es"
        and h2: "e \<in> EsA (toSGr SGL)"
        and h3: "v \<in> clan v2 (toSGr SGL)"
        and h4: "src (toSGr SGL) e = Some v2"
        from h1 show "(e, v) \<in> set (consSrcSt0 SGL es)"
        proof (induct es, simp)
          fix a es
          assume h5: "e \<in> set es \<Longrightarrow> (e, v) \<in> set (consSrcSt0 SGL es)"
            and h6: "e \<in> set (a # es)"
          then show "(e, v) \<in> set (consSrcSt0 SGL (a # es))"
          proof (case_tac "e=a")
            assume "e=a"
            then show "(e, v) \<in> set (consSrcSt0 SGL (a # es))"
              using h2 h3 h4 hb1 by (simp only: in_consSrcSt0_hd)
              (simp add: image_def clan_eq_consClan)
          next
            assume "e\<noteq>a"
            then show "(e, v) \<in> set (consSrcSt0 SGL (a # es))"
              using in_consSrcSt0_nothd h5 h6
              by (simp)
          qed
        qed
      qed
    qed
  qed   

definition consSrcSt:: "SGr_ls \<Rightarrow> (E\<times>V) list"
where
  "consSrcSt SGL \<equiv> consSrcSt0 SGL (EsG SGL)"

lemma in_consSrcSt: 
  fixes e v
  assumes ha: "is_wf_sg (toSGr SGL)"
  shows "(e, v) \<in> set(consSrcSt SGL)  \<longleftrightarrow> 
     (e \<in> EsA (toSGr SGL) \<and> (\<exists>v2. v \<in> clan v2 (toSGr SGL) \<and> src (toSGr SGL) e = Some v2))"
  proof -
      have hb: "set (EsG SGL) \<subseteq> Es (toSGr SGL)" 
        by (simp add: toSGr_def)
      have hc: "e \<in> EsA (toSGr SGL) \<Longrightarrow> e \<in> set (EsG SGL)"
        by (simp add: Fragmenta_SGsL.in_set_EsG ha in_EsA_in_ES)
      show ?thesis
      using ha hb by (auto simp add: consSrcSt_def in_consSrcSt0_iff hc)
  qed

lemma srcst_eq_consSrcSt: 
  assumes ha: "is_wf_sg (toSGr SGL)"
  shows "srcst (toSGr SGL) = set(consSrcSt SGL)"
  using ha by (auto simp add: srcst_def in_consSrcSt)

definition consUSG:: "SGr_ls \<Rightarrow> SGr_ls \<Rightarrow> SGr_ls"
where
  "consUSG SGL1 SGL2 = \<lparr>NsG = (NsG SGL1)@(NsG SGL2), EsG = (EsG SGL1)@(EsG SGL2),
    srcG = (srcG SGL2)@(srcG SGL1), tgtG = (tgtG SGL2)@(tgtG SGL1),
    ntyG = (ntyG SGL2)@(ntyG SGL1), etyG = (etyG SGL2)@(etyG SGL1),
    srcmG = (srcmG SGL2)@(srcmG SGL1), tgtmG = (tgtmG SGL2)@(tgtmG SGL1)\<rparr>"

(*Theorem that shows that they are the same*)
lemma USGEqconsUSG: "(toSGr SGL1) USG (toSGr SGL2) = toSGr (consUSG SGL1 SGL2)"
  proof (simp add: SGr_eq, rule conjI)
    show "Ns (toSGr SGL1 USG toSGr SGL2) = Ns (toSGr (consUSG SGL1 SGL2))"
      by (simp add: toSGr_def cupSG_def consUSG_def)
  next
    apply_end (rule conjI)
    show "Es (toSGr SGL1 USG toSGr SGL2) = Es (toSGr (consUSG SGL1 SGL2))"
      by (simp add: toSGr_def cupSG_def consUSG_def)
  next
    apply_end (rule conjI)
    show "src (toSGr SGL1) ++ src (toSGr SGL2) = src (toSGr (consUSG SGL1 SGL2))"
    by (simp add: toSGr_def cupSG_def consUSG_def)
  next
    apply_end (rule conjI)
    show "tgt (toSGr SGL1) ++ tgt (toSGr SGL2) = tgt (toSGr (consUSG SGL1 SGL2))"
    by (simp add: toSGr_def cupSG_def consUSG_def)
  next
    apply_end (rule conjI)
    show "nty (toSGr SGL1 USG toSGr SGL2) = nty (toSGr (consUSG SGL1 SGL2))"
      by (simp add: toSGr_def cupSG_def consUSG_def)
  next
    apply_end (rule conjI)
    show "ety (toSGr SGL1 USG toSGr SGL2) = ety (toSGr (consUSG SGL1 SGL2))"
     by (simp add: toSGr_def cupSG_def consUSG_def)
  next
    apply_end (rule conjI)
    show "srcm (toSGr SGL1) ++ srcm (toSGr SGL2) = srcm (toSGr (consUSG SGL1 SGL2))"
     by (simp add: toSGr_def cupSG_def consUSG_def)
  next
    show "tgtm (toSGr SGL1 USG toSGr SGL2) = tgtm (toSGr (consUSG SGL1 SGL2))"
     by (simp add: toSGr_def cupSG_def consUSG_def) 
  qed
  
end