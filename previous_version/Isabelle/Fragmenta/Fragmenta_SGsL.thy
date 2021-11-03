(*  Title:      Fragmenta theory of structural graphs (SGs)
    Description: 'Fragmenta' theory presented in the Models 2015 paper.
    Author:     Nuno Amálio
*)
theory Fragmenta_SGsL
imports Fragmenta_SGs Fragmenta_GraphsL "../Extra/Finite_Transitive_Closure_Simprocs" 

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
definition toSGr :: "'a SGr_ls_scheme \<Rightarrow> SGr"
where
  "toSGr SGL \<equiv> \<lparr>Ns = set (NsG SGL), Es = set (EsG SGL), 
    src = map_of (srcG SGL), tgt = map_of (tgtG SGL),
    nty = map_of (ntyG SGL), ety = map_of (etyG SGL), 
    srcm  = map_of (srcmG SGL), tgtm = map_of (tgtmG SGL)\<rparr>"

lemma is_wf_g_toSGr_imp_toGr: "is_wf_g (toSGr SGL) \<Longrightarrow> is_wf_g (toGr SGL)"
  by (simp add: toSGr_def toGr_def is_wf_g_def)

lemma in_set_EsG: "e \<in> set (EsG SGL) \<longleftrightarrow> e \<in> Es (toSGr SGL)"
  by (simp add: toSGr_def)
  
definition is_wf_sgL :: "'a SGr_ls_scheme \<Rightarrow> bool"
where
  "is_wf_sgL SGL \<equiv> is_wf_gL SGL \<and>
    distinct (map fst (ntyG SGL)) \<and> distinct (map fst (etyG SGL)) \<and> 
    distinct (map fst (srcmG SGL)) \<and> distinct (map fst (tgtmG SGL)) \<and> 
    is_wf_sg (toSGr SGL)"

lemma EsTy_eq_ls_exp: 
  assumes "distinct (map fst (etyG SGL))" and "None \<notin> ets"
  shows "EsTy (toSGr SGL) ets = set(map fst [p\<leftarrow>(etyG SGL). snd p \<in> (the ` ets)])"
  proof
    apply_end (rule subsetI)
    fix x
    assume h1: "x \<in> EsTy (toSGr SGL) ets"
    then have h2: "\<exists> y. ety (toSGr SGL) x = y \<and> y \<in> ets" by (simp add: EsTy_def)
    then obtain y where "ety (toSGr SGL) x = y \<and> y \<in> ets" by blast
    then have "\<exists> y. ety (toSGr SGL) x = Some y" using assms(2) by (cases y)auto
    then obtain y where "ety (toSGr SGL) x = Some y" by blast
    then show " x \<in> set (map fst [p\<leftarrow>etyG SGL . snd p \<in> (the ` ets)])"
      using h1 assms(2) by (simp add: toSGr_def EsTy_def image_def)
          (rule exI[where x="y"], simp add: map_of_SomeD, force)
  next
    apply_end (rule subsetI)
    fix x
    have "\<And> y. y \<noteq> None \<Longrightarrow> Some (the y) = y"
      by (simp)
    then have h1: "\<And> y. y \<in> ets \<Longrightarrow> Some (the y) = y" 
      by (smt assms(2))
    assume "x \<in> set (map fst [p\<leftarrow>etyG SGL . snd p \<in> the ` ets])"
    then have "\<exists> y. (x, y) \<in> set (etyG SGL) \<and> Some y \<in> ets" using assms h1 by auto
    then obtain y where "(x, y) \<in> set (etyG SGL) \<and> Some y \<in> ets" by blast
    then have "map_of (etyG SGL) x = Some y \<and> Some y \<in> ets"
      using assms by (simp add: is_wf_sgL_def image_def)
    then show "x \<in> EsTy (toSGr SGL) ets"
      using assms by (auto simp add: EsTy_def toSGr_def image_def)
  qed
     
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

definition EsRL:: "SGr_ls \<Rightarrow> E list"
where
  "EsRL SGL \<equiv> (filter (\<lambda> e. ety (toSGr SGL) e = Some eref) (EsG SGL))"

lemma EsR_eq_EsRL: 
  assumes "ftotal_on (ety (toSGr SGL)) (Es (toSGr SGL)) SGETy_set "
  shows "EsR (toSGr SGL) = set(EsRL SGL)"
  using assms by (simp add: toSGr_def EsRL_def EsR_def EsTy_def vimage_def ftotal_on_def)
    (rule equalityI, rule subsetI, auto)

definition EsAL:: "SGr_ls \<Rightarrow> E list"
where
  "EsAL SGL \<equiv> 
    (filter (\<lambda> e. ety (toSGr SGL) e \<in> {Some ecompbi, Some ecompuni, Some erelbi, Some ereluni, Some elnk}) (EsG SGL))"

lemma EsA_eq_EsAL: 
  assumes "ftotal_on (ety (toSGr SGL)) (Es (toSGr SGL)) SGETy_set "
  shows "EsA (toSGr SGL) = set(EsAL SGL)"
  using assms by (simp add: toSGr_def EsAL_def EsA_def EsTy_def vimage_def ftotal_on_def)
    (rule equalityI, rule subsetI, auto)

definition EsIdL:: "'a Gr_ls_scheme \<Rightarrow> E list"
where
  "EsIdL GL \<equiv> (filter (\<lambda> e. src (toGr GL) e = tgt (toGr GL) e ) (EsG GL))"

lemma EsId_eq_EsIdL: 
  assumes "is_wf_g (toSGr SGL)"
  shows "EsId (toSGr SGL) = set(EsIdL SGL)"
  using assms in_set_EsG by (simp add: toSGr_def toGr_def EsIdL_def EsId_def is_wf_g_def ftotal_on_def)

definition EsRPL:: "SGr_ls \<Rightarrow> E list"
where
  "EsRPL SGL \<equiv> [e\<leftarrow>(EsRL SGL). nty (toSGr SGL) (the (src (toSGr SGL) e)) = Some nprxy]"

lemma EsRP_eq_EsRPL: 
  assumes "is_wf_sg(toSGr SGL)"
  shows "EsRP (toSGr SGL) = set(EsRPL SGL)"
  proof 
    apply_end(rule subsetI)
    fix x
    assume "x \<in> EsRP (toSGr SGL)"
    then show "x \<in> set (EsRPL SGL)"
    using assms by (simp only: EsR_eq_EsRL EsRPL_def EsRP_def is_wf_sg_def)
    (auto simp add: NsP_def NsTy_def)
  next
    apply_end(rule subsetI)
    fix x
    assume h1: "x \<in> set (EsRPL SGL)"
    hence "x \<in> (EsR (toSGr SGL))" 
      using assms by (simp add: EsRPL_def EsR_eq_EsRL is_wf_sg_def)
    hence "x \<in> Es (toSGr SGL)"
      using assms by (simp add: in_EsR_in_Es)
    hence "\<exists> y. src (toSGr SGL) x = Some y"
      using assms by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def domD)
    then show "x \<in> EsRP (toSGr SGL)"
      using assms h1 by (simp only: EsR_eq_EsRL EsRPL_def EsRP_def is_wf_sg_def)
      (auto simp add: NsP_def NsTy_def)
  qed

definition consInhSt::"V \<Rightarrow> SGr_ls \<Rightarrow> V list"
where
  "consInhSt v SGL \<equiv> 
    (let consInh = consInh SGL in
      rtrancl_list_impl (consInh) [v])"

lemma inhst_eq_consInhSt:
  assumes "is_wf_g (toSGr SGL)" 
  shows "(v1, v2) \<in> inhst (toSGr SGL) = (v2 \<in> set(consInhSt v1 SGL))"
proof
  assume "(v1, v2) \<in> inhst (toSGr SGL)"
  hence "v2 \<in> (inh (toSGr SGL))\<^sup>* `` {v1}" 
    by (auto simp only: inhst_def)
  then show "v2 \<in> set (consInhSt v1 SGL)"
    using assms consInhSt_def inh_eq_consInh rtrancl_Image_eq by fastforce
next
  assume "v2 \<in> set (consInhSt v1 SGL)"
  then show "(v1, v2) \<in> inhst (toSGr SGL)" 
    by (metis Image_singleton_iff assms consInhSt_def inh_eq_consInh inhst_def list.set(1) 
        list.simps(15) rtrancl_Image_eq)
      (*using assms by (simp only: consInhSt_def inhst_def Let_def)(simp add: inh_eq_consInh rtrancl_Image_eq)*)
      (*by (simp add: h2 consInhSt_def Let_def, simp only: inhst_def inh_eq_consInh rtrancl_Image_eq)
      by (simp add: consInhSt_def h1 Let_def)*)
       (* (simp add: inh_eq_consInh rtrancl_Image_eq)*)
  qed


definition consInhStInv::"V \<Rightarrow> SGr_ls \<Rightarrow> V list"
where
  "consInhStInv v SGL \<equiv> 
    (let consInh = consInh SGL in
      rtrancl_list_impl (zip(map snd consInh)(map fst consInh)) [v])"

lemma inhstinv_eq_consInhSt:
  assumes "is_wf_g (toSGr SGL)" 
  shows "(v1, v2) \<in> (inhst (toSGr SGL))\<inverse> = (v1 \<in> set(consInhSt v2 SGL))"
proof
  assume "(v1, v2) \<in> (inhst (toSGr SGL))\<inverse>"
  hence "(v2, v1) \<in> (inhst (toSGr SGL))" by auto
  then show "v1 \<in> set (consInhSt v2 SGL)" using assms by (simp only: inhst_eq_consInhSt) 
next
  assume "v1 \<in> set (consInhSt v2 SGL)"
  then show "(v1, v2) \<in> (inhst (toSGr SGL))\<inverse>" using assms by (simp add: inhst_eq_consInhSt)
qed

lemma inhstinv_eq_consInhStInv:
  assumes "is_wf_g (toSGr SGL)" 
  shows "(v1, v2) \<in> (inhst (toSGr SGL))\<inverse> = (v2 \<in> set(consInhStInv v1 SGL))"
proof 
  assume "(v1, v2) \<in> (inhst (toSGr SGL))\<inverse>"
  hence "v2 \<in> ((inh (toSGr SGL))\<^sup>*)\<inverse> `` {v1}" 
    by (auto simp only: inhst_def)
  then show "v2 \<in> set (consInhStInv v1 SGL)"
    by (metis assms consInhStInv_def empty_set inh_eq_consInh inhst_def_simp list.simps(15) 
      rtrancl_Image_eq set_list_inv_eq)
next
  assume "v2 \<in> set (consInhStInv v1 SGL)"
  then show "(v1, v2) \<in> (inhst (toSGr SGL))\<inverse>"
    by (metis Image_singleton_iff assms consInhStInv_def empty_set inh_eq_consInh inhst_def 
       inhst_def_simp list.simps(15) rtrancl_Image_eq set_list_inv_eq)
qed

lemma inhst_im_eq_consInhSt:
  assumes "is_wf_g (toSGr SGL)" 
  shows "(inhst (toSGr SGL))``{v1} = set(consInhSt v1 SGL)"
  using assms inhst_eq_consInhSt by auto

(*definition consInhStV::"SGr_ls \<Rightarrow> V \<Rightarrow> (V\<times>V) list"
where
  "consInhStV SGL v \<equiv> 
    (let consInh = consInh SGL in
      map (Pair v) (rtrancl_list_impl (consInh) [v]))"

lemma consInstV_eq_ConsInhSt:
  assumes "is_wf_g (toSGr SGL)" 
  shows "(v1, v2) \<in> set (consInhStV SGL v1) = (v2 \<in> set(consInhSt v1 SGL))"
  using assms by (auto simp add: consInhStV_def inh_eq_consInh inhst_def consInhSt_def)

lemma inhst_eq_consInhStV:
  assumes "is_wf_g (toSGr SGL)" 
  shows "(v1, v2) \<in> inhst (toSGr SGL) = ((v1, v2) \<in> set(consInhStV SGL v1))"
proof
  assume "(v1, v2) \<in> inhst (toSGr SGL)"
  hence "v2 \<in> (inh (toSGr SGL))\<^sup>* `` {v1}" 
    by (auto simp only: inhst_def)
  then show "(v1, v2) \<in> set (consInhStV SGL v1)"
    using assms consInhStV_def inh_eq_consInh rtrancl_Image_eq by fastforce
next
  assume "(v1, v2) \<in> set (consInhStV SGL v1)"
  hence "v2 \<in> set(consInhSt v1 SGL)" using assms by (simp only: consInstV_eq_ConsInhSt)
  then show "(v1, v2) \<in> inhst (toSGr SGL)"
    using assms by (simp add: inhst_eq_consInhSt)
qed*)

(*primrec consInhStW0:: "V list \<Rightarrow> SGr_ls \<Rightarrow> (V\<times>V) list"
where
  "consInhStW0 [] SGL = []" |
  "consInhStW0 (v#vs) SGL = (consInhStV SGL v)@(consInhStW0 vs SGL)"

lemma in_consInhStW0_hd:
  shows "(x, y) \<in> set(consInhStW0 (x # vs) SGL) = ((x, y) \<in> set(consInhStV SGL x))"
  by (induct vs) (auto simp add: consInhStV_def)

lemma in_consInhStW0_nothd: 
  assumes "x \<noteq> v"
  shows "(x, y) \<in> set(consInhStW0 (v # vs) SGL) = ((x, y) \<in> set(consInhStW0 vs SGL))"
  using assms by (auto simp add: consInhStV_def) *)

(*lemma in_consInhStW0:
  assumes "x \<in> set(vs)"
  shows "(x, y) \<in> set (consInhStW0 vs SGL) = ((x, y) \<in> set(consInhStV SGL x))"
proof
  assume "(x, y) \<in> set (consInhStW0 vs SGL)"
  then show "(x, y) \<in> set (consInhStV SGL x)"
  proof (induct vs)
    assume "(x, y) \<in> set (consInhStW0 [] SGL)"
    then show "(x, y) \<in> set (consInhStV SGL x)" by auto
  next
    fix v vs
    assume h: "(x, y) \<in> set (consInhStW0 vs SGL) \<Longrightarrow> (x, y) \<in> set (consInhStV SGL x)"
    assume "(x, y) \<in> set (consInhStW0 (v # vs) SGL)"
    hence "(x, y) \<in> set (consInhStV SGL v) \<or> (x, y) \<in> set (consInhStW0 vs SGL)" by auto
    then show "(x, y) \<in> set (consInhStV SGL x)" 
    proof
      assume "(x, y) \<in> set (consInhStV SGL v)"
      then show "(x, y) \<in> set (consInhStV SGL x)" 
        by (auto simp add: consInhStV_def)
    next
      assume "(x, y) \<in> set (consInhStW0 vs SGL)"
      then show "(x, y) \<in> set (consInhStV SGL x)" 
        using h by auto
    qed
  qed
next
  assume "(x, y) \<in> set (consInhStV SGL x)"
  hence "(x, y) \<in> set (consInhStV SGL x) \<and> x \<in> set(vs)" using assms by auto
  then show "(x, y) \<in> set (consInhStW0 vs SGL)"
  proof (induct vs) 
    case Nil
    then show ?case by auto
  next
    fix v vs
    assume h: "(x, y) \<in> set (consInhStV SGL x) \<and> x \<in> set vs \<Longrightarrow> (x, y) \<in> set (consInhStW0 vs SGL)"
    assume "(x, y) \<in> set (consInhStV SGL x) \<and> x \<in> set (v # vs)"
    then show "(x, y) \<in> set (consInhStW0 (v # vs) SGL)" 
      using h by auto
  qed
qed*)
    
(*definition consInhStW::"SGr_ls \<Rightarrow> (V\<times>V) list"
where
  "consInhStW SGL \<equiv> 
    (let consInh = consInh SGL in
       remdups(consInhStW0 (map fst consInh) SGL))"

lemma consInhStV_in_consInhStW:
  assumes "(x, y) \<in> set (consInhStV SGL x)" and "is_wf_g (toSGr SGL)"  and "inh (toSGr SGL) \<noteq> {}"
  shows "(x, y) \<in> set(consInhStW SGL)"
proof (simp add: consInhStW_def, cases "map fst (consInh SGL)") 
  assume "map fst (consInh SGL) = []"
  hence "{} = set (consInh SGL)" by auto
  hence "{} = inh (toSGr SGL)" using assms(2) by (simp add: inh_eq_consInh)
  then show "(x, y) \<in> set (consInhStW0 (map fst (consInh SGL)) SGL)"
    using assms(3) by auto
next
  fix v vs
  assume h1: "map fst (consInh SGL) = v#vs"
  show "(x, y) \<in> set (consInhStW0 (map fst (consInh SGL)) SGL)"
  proof (case_tac "x = v")
    assume "x = v"
    then show "(x, y) \<in> set (consInhStW0 (map fst (consInh SGL)) SGL)"
      using h1 assms(1) by (simp only: in_consInhStW0_hd)
  next
    assume "x \<noteq> v"
    hence "(x, y) \<in> set (consInhStW0 (v#vs) SGL)"
    proof (induct vs)
      case Nil
      then show ?case by simp
      
    then show "(x, y) \<in> set (consInhStW0 (map fst (consInh SGL)) SGL)"
      using in_consInhStW0_nothd[where x="x" and y="y" and v="v" and vs="vs" and SGL="SGL"] 
      using h2 h1 by (simp )
  qed
qed

lemma inhst_eq_consInhStW:
  assumes "is_wf_g (toSGr SGL)"  and "inh (toSGr SGL) \<noteq> {}"
  shows "inhst (toSGr SGL) = set(consInhStW SGL)"
proof
  show "inhst (toSGr SGL) \<subseteq> set (consInhStW SGL)"
  proof (rule subrelI)
    fix x y
    assume h: "(x, y) \<in> inhst (toSGr SGL)"
    show "(x, y) \<in> set (consInhStW SGL)"
    proof (simp add: consInhStW_def, induct "map fst (consInh SGL)")
      assume "[] = map fst (consInh SGL)"
      then show "(x, y) \<in> set (consInhStW0 (map fst (consInh SGL)) SGL)"
        using h assms by (auto simp add: inhst_eq_consInhSt consInhSt_def rtrancl_list_impl inh_eq_consInh)
    next
      fix v vs
      assume h1: "vs = map fst (consInh SGL) \<Longrightarrow> (x, y) \<in> set (consInhStW0 (map fst (consInh SGL)) SGL)"
      assume "v # vs  = map fst (consInh SGL)"
      hence h2: "map fst (consInh SGL) = v # vs" by auto
      from h have h3: "(x, y) \<in> set (consInhStV SGL x)" 
        using assms(1) by (simp add: inhst_eq_consInhStV)
      show "(x, y) \<in> set (consInhStW0 (map fst (consInh SGL)) SGL)" 
      proof (case_tac "x=v")
        assume "x=v"
        then show "(x, y) \<in> set (consInhStW0 (map fst (consInh SGL)) SGL)" 
          using assms(1) h h2 by (simp add: in_consInhStW0 inhst_eq_consInhStV)
      next
        assume "x\<noteq>v"
        hence "(x, y) \<in> set (consInhStW0 (map fst (consInh SGL)) SGL) = ((x, y) \<in> set (consInhStW0 vs SGL))"
          using h2 in_consInhStW0_nothd by auto
        then show "(x, y) \<in> set (consInhStW0 (map fst (consInh SGL)) SGL)" 
          using h3 by (simp add: h1 h2)
    qed*)

lemma inhstinv_im_eq_consInhStInv:
  assumes "is_wf_g (toSGr SGL)" 
  shows "(inhst (toSGr SGL))\<inverse> `` {v1} = set(consInhStInv v1 SGL)"
  using assms inhstinv_eq_consInhStInv by auto

fun consSrcStE::"SGr_ls \<Rightarrow> E \<Rightarrow> (E\<times>V) list" 
where
  "consSrcStE SGL e = (if e \<in> set (EsAL SGL)  
      then map (Pair e) (consInhStInv (the(src (toSGr SGL) e)) SGL)
      else [])"

fun consTgtStE::"SGr_ls \<Rightarrow> E \<Rightarrow> (E\<times>V) list" 
where
  "consTgtStE SGL e = (if e \<in> set (EsAL SGL)  
      then map (Pair e) (consInhStInv (the(tgt (toSGr SGL) e)) SGL)
      else [])"

primrec consSrcSt0::"SGr_ls \<Rightarrow> E list \<Rightarrow> (E\<times>V) list" 
where
  "consSrcSt0 SGL [] = []" |
  "consSrcSt0 SGL (e#es) = (consSrcStE SGL e)@(consSrcSt0 SGL es)"

primrec consTgtSt0::"SGr_ls \<Rightarrow> E list \<Rightarrow> (E\<times>V) list" 
where
  "consTgtSt0 SGL [] = []" |
  "consTgtSt0 SGL (e#es) = (consTgtStE SGL e)@(consTgtSt0 SGL es)"

lemma in_consSrcSt0: 
  "(e', v) \<in> set(consSrcSt0 SGL (e # es)) \<longleftrightarrow> 
    (e', v) \<in> set(consSrcStE SGL e) \<or> (e', v) \<in> set(consSrcSt0 SGL es)"
  by (simp)

lemma in_consTgtSt0: 
  "(e', v) \<in> set(consTgtSt0 SGL (e # es)) \<longleftrightarrow> 
    (e', v) \<in> set(consTgtStE SGL e) \<or> (e', v) \<in> set(consTgtSt0 SGL es)"
  by (simp)

lemma in_consSrcSt0_hd: 
  "(e, v) \<in> set(consSrcSt0 SGL (e # es)) \<longleftrightarrow> (e, v) \<in> set(consSrcStE SGL e)"
  by (induct es, auto)

lemma in_consTgtSt0_hd: 
  "(e, v) \<in> set(consTgtSt0 SGL (e # es)) \<longleftrightarrow> (e, v) \<in> set(consTgtStE SGL e)"
  by (induct es, auto)

lemma in_consSrcSt0_nothd: 
  assumes "e' \<noteq> e"
  shows "(e', v) \<in> set(consSrcSt0 SGL (e # es)) \<longleftrightarrow> (e', v) \<in> set(consSrcSt0 SGL es)"
  using assms by (induct es, auto)

lemma in_consTgtSt0_nothd: 
  assumes "e' \<noteq> e"
  shows "(e', v) \<in> set(consTgtSt0 SGL (e # es)) \<longleftrightarrow> (e', v) \<in> set(consTgtSt0 SGL es)"
  using assms by (induct es, auto)

lemma in_consSrcSt0_iff:
  fixes e v es 
  assumes ha: "set es \<subseteq> set(EsG SGL)" and hb: "is_wf_sg (toSGr SGL)" 
  shows "(e, v) \<in> set(consSrcSt0 SGL es) \<longleftrightarrow> 
    e \<in> set(es) \<and> (e, v) \<in> EsA (toSGr SGL) \<lhd> pfunToRel(src (toSGr SGL)) O (inhst (toSGr SGL))\<inverse>"
  proof -
    from hb have hb1: "is_wf_g (toSGr SGL)"
      by (simp add: is_wf_sg_def)
    show ?thesis
    proof
      assume "(e, v) \<in> set (consSrcSt0 SGL es)"
      then show "e \<in> set(es) \<and> (e, v) \<in> EsA (toSGr SGL) \<lhd> pfunToRel (src (toSGr SGL)) O (inhst (toSGr SGL))\<inverse>"
      proof (induct es, simp)
        fix a es'
        assume hd: "(e, v) \<in> set (consSrcSt0 SGL es') \<Longrightarrow> 
          e \<in> set(es') \<and> (e, v) \<in> EsA (toSGr SGL) \<lhd> pfunToRel(src (toSGr SGL)) O (inhst (toSGr SGL))\<inverse>"
        and he: "(e, v) \<in> set (consSrcSt0 SGL (a # es')) "
        then show "e \<in> set (a # es') \<and> (e, v) \<in> EsA (toSGr SGL) \<lhd> pfunToRel(src (toSGr SGL)) O (inhst (toSGr SGL))\<inverse>"
        proof (case_tac "e=a")
          assume hf: "e=a"
          hence "(a, v) \<in> set(consSrcStE SGL e)"
            using he by (simp only: in_consSrcSt0_hd)
          then show "e \<in> set (a # es') \<and>(e, v) \<in> EsA (toSGr SGL) \<lhd> pfunToRel(src (toSGr SGL)) O (inhst (toSGr SGL))\<inverse>"
            using hf hb1 hb in_EsA_in_ES[of "(toSGr SGL)" "a"] 
            by (simp only: image_def relcomp_unfold inhstinv_eq_consInhStInv dres_def pfunToRel_def, simp)
              (rule exI[where x="the(src (toSGr SGL) a)"], auto simp add: is_wf_g_def is_wf_sg_def ftotal_on_def domD EsA_eq_EsAL)
        next
          assume hf: "e\<noteq>a"
          then have "(e, v) \<in> set (consSrcSt0 SGL es')"
            using he in_consSrcSt0_nothd by (simp)
          then show "e \<in> set (a # es') \<and> (e, v) \<in> EsA (toSGr SGL) \<lhd> pfunToRel (src (toSGr SGL)) O (inhst (toSGr SGL))\<inverse>"
            using hd by simp
        qed
      qed
    next
      assume "e \<in> set es \<and>(e, v) \<in> EsA (toSGr SGL) \<lhd> pfunToRel (src (toSGr SGL)) O (inhst (toSGr SGL))\<inverse>"
      then show "(e, v) \<in> set (consSrcSt0 SGL es)"
      proof (clarify)
        fix v2
        assume h1: "e \<in> set es"
        and h2: "(e, v2) \<in> EsA (toSGr SGL) \<lhd> pfunToRel (src (toSGr SGL))"
        and h3: "(v, v2) \<in> inhst (toSGr SGL)"
        from h2 have h4: "e \<in> EsA (toSGr SGL)" by (simp add: dres_def)
        from h2 have h5: "src (toSGr SGL) e = Some v2" by (simp add: dres_def pfunToRel_def)  
        from h3 have h3a: "(v2, v) \<in> (inhst (toSGr SGL))\<inverse>" by auto
        from h1 show "(e, v) \<in> set (consSrcSt0 SGL es)"
        proof (induct es, simp)
          fix a es
          assume h6: "e \<in> set es \<Longrightarrow> (e, v) \<in> set (consSrcSt0 SGL es)"
            and h7: "e \<in> set (a # es)"
          then show "(e, v) \<in> set (consSrcSt0 SGL (a # es))"
          proof (case_tac "e=a")
            assume "e=a"
            then show "(e, v) \<in> set (consSrcSt0 SGL (a # es))"
              using h5 h2 h3a h4 hb 
              by (simp only: in_consSrcSt0_hd inhstinv_eq_consInhStInv is_wf_sg_def EsA_eq_EsAL)(auto)
          next
            assume "e\<noteq>a"
            then show "(e, v) \<in> set (consSrcSt0 SGL (a # es))"
              using in_consSrcSt0_nothd h5 h6 h7
              by (auto)
          qed
        qed
      qed
    qed
  qed   

lemma in_consTgtSt0_iff:
  fixes e v es 
  assumes ha: "set es \<subseteq> set(EsG SGL)" and hb: "is_wf_sg (toSGr SGL)" 
  shows "(e, v) \<in> set(consTgtSt0 SGL es) \<longleftrightarrow> 
    e \<in> set(es) \<and> (e, v) \<in> EsA (toSGr SGL) \<lhd> pfunToRel(tgt (toSGr SGL)) O (inhst (toSGr SGL))\<inverse>"
  proof -
    from hb have hb1: "is_wf_g (toSGr SGL)"
      by (simp add: is_wf_sg_def)
    show ?thesis
    proof
      assume "(e, v) \<in> set (consTgtSt0 SGL es)"
      then show "e \<in> set(es) \<and> (e, v) \<in> EsA (toSGr SGL) \<lhd> pfunToRel (tgt (toSGr SGL)) O (inhst (toSGr SGL))\<inverse>"
      proof (induct es, simp)
        fix a es'
        assume hd: "(e, v) \<in> set (consTgtSt0 SGL es') \<Longrightarrow> 
          e \<in> set(es') \<and> (e, v) \<in> EsA (toSGr SGL) \<lhd> pfunToRel(tgt (toSGr SGL)) O (inhst (toSGr SGL))\<inverse>"
        and he: "(e, v) \<in> set (consTgtSt0 SGL (a # es')) "
        then show "e \<in> set (a # es') \<and> (e, v) \<in> EsA (toSGr SGL) \<lhd> pfunToRel(tgt (toSGr SGL)) O (inhst (toSGr SGL))\<inverse>"
        proof (case_tac "e=a")
          assume hf: "e=a"
          hence "(a, v) \<in> set(consTgtStE SGL e)"
            using he by (simp only: in_consTgtSt0_hd)
          then show "e \<in> set (a # es') \<and>(e, v) \<in> EsA (toSGr SGL) \<lhd> pfunToRel(tgt (toSGr SGL)) O (inhst (toSGr SGL))\<inverse>"
            using hf hb1 hb in_EsA_in_ES[of "(toSGr SGL)" "a"] 
            by (simp only: image_def relcomp_unfold inhstinv_eq_consInhStInv dres_def pfunToRel_def, simp)
              (rule exI[where x="the(tgt (toSGr SGL) a)"], auto simp add: is_wf_g_def is_wf_sg_def ftotal_on_def domD EsA_eq_EsAL)
        next
          assume hf: "e\<noteq>a"
          then have "(e, v) \<in> set (consTgtSt0 SGL es')"
            using he in_consTgtSt0_nothd by (simp)
          then show "e \<in> set (a # es') \<and> (e, v) \<in> EsA (toSGr SGL) \<lhd> pfunToRel (tgt (toSGr SGL)) O (inhst (toSGr SGL))\<inverse>"
            using hd by simp
        qed
      qed
    next
      assume "e \<in> set es \<and>(e, v) \<in> EsA (toSGr SGL) \<lhd> pfunToRel (tgt (toSGr SGL)) O (inhst (toSGr SGL))\<inverse>"
      then show "(e, v) \<in> set (consTgtSt0 SGL es)"
      proof (clarify)
        fix v2
        assume h1: "e \<in> set es"
        and h2: "(e, v2) \<in> EsA (toSGr SGL) \<lhd> pfunToRel (tgt (toSGr SGL))"
        and h3: "(v, v2) \<in> inhst (toSGr SGL)"
        from h2 have h4: "e \<in> EsA (toSGr SGL)" by (simp add: dres_def)
        from h2 have h5: "tgt (toSGr SGL) e = Some v2" by (simp add: dres_def pfunToRel_def)  
        from h3 have h3a: "(v2, v) \<in> (inhst (toSGr SGL))\<inverse>" by auto
        from h1 show "(e, v) \<in> set (consTgtSt0 SGL es)"
        proof (induct es, simp)
          fix a es
          assume h6: "e \<in> set es \<Longrightarrow> (e, v) \<in> set (consTgtSt0 SGL es)"
            and h7: "e \<in> set (a # es)"
          then show "(e, v) \<in> set (consTgtSt0 SGL (a # es))"
          proof (case_tac "e=a")
            assume "e=a"
            then show "(e, v) \<in> set (consTgtSt0 SGL (a # es))"
              using h5 h2 h3a h4 hb 
              by (simp only: in_consSrcSt0_hd inhstinv_eq_consInhStInv is_wf_sg_def EsA_eq_EsAL)(auto)
          next
            assume "e\<noteq>a"
            then show "(e, v) \<in> set (consTgtSt0 SGL (a # es))"
              using in_consTgtSt0_nothd h5 h6 h7
              by (auto)
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
     (e \<in> EsA (toSGr SGL) \<and> (\<exists>v2. (v, v2) \<in> inhst (toSGr SGL) \<and> src (toSGr SGL) e = Some v2))"
  proof -
      have hb: "set (EsG SGL) \<subseteq> Es (toSGr SGL)" 
        by (simp add: toSGr_def)
      have hc: "e \<in> EsA (toSGr SGL) \<Longrightarrow> e \<in> set (EsG SGL)"
        by (simp add: Fragmenta_SGsL.in_set_EsG ha in_EsA_in_ES)
      show ?thesis
      using ha hb by (auto simp add: consSrcSt_def in_consSrcSt0_iff hc dres_def pfunToRel_def)
  qed

lemma srcst_eq_consSrcSt: 
  assumes "is_wf_sg (toSGr SGL)"
  shows "srcst (toSGr SGL) = set(consSrcSt SGL)"
  using assms by (auto simp add: srcst_def in_consSrcSt dres_def pfunToRel_def inhst_def)

definition consTgtSt:: "SGr_ls \<Rightarrow> (E\<times>V) list"
where
  "consTgtSt SGL \<equiv> consTgtSt0 SGL (EsG SGL)"

lemma in_consTgtSt: 
  fixes e v
  assumes ha: "is_wf_sg (toSGr SGL)"
  shows "(e, v) \<in> set(consTgtSt SGL)  \<longleftrightarrow> 
     (e \<in> EsA (toSGr SGL) \<and> (\<exists>v2. (v, v2) \<in> inhst (toSGr SGL) \<and> tgt (toSGr SGL) e = Some v2))"
  proof -
      have hb: "set (EsG SGL) \<subseteq> Es (toSGr SGL)" 
        by (simp add: toSGr_def)
      have hc: "e \<in> EsA (toSGr SGL) \<Longrightarrow> e \<in> set (EsG SGL)"
        by (simp add: Fragmenta_SGsL.in_set_EsG ha in_EsA_in_ES)
      show ?thesis
      using ha hb by (auto simp add: consTgtSt_def in_consTgtSt0_iff hc dres_def pfunToRel_def)
  qed

lemma tgtst_eq_consTgtSt: 
  assumes "is_wf_sg (toSGr SGL)"
  shows "tgtst (toSGr SGL) = set(consTgtSt SGL)"
  using assms by (auto simp add: tgtst_def in_consTgtSt dres_def pfunToRel_def inhst_def)

definition consInhStCompMorphPair::"SGr_ls \<Rightarrow> (V\<times>V) \<Rightarrow> (V\<times>V) list"
where
  "consInhStCompMorphPair SGL p = (map (Pair (snd p)) (consInhStInv (fst p)  SGL))"

lemma consInhStCompMorphPair_eq:
  assumes "is_wf_g (toSGr SGL)" 
  shows "set(consInhStCompMorphPair SGL p) = {(snd p, fst p)} O (inhst (toSGr SGL))\<inverse>"
  using assms consInhStCompMorphPair_def inhstinv_eq_consInhStInv by auto

primrec consInhStCompMorph0::"SGr_ls \<Rightarrow> (V\<times>V) list \<Rightarrow> (V\<times>V) list"
where
  "consInhStCompMorph0 SGL [] = []" | 
  "consInhStCompMorph0 SGL (p#ps) = 
    (consInhStCompMorphPair SGL p)@(consInhStCompMorph0 SGL ps)"

definition consInhStCompMorph::"SGr_ls \<Rightarrow> (V\<times>V) list \<Rightarrow> (V\<times>V) list"
where
  "consInhStCompMorph SGL rl = invert (consInhStCompMorph0 SGL rl)"

lemma in_consInhStCompMorph_insert_eq:
  "set (consInhStCompMorph SGL (p # rl)) = set(invert (consInhStCompMorphPair SGL p)) \<union> set (consInhStCompMorph SGL rl)"
proof
  show "set (consInhStCompMorph SGL (p # rl)) \<subseteq> set (invert (consInhStCompMorphPair SGL p)) \<union> set (consInhStCompMorph SGL rl)"
  proof (rule subrelI)
    fix x y
    assume "(x, y) \<in> set (consInhStCompMorph SGL (p # rl))"
    hence "(y, x) \<in> set (consInhStCompMorph0 SGL (p # rl))" 
      using consInhStCompMorph_def in_invert by fastforce
    hence "(y, x) \<in> set (consInhStCompMorphPair SGL p) \<or> (y, x) \<in> set (consInhStCompMorph0 SGL rl)" 
      by simp
    then show "(x, y) \<in> set (invert (consInhStCompMorphPair SGL p)) \<union> set (consInhStCompMorph SGL rl)"
      using consInhStCompMorph_def in_invert by fastforce
  qed
next
  show "set (invert (consInhStCompMorphPair SGL p)) \<union> set (consInhStCompMorph SGL rl) \<subseteq> set (consInhStCompMorph SGL (p # rl))"
  using consInhStCompMorph_def by auto
qed

lemma consInhStCompMorph_is_eq:
  assumes "is_wf_g (toSGr SGL)" 
  shows "set(consInhStCompMorph SGL rl) = inhst (toSGr SGL) O set(rl)"
proof
  show "set (consInhStCompMorph SGL rl) \<subseteq> inhst (toSGr SGL) O set rl"
  proof (rule subrelI)
    fix x y
    assume "(x, y) \<in> set (consInhStCompMorph SGL rl)"
    hence "(y, x) \<in> set (consInhStCompMorph0 SGL rl)" 
      using in_invert consInhStCompMorph_def by force
    then show "(x, y) \<in> inhst (toSGr SGL) O set rl"
    proof (induct rl)
      case Nil
      then show ?case by auto
    next
      fix p rl 
      assume h1: "(y, x) \<in> set (consInhStCompMorph0 SGL rl) \<Longrightarrow> (x, y) \<in> inhst (toSGr SGL) O set rl"
      assume "(y, x) \<in> set (consInhStCompMorph0 SGL (p # rl))"
      hence h2: "(y, x) \<in> set(consInhStCompMorphPair SGL p)\<union>set(consInhStCompMorph0 SGL rl)"
        by simp
      hence "(y, x) \<in> {(snd p, fst p)} O (inhst (toSGr SGL))\<inverse> \<or> (y, x) \<in> set(consInhStCompMorph0 SGL rl)"
        by (simp add: assms consInhStCompMorphPair_eq)
      then show "(x, y) \<in> inhst (toSGr SGL) O set (p # rl)"
      proof
        assume "(y, x) \<in> {(snd p, fst p)} O (inhst (toSGr SGL))\<inverse>"
        then show "(x, y) \<in> inhst (toSGr SGL) O set (p # rl)"
          using relcomp.relcompI by auto
      next
        assume "(y, x) \<in> set (consInhStCompMorph0 SGL rl)"
        then show "(x, y) \<in> inhst (toSGr SGL) O set (p # rl)"
          using h1 by auto
      qed
    qed
  qed
next
  show "inhst (toSGr SGL) O set rl \<subseteq> set (consInhStCompMorph SGL rl)"
  proof (rule subrelI)
    fix x y 
    assume "(x, y) \<in> inhst (toSGr SGL) O set rl"
    then show "(x, y) \<in> set (consInhStCompMorph SGL rl)"
    proof (induct rl)
      case Nil
      then show ?case by auto
    next
      fix p rl
      assume h1: "(x, y) \<in> inhst (toSGr SGL) O set rl \<Longrightarrow> (x, y) \<in> set (consInhStCompMorph SGL rl)"
      assume "(x, y) \<in> inhst (toSGr SGL) O set (p # rl)"
      hence "(x, y) \<in> inhst (toSGr SGL) O {p} \<or> (x, y) \<in> inhst (toSGr SGL) O set (rl)"
        by auto
      then show "(x, y) \<in> set (consInhStCompMorph SGL (p # rl))"
      proof
        assume "(x, y) \<in> inhst (toSGr SGL)O {p}"
        hence "(y, x) \<in> {(snd p, fst p)} O (inhst (toSGr SGL))\<inverse>" by auto
        hence "(y, x) \<in> set(consInhStCompMorphPair SGL p)" 
          by (simp add: assms consInhStCompMorphPair_eq)
        hence "(y, x) \<in> set(consInhStCompMorph0 SGL (p # rl))" by simp
        then show "(x, y) \<in> set (consInhStCompMorph SGL (p # rl))"
          using in_invert consInhStCompMorph_def by force
      next
        assume "(x, y) \<in> inhst (toSGr SGL) O set rl"
        then show "(x, y) \<in> set (consInhStCompMorph SGL (p # rl))"
          using h1 by (auto simp only: in_consInhStCompMorph_insert_eq)
      qed
    qed
  qed
qed

definition consMorphCompInhStPair::"SGr_ls \<Rightarrow> (V\<times>V) \<Rightarrow> (V\<times>V) list"
where
  "consMorphCompInhStPair SGL p = (map (Pair (fst p)) (consInhSt (snd p)  SGL))"

lemma consMorphCompInhStPair_eq:
  assumes "is_wf_g (toSGr SGL)" 
  shows "set(consMorphCompInhStPair SGL p) = {p} O inhst (toSGr SGL)"
proof
  show "set (consMorphCompInhStPair SGL p) \<subseteq> {p} O inhst (toSGr SGL)"
  proof (rule subrelI)
    fix x y
    assume "(x, y) \<in> set (consMorphCompInhStPair SGL p)"
    hence "x = fst p \<and> y \<in> set(consInhSt (snd p) SGL)"
      by (auto simp add: consMorphCompInhStPair_def) 
    hence "x = fst p \<and> (snd p, y) \<in> inhst (toSGr SGL)"
      using assms by (simp add: inhst_eq_consInhSt)
    then show "(x, y) \<in> {p} O inhst (toSGr SGL)"
      by force
  qed
next
  show "{p} O inhst (toSGr SGL) \<subseteq> set (consMorphCompInhStPair SGL p)"
    using assms by (auto simp add: consMorphCompInhStPair_def inhst_eq_consInhSt)
qed

primrec consMorphCompInhSt0::"SGr_ls \<Rightarrow> (V\<times>V) list \<Rightarrow> (V\<times>V) list"
where
  "consMorphCompInhSt0 SGL [] = []" | 
  "consMorphCompInhSt0 SGL (p#ps) = 
    (consMorphCompInhStPair SGL p)@(consMorphCompInhSt0 SGL ps)"

definition consMorphCompInhSt::"SGr_ls \<Rightarrow> (V\<times>V) list \<Rightarrow> (V\<times>V) list"
where
  "consMorphCompInhSt SGL rl = consMorphCompInhSt0 SGL rl"

lemma consMorphCompInhSt_is_eq:
  assumes "is_wf_g (toSGr SGL)" 
  shows "set(consMorphCompInhSt SGL rl) = set(rl) O inhst (toSGr SGL)"
proof
  show "set (consMorphCompInhSt SGL rl) \<subseteq> set rl O inhst (toSGr SGL)"
  proof (rule subrelI)
    fix x y
    assume "(x, y) \<in> set (consMorphCompInhSt SGL rl)"
    hence "(x, y) \<in> set (consMorphCompInhSt0 SGL rl)" 
      by (simp add: consMorphCompInhSt_def)
    then show "(x, y) \<in> set rl O inhst (toSGr SGL)"
    proof (induct rl)
      case Nil
      then show ?case by auto
    next
      fix p rl
      assume h1: "(x, y) \<in> set (consMorphCompInhSt0 SGL rl) \<Longrightarrow> (x, y) \<in> set rl O inhst (toSGr SGL)"
      assume "(x, y) \<in> set (consMorphCompInhSt0 SGL (p # rl))"
      hence "(x, y) \<in> set(consMorphCompInhStPair SGL p)\<or> (x, y) \<in> set(consMorphCompInhSt0 SGL (rl))" 
        by auto
      then show "(x, y) \<in> set (p # rl) O inhst (toSGr SGL)"
      proof
        assume "(x, y) \<in> set(consMorphCompInhStPair SGL p)"
        hence "(x, y) \<in> {p} O inhst (toSGr SGL)"
          using assms by (simp only: consMorphCompInhStPair_eq)
        then show "(x, y) \<in> set (p # rl) O inhst (toSGr SGL)" by auto
      next
        assume "(x, y) \<in> set (consMorphCompInhSt0 SGL rl)"
        then show "(x, y) \<in> set (p # rl) O inhst (toSGr SGL)"
          using h1 by auto
      qed
    qed
  qed
next
  show "set rl O inhst (toSGr SGL) \<subseteq> set (consMorphCompInhSt SGL rl)"
  proof (rule subrelI)
    fix x y
    assume "(x, y) \<in> set rl O inhst (toSGr SGL)"
    then show "(x, y) \<in> set (consMorphCompInhSt SGL rl)"
    proof (induct rl)
      case Nil
      then show ?case by auto
    next
      fix p rl
      assume h: "(x, y) \<in> set rl O inhst (toSGr SGL) \<Longrightarrow> (x, y) \<in> set (consMorphCompInhSt SGL rl)"
      assume "(x, y) \<in> set (p # rl) O inhst (toSGr SGL)"
      hence "(x, y) \<in> {p} O inhst (toSGr SGL) \<or> (x, y) \<in> set (rl) O inhst (toSGr SGL)" by auto
      then show "(x, y) \<in> set (consMorphCompInhSt SGL (p # rl))"
      proof
        assume "(x, y) \<in> {p} O inhst (toSGr SGL)"
        hence "(x, y) \<in> set(consMorphCompInhStPair SGL p)"
          using assms by (simp only: consMorphCompInhStPair_eq)
        then show "(x, y) \<in> set (consMorphCompInhSt SGL (p # rl))"
          by (simp add: consMorphCompInhSt_def)
      next
        assume "(x, y) \<in> set rl O inhst (toSGr SGL)"
        then show "(x, y) \<in> set (consMorphCompInhSt SGL (p # rl))"
          using h by (simp add: consMorphCompInhSt_def)
      qed
    qed
  qed
qed

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

lemma pfunToRel_eq_set_fV:
  assumes "distinct(map fst (fVL SGL))" 
  shows "pfunToRel (fV (toMorph SGL)) = set(fVL SGL)"
proof
  show "pfunToRel (fV (toMorph SGL)) \<subseteq> set (fVL SGL)" 
  proof (rule subrelI)
    fix x y
    assume "(x, y) \<in> pfunToRel (fV (toMorph SGL))"
    then show "(x, y) \<in> set (fVL SGL)" 
      by (simp add: pfunToRel_def toMorph_def map_of_SomeD)
  qed
next
  show "set (fVL SGL) \<subseteq> pfunToRel (fV (toMorph SGL))"
  proof (rule subrelI)
    fix x y
    assume "(x, y) \<in> set (fVL SGL)"
    then show "(x, y) \<in> pfunToRel (fV (toMorph SGL))"
      using assms by (simp add: pfunToRel_def toMorph_def)
  qed
qed

lemma pfunToRel_eq_set_fE:
  assumes "distinct(map fst (fEL SGL))" 
  shows "pfunToRel (fE (toMorph SGL)) = set(fEL SGL)"
proof
  show "pfunToRel (fE (toMorph SGL)) \<subseteq> set (fEL SGL)" 
  proof (rule subrelI)
    fix x y
    assume "(x, y) \<in> pfunToRel (fE (toMorph SGL))"
    then show "(x, y) \<in> set (fEL SGL)" 
      by (simp add: pfunToRel_def toMorph_def map_of_SomeD)
  qed
next
  show "set (fEL SGL) \<subseteq> pfunToRel (fE (toMorph SGL))"
  proof (rule subrelI)
    fix x y
    assume "(x, y) \<in> set (fEL SGL)"
    then show "(x, y) \<in> pfunToRel (fE (toMorph SGL))"
      using assms by (simp add: pfunToRel_def toMorph_def)
  qed
qed

lemma pfunToRel_eq_set_srcG:
  assumes "distinct(map fst (srcG GL))" 
  shows "pfunToRel (src (toGr GL)) = set(srcG GL)"
  by (simp add: assms pfunTorel_is_eq toGr_def)

lemma pfunToRel_eq_set_tgtG:
  assumes "distinct(map fst (tgtG GL))" 
  shows "pfunToRel (tgt (toGr GL)) = set(tgtG GL)"
  by (simp add: assms pfunTorel_is_eq toGr_def)

end