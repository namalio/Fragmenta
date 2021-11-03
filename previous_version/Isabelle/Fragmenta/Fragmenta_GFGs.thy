theory Fragmenta_GFGs
imports Base_GraphsL Fragmenta_Frs

begin

datatype GFGEdgeTy = eimp | econti 

definition GFGEdgeTy_set :: "GFGEdgeTy set"
where 
   "GFGEdgeTy_set = {eimp, econti}"

(*Type of GFGr*)
record GFGr = Gr +
   ext_ty :: "E \<rightharpoonup> GFGEdgeTy" 

definition gr_gfg :: "GFGr \<Rightarrow> Gr"
where
  "gr_gfg GFG = \<lparr>Ns = Ns GFG, Es = Es GFG, src = src GFG, tgt = tgt GFG\<rparr>"

(*All nodes of a GFG must have a corresponding self edge*)
definition NodesWithSelfEdges :: "GFGr \<Rightarrow> bool"
where
  "NodesWithSelfEdges GFG \<equiv> 
    (\<forall> v. v \<in> Ns GFG \<longrightarrow> (\<exists> e. e \<in> Es GFG \<and> src GFG e = Some v \<and> tgt GFG e = Some v))"

definition is_wf_gfg :: "GFGr \<Rightarrow> bool"
where
  "is_wf_gfg GFG \<equiv> is_wf_g GFG 
      \<and> ftotal_on (ext_ty GFG) (Es GFG) GFGEdgeTy_set 
      \<and> NodesWithSelfEdges GFG
      \<and> acyclicGr (restrict GFG ((Es GFG) - (EsId GFG)))"

(*Type of GFGr_ls*)
record GFGr_ls = Gr_ls +
   ext_ty_ls :: "(E \<times> GFGEdgeTy) list" 

definition grl_gfgl :: "GFGr_ls \<Rightarrow> Gr_ls"
where
  "grl_gfgl GFG = \<lparr>NsG = NsG GFG, EsG = EsG GFG, srcG = srcG GFG, tgtG = tgtG GFG\<rparr>"

(*A function that converts the list-based representation to the set-based one*)
definition toGFGr :: "GFGr_ls \<Rightarrow> GFGr"
where
  "toGFGr GFGL \<equiv> \<lparr>Ns = set (NsG GFGL), 
    Es = set (EsG GFGL), 
    src = map_of (srcG GFGL), 
    tgt = map_of (tgtG GFGL),
    ext_ty = map_of (ext_ty_ls GFGL)\<rparr>"

definition is_wf_gfg_ls :: "GFGr_ls \<Rightarrow> bool"
where
  "is_wf_gfg_ls GFGL \<equiv> distinct (NsG GFGL) 
    \<and> distinct (map fst (srcG GFGL)) \<and> distinct (map fst (tgtG GFGL)) 
    \<and> is_wf_gfg (toGFGr GFGL)"

(*Definitions that are useful for acyclicity proofs of GFGs*)
primrec consAcyclicEs:: "GFGr \<Rightarrow> E list \<Rightarrow> E list"
where
  "consAcyclicEs GFG [] = []"
  | "consAcyclicEs GFG (e#es) = (if e \<in> (Es GFG) \<and> e \<notin> (EsId GFG) 
      then e#(consAcyclicEs GFG es) 
      else (consAcyclicEs GFG es))"

lemma sub_EsG: "set(consAcyclicEs GFG es) \<subseteq> Es GFG"
  by (induct es, simp_all)

lemma consAcyclicEs_same:
  assumes "e \<notin> (Es GFG) \<or> e \<in> (EsId GFG)"
  shows "consAcyclicEs GFG (e#es) = consAcyclicEs GFG es"
  proof -
    from assms show ?thesis
      by auto
  qed
  
lemma in_consAcyclicEs_iff:
  fixes e
  shows "e \<in> set(consAcyclicEs GFG es) \<longleftrightarrow> e \<in> set (es) \<and> e \<in> (Es GFG) \<and> e \<notin> (EsId GFG)"
  proof
    assume "e \<in> set (consAcyclicEs GFG es)"
    then show "e \<in> set es \<and> e \<in> Es GFG \<and> e \<notin> EsId GFG"
    proof (induct es, simp)
      fix a es'
      assume ha: "(e \<in> set (consAcyclicEs GFG es') \<Longrightarrow> e \<in> set es' \<and> e \<in> Es GFG \<and> e \<notin> EsId GFG)"
      assume hb: "e \<in> set (consAcyclicEs GFG (a # es'))"
      show "e \<in> set (a # es') \<and> e \<in> Es GFG \<and> e \<notin> EsId GFG"
      proof (case_tac "a \<in> Es GFG \<and> a \<notin> EsId GFG")
        assume hc: "a \<in> Es GFG \<and> a \<notin> EsId GFG"
        from hb hc have "e \<in> set(a#consAcyclicEs GFG es')"
          by auto
        then show "e \<in> set (a # es') \<and> e \<in> Es GFG \<and> e \<notin> EsId GFG"
          using hc ha by auto
      next
        assume hc: "\<not> (a \<in> Es GFG \<and> a \<notin> EsId GFG)"
        from hb hc have "e \<in> set(consAcyclicEs GFG es')"
          by auto
        then show "e \<in> set (a # es') \<and> e \<in> Es GFG \<and> e \<notin> EsId GFG"
          using hc ha by auto
      qed  
    qed
  next
    show "e \<in> set es \<and> e \<in> Es GFG \<and> e \<notin> EsId GFG \<Longrightarrow> e \<in> set (consAcyclicEs GFG es)"
    proof (induct es, simp)
      fix a es'
      assume ha: "(e \<in> set es' \<and> e \<in> Es GFG \<and> e \<notin> EsId GFG \<Longrightarrow> e \<in> set (consAcyclicEs GFG es'))"
      assume hb: "e \<in> set (a # es') \<and> e \<in> Es GFG \<and> e \<notin> EsId GFG"
      then show "e \<in> set (consAcyclicEs GFG (a # es'))"
      proof (case_tac "e=a")
        assume hc: "e=a"
        then show "e \<in> set (consAcyclicEs GFG (a # es'))"
          using ha hb by auto
      next
        assume hc: "e \<noteq> a"
        then show "e \<in> set (consAcyclicEs GFG (a # es'))"
          using ha hb by auto
      qed
    qed      
  qed

lemma rel_restrict_eq_consRel0:
  assumes ha: "is_wf_g (toGFGr GFGL)" 
  shows "relOfGr (restrict (toGFGr GFGL) ((Es (toGFGr GFGL)) - (EsId (toGFGr GFGL)))) 
    = set(consRel0 (toGFGr GFGL) (consAcyclicEs (toGFGr GFGL) (EsG GFGL)))"
  proof -
    let ?restrict_G = "restrict (toGFGr GFGL) (Es (toGFGr GFGL) - EsId (toGFGr GFGL))"
    have hb: "Es (toGFGr GFGL) = set (EsG GFGL)"
          by (simp add: in_set_EsG toGFGr_def)
    show ?thesis
    proof
      show "relOfGr (?restrict_G) \<subseteq> set(consRel0 (toGFGr GFGL) (consAcyclicEs (toGFGr GFGL) (EsG GFGL)))"
      proof (rule subrelI)
        fix x y
        have hc: "set (consAcyclicEs (toGFGr GFGL) (EsG GFGL)) \<subseteq> Es (toGFGr GFGL)"
          by (simp add: sub_EsG)
        have hd: "is_wf_g (?restrict_G)"
          using ha by (simp add: toGr_def is_wf_restrict)
        assume "(x, y) \<in> relOfGr (?restrict_G)"
        then have "\<exists>e. e \<in> Es (toGFGr GFGL) \<and> e \<notin> (EsId (toGFGr GFGL)) 
          \<and> src (toGFGr GFGL) e = Some x \<and> tgt (toGFGr GFGL) e = Some y"
          using ha hb by (auto simp add: relOfGr_def adjacent_def rst_fun_def vimage_def 
            restrict_map_def is_wf_g_def ftotal_on_def in_set_EsG)
        then show "(x, y) \<in> set(consRel0 (toGFGr GFGL) (consAcyclicEs (toGFGr GFGL) (EsG GFGL)))"
          using ha hc hb by (auto simp add: in_consRel0)
            (rule exI, auto simp add: in_consAcyclicEs_iff)
      qed
    next
      show "set(consRel0 (toGFGr GFGL) (consAcyclicEs (toGFGr GFGL) (EsG GFGL)))
        \<subseteq> relOfGr (?restrict_G)"
      proof (rule subrelI)
        fix x y
        assume "(x, y) \<in> set(consRel0 (toGFGr GFGL) (consAcyclicEs (toGFGr GFGL) (EsG GFGL)))"
        then have "\<exists>e. e \<in> Es (toGFGr GFGL) \<and> e \<notin> (EsId (toGFGr GFGL)) 
          \<and> src (toGFGr GFGL) e = Some x \<and> tgt (toGFGr GFGL) e = Some y"
          using ha sub_EsG[of "(toGFGr GFGL)" "(EsG GFGL)"] hb
          by (simp add: in_consRel0 in_consAcyclicEs_iff)
        then show "(x, y) \<in> relOfGr (restrict (toGFGr GFGL) (Es (toGFGr GFGL) - EsId (toGFGr GFGL)))"
          using ha hb by (auto simp add: relOfGr_def adjacent_def rst_fun_def vimage_def 
            restrict_map_def is_wf_g_def ftotal_on_def in_set_EsG)
      qed
    qed
  qed

(* GFG morphisms*)
definition morphGFGr :: "GFGr \<Rightarrow> GFGr \<Rightarrow> Morph set"
where
  "morphGFGr GFG1 GFG2 \<equiv> 
    morphGr GFG1 GFG2 \<inter> {r. (ext_ty GFG2) \<circ>\<^sub>m (fE r) = (ext_ty GFG1)}"

(* F to GFG morphisms*)
definition morphF2GFGr :: "Fr \<Rightarrow> GFGr \<Rightarrow> Morph set"
where
  "morphF2GFGr F GFG \<equiv> morphGr (withRsG F) (gr_gfg GFG) 
    \<inter> {r. Ns (sg F) \<noteq> {} \<longrightarrow> (\<exists> vf. (fV r)`(Ns (sg F)) = {Some vf}
      \<and> Es (sg F) - EsR(sg F) \<noteq> {} \<longrightarrow> (\<exists> ef. (fE r)`(Es (sg F) - EsR(sg F)) = {Some ef} 
        \<and> (src GFG ef) = Some vf \<and> (tgt GFG ef) = Some vf))}"

end
