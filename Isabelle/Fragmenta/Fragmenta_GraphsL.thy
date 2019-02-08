(*  Title:      List version of the Fragmenta Theory of Graphs
    Description: 'Fragmenta' theory of Graphs presented in the Models 2015 paper.
    Author:     Nuno Amálio
*)

theory Fragmenta_GraphsL
imports Fragmenta_Graphs Base_GraphsL
begin

definition consUG:: "'a Gr_ls_scheme \<Rightarrow> 'a Gr_ls_scheme \<Rightarrow> Gr_ls"
where
  "consUG GL1 GL2 = \<lparr>NsG = (NsG GL1)@(NsG GL2), 
    EsG = (EsG GL1)@(EsG GL2),
    srcG = (srcG GL2)@(srcG GL1), 
    tgtG = (tgtG GL2)@(tgtG GL1)\<rparr>"

lemma NsG_consUG[simp]: "NsG (consUG GL1 GL2) = (NsG GL1)@(NsG GL2)"
  by (simp add: consUG_def)

lemma EsG_consUG[simp]: "EsG (consUG GL1 GL2) = (EsG GL1)@(EsG GL2)"
  by (simp add: consUG_def)

lemma srcG_consUG[simp]: "srcG (consUG GL1 GL2) = (srcG GL2)@(srcG GL1)"
  by (simp add: consUG_def)

lemma tgtG_consUG[simp]: "tgtG (consUG GL1 GL2) = (tgtG GL2)@(tgtG GL1)"
  by (simp add: consUG_def)

lemma "(toGr GL1) UG (toGr GL2) = toGr (consUG GL1 GL2)"
  proof (simp add: Gr_eq, rule conjI)
    show "Ns (toGr GL1) \<union> Ns (toGr GL2) = Ns (toGr (consUG GL1 GL2))"
      by (simp add: toGr_def)
  next
    apply_end (rule conjI)
    show "Es (toGr GL1) \<union> Es (toGr GL2) = Es (toGr (consUG GL1 GL2))"
      by (simp add: toGr_def)
  next
    apply_end (rule conjI)
    show "src (toGr GL1) ++ src (toGr GL2) = src (toGr (consUG GL1 GL2))"
    by (simp add: toGr_def)
  next
    show "tgt (toGr GL1) ++ tgt (toGr GL2) = tgt (toGr (consUG GL1 GL2))"
    by (simp add: toGr_def)
  qed

(*An alternative representation of morphisms as lists*)
record MorphL =
  fVL :: "(V\<times>V) list"
  fEL :: "(E\<times>E) list"

(*The empty graph morphism in the listed representation*)
definition emptyGML :: "MorphL"
where
  "emptyGML \<equiv> \<lparr>fVL = [], fEL = [] \<rparr>"

definition toMorph :: "MorphL \<Rightarrow> Morph"
where
  "toMorph ML \<equiv> \<lparr>fV = map_of (fVL ML), fE = map_of (fEL ML)\<rparr>"

definition is_wf_MorphL:: "MorphL \<Rightarrow> bool"
where
  "is_wf_MorphL ML \<equiv> distinct (map fst (fVL ML)) \<and> distinct (map fst (fEL ML))"

lemma pfunTorel_is_eq: 
  assumes "distinct(map fst LP)"
  shows "pfunToRel (map_of LP) = set LP"
proof
  show "pfunToRel (map_of LP) \<subseteq> set LP"
  proof (rule subrelI)
    fix x y
    assume "(x, y) \<in> pfunToRel (map_of LP)"
    then show "(x, y) \<in> set LP" 
      by (simp add: map_of_SomeD pfunToRel_def)
  qed
next
  show "set LP \<subseteq> pfunToRel (map_of LP)"
    using assms by (simp add: pfunToRel_def)
qed

definition consUGM:: "'a MorphL_scheme \<Rightarrow> 'a MorphL_scheme \<Rightarrow> MorphL"
where
  "consUGM ML1 ML2 = \<lparr>fVL = (fVL ML2)@(fVL ML1), fEL = (fEL ML2)@(fEL ML1)\<rparr>"

lemma fVL_consUGM[simp]: "fVL (consUGM ML1 ML2) = (fVL ML2)@(fVL ML1)"
  by (simp add: consUGM_def)

lemma fEL_consUGM[simp]: "fEL (consUGM ML1 ML2) = (fEL ML2)@(fEL ML1)"
  by (simp add: consUGM_def)

lemma UGM_eq_ConsUGM: "(toMorph ML1) UGM (toMorph ML2) = toMorph(consUGM ML1 ML2)"
  proof (simp add: Morph_eq, rule conjI)  
    show "fV (toMorph ML1) ++ fV (toMorph ML2) = fV (toMorph (consUGM ML1 ML2))"
      by (simp add: toMorph_def)
  next
    show "fE (toMorph ML1) ++ fE (toMorph ML2) = fE (toMorph (consUGM ML1 ML2))"
      by (simp add: toMorph_def)
  qed


end