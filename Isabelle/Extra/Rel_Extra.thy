theory Rel_Extra
imports Relation
begin

lemma single_valued_Un: "single_valued (r \<union> s) \<Longrightarrow> single_valued r \<and> single_valued s"
  by (auto simp add: single_valued_def)

lemma single_valued_dist_Un: 
  assumes h1: "Domain r \<inter> Domain s = {}"
  shows "single_valued (r \<union> s) \<longleftrightarrow> single_valued r  \<and> single_valued s"
  proof
    assume "single_valued (r \<union> s)"
    then show "single_valued r \<and> single_valued s"
      using single_valued_Un[of r s]
      by (simp)
  next
    assume "single_valued r \<and> single_valued s"
    then show "single_valued (r \<union> s)"
      using h1 by (auto simp add: single_valued_def)
  qed

(*Defines the domain restriction*)
definition dres :: "'a set \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> ('a \<times> 'b) set" (infixl "\<lhd>" 100)
where
  "A \<lhd> r \<equiv> {(x, y). (x, y) \<in> r \<and> x \<in> A}"

lemma dres_empty[simp]: "{}\<lhd> r = {}"
  by (simp add: dres_def)

lemma in_dres: "(a, b) \<in> A \<lhd> r \<Longrightarrow> a \<in> A"
  by (simp add: dres_def)

(*Defines the range restriction*)
definition rres :: "('a \<times> 'b) set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set" (infixl "\<rhd>" 100)
where
  "r\<rhd> B \<equiv> {(x, y). (x, y) \<in> r \<and> y \<in> B}"

lemma rres_empty[simp]: "r\<rhd>{} = {}"
  by (simp add: rres_def)

(*Gives pairs that are linked across two relations*)
definition at_intersec_rel:: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel"
where
  "at_intersec_rel r s \<equiv> {(x, y). 
    (x, y) \<in> (Field r \<inter> Field s)\<lhd>(r \<union> s) \<union> (r \<union> s)\<rhd>(Field r \<inter> Field s)}"

lemma at_intersec_rel1_empty[simp]: "at_intersec_rel {} s = {}"
  by (auto simp add: at_intersec_rel_def)

lemma at_intersec_rel2_empty[simp]: "at_intersec_rel r {} = {}"
  by (auto simp add: at_intersec_rel_def)

lemma in_intersec_rel_in_cup: "(x, y) \<in> at_intersec_rel r s \<Longrightarrow> (x, y) \<in> r \<union> s"
  by (auto simp add: at_intersec_rel_def dres_def rres_def)

lemma in_at_intersec_rel_in_Dom: "(x, y) \<in> at_intersec_rel r s \<Longrightarrow> x \<in> Domain (r \<union> s)"
  by (auto simp add: at_intersec_rel_def dres_def rres_def)

lemma in_at_intersec_rel_in_Ran: "(x, y) \<in> at_intersec_rel r s \<Longrightarrow> y \<in> Range (r \<union> s)"
  by (auto simp add: at_intersec_rel_def dres_def rres_def)

lemma not_in_at_intersec_rel: 
  "(x, y) \<notin> at_intersec_rel r s \<Longrightarrow> (x, y) \<notin> (r \<union> s) 
    \<or> ((x, y) \<in> (r \<union> s) \<and> (x \<notin> Domain (r \<inter>  s)\<and> y \<notin> Range (r \<inter> s)))"
    by (auto simp add: at_intersec_rel_def dres_def rres_def Field_def)

lemma in_at_intersec_rel_1:
  assumes h1: "x \<in> Field r" and h2: "x \<in> Field s" and h3: "(x, z) \<in> r \<union> s"
  shows "(x, z) \<in> at_intersec_rel r s"
    using h1 h2 h3 by (auto simp add: at_intersec_rel_def dres_def rres_def)

lemma in_at_intersec_rel_2:
  assumes h1: "x \<in> Field r" and h2: "x \<in> Field s" and h3: "(z, x) \<in> r \<union> s"
  shows "(z, x) \<in> at_intersec_rel r s"
    using h1 h2 h3 by (auto simp add: at_intersec_rel_def dres_def rres_def)

lemma disj_then_at_intersec_rel_empty:
  assumes h1: "Field r \<inter> Field s = {}"
  shows "at_intersec_rel r s = {}"
    using h1 by (simp add: at_intersec_rel_def)

lemma at_intersec_rel_empty_then_disj:
  assumes h1: "at_intersec_rel r s = {}"
  shows "Field r \<inter> Field s = {}"
  proof (rule ccontr)
    assume h2: "Field r \<inter> Field s \<noteq> {}"
    from h2 have h3: "\<exists> x z. x \<in> Field r \<inter> Field s \<and> ((x, z) \<in> r \<union> s \<or> (z, x) \<in> r \<union> s)" 
      by (auto simp add: Field_def)
    from h3 have h4: "at_intersec_rel r s \<noteq> {}"
      by (clarify) (erule disjE, auto intro: in_at_intersec_rel_1 in_at_intersec_rel_2)
    from h1 h4 show "False" by simp
  qed

lemma not_disj_then_at_intersec_not_empty:
  assumes h1: "Field r \<inter> Field s \<noteq> {}"
  shows "at_intersec_rel r s \<noteq> {}"
  proof (rule ccontr, simp)
    assume h2: "at_intersec_rel r s = {}"
    from h2 have h2a: "Field r \<inter> Field s = {}" 
      by (simp add: at_intersec_rel_empty_then_disj)
    from h1 h2a show False
      by simp
  qed

(* Defines the relation override of Z*)
definition rel_override :: "('a \<times> 'b) set \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> ('a \<times> 'b) set" (infixr "\<oplus>" 100)
where
  "r \<oplus> s \<equiv> {(x, y). (x \<in> Domain s \<and> (x, y) \<in> s) \<or> (x \<notin> Domain s \<and> (x, y) \<in> r)}"

lemma rel_override_reflex[simp]: "r \<oplus> r = r"
  by (auto simp add: rel_override_def)

definition rel_total_on::"('a\<times>'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool"
where
  "rel_total_on r A B \<equiv> Domain r = A \<and> Range r \<subseteq> B"

lemma in_to_image: "((x, y) \<in> r) = (y \<in> r``{x})"
  proof
    assume "(x, y) \<in> r"
    then show "y \<in> r `` {x}"
      by auto
  next
    assume "y \<in> r `` {x}"
    then show "(x, y) \<in> r"
      by auto
  qed

end