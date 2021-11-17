theory Rel_Extra
imports Main
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

(* Domain restriction *)
definition dres :: "'a set \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> ('a \<times> 'b) set" (infixl "\<lhd>" 100)
where
  "A \<lhd> r \<equiv> {(x, y). (x, y) \<in> r \<and> x \<in> A}"

lemma dres_empty[simp]: "{}\<lhd> r = {}"
  by (simp add: dres_def)

lemma dres_domain_r[simp]: "(Domain r)\<lhd> r = r"
  by (auto simp add: dres_def)

lemma in_dres: "(a, b) \<in> A \<lhd> r \<Longrightarrow> a \<in> A"
  by (simp add: dres_def)

lemma dres_union_r: "A \<lhd> (r \<union> s) = (A \<lhd> r) \<union> (A \<lhd> s)"
  by (auto simp add: dres_def)

(* Range restriction *)
definition rres :: "('a \<times> 'b) set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set" (infixl "\<rhd>" 100)
where
  "r\<rhd> B \<equiv> {(x, y). (x, y) \<in> r \<and> y \<in> B}"

lemma rres_empty[simp]: "r\<rhd>{} = {}"
  by (simp add: rres_def)

(* Domain subtraction *)
definition dsub :: "'a set \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> ('a \<times> 'b) set" (infixl "\<unlhd>" 100)
where
  "A \<unlhd> r \<equiv> ((Domain r) - A) \<lhd> r"

lemma dsub_empty[simp]: "{} \<unlhd> r = r"
  by (simp add: dsub_def)

lemma dsub_emptyr[simp]: "A \<unlhd> {} = {}"
  by (simp add: dsub_def)

lemma dsub_domain_r[simp]: "(Domain r) \<unlhd> r = {}"
  by (simp add: dsub_def)

lemma dsub_union_r: "A \<unlhd> (r \<union> s) = (A \<unlhd> r) \<union> (A \<unlhd> s)"
  by (auto simp add: dsub_def dres_union_r dres_def Domain_def)

(* Range subtraction *)
definition rsub :: "('a \<times> 'b) set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set" (infixl "\<unrhd>" 100)
where
  "r \<unrhd> B \<equiv> r \<rhd> ((Range r) - B)"

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

(* Z's relation override *)
definition rel_override :: "('a \<times> 'b) set \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> ('a \<times> 'b) set" (infixr "\<oplus>" 100)
where
  "r \<oplus> s \<equiv> ((Domain s)\<unlhd> r) \<union> s"

lemma rel_override_reflex[simp]: "r \<oplus> r = r"
  by (auto simp add: rel_override_def)

lemma override_r_w_empty[simp]:
  shows "r \<oplus> {} = r"
  by (simp add: rel_override_def)

lemma override_empty_w_s[simp]:
  shows "{} \<oplus> s = s"
  by (auto simp add: rel_override_def)

lemma override_union_w_r: "(s \<union> t) \<oplus> r = (s \<oplus> r) \<union> (t\<oplus> r)"
  by (auto simp add: rel_override_def dsub_union_r)

lemma in_override_in_r:
  assumes "(x, y) \<in> r \<oplus>s" and "x \<notin> (Domain s)"
  shows "(x, y) \<in> r"
using assms 
  by (simp add: rel_override_def Domain_iff dsub_def dres_def)

lemma in_r_in_override:
  assumes "(x, y) \<in> r" and "x \<notin> (Domain s)"
  shows "(x, y) \<in> r \<oplus>s"
using assms 
by (auto simp add: rel_override_def Domain_iff dsub_def dres_def)

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

definition rtotalise_in::"('a\<times>'a) set \<Rightarrow> 'a set\<Rightarrow>('a\<times>'a) set"
  where
  "rtotalise_in r A = (Id_on A) \<oplus> r"

lemma rtotalise_in_empty[simp]:
  shows "rtotalise_in r {} = r"
  by (simp add: rtotalise_in_def) 

lemma rtotalise_empty_in_something[simp]:
  shows "rtotalise_in {} s = (Id_on s)"
  by (simp add: rtotalise_in_def)

lemma Id_on_union: "Id_on (A \<union> B) = Id_on A \<union> Id_on B"
proof
  show "Id_on (A \<union> B) \<subseteq> Id_on A \<union> Id_on B"
    by blast
next
  show "Id_on A \<union> Id_on B \<subseteq> Id_on (A \<union> B)"
    by blast
qed

lemma totalise_in_union:
  shows "rtotalise_in r (A \<union> B) = rtotalise_in r A \<union> rtotalise_in r B"
  by (simp add: rtotalise_in_def Id_on_union override_union_w_r)

definition overridecl :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"  ("(_\<^sup>\<oplus>)" [1000] 999)
  where
    "r\<^sup>\<oplus> \<equiv> r\<^sup>+ - {(x, y) . (x, y) \<in> r \<and> x \<noteq> y \<and> (\<exists> z. z \<noteq> y \<and> (y, z) \<in> r)}" 

(*inductive_set overridecl :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"  ("(_\<^sup>\<oplus>)" [1000] 999)
  for r :: "('a \<times> 'a) set"
  where
    into_overridecl [intro!, Pure.intro!]: "(x, y) \<in> r \<Longrightarrow>x = y \<Longrightarrow> (x, y) \<in> r\<^sup>\<oplus>"
  | into_overridecl2 [intro!, Pure.intro!]: "(x, y) \<in> r \<Longrightarrow>x \<noteq> y \<Longrightarrow> y \<notin> (Domain r) \<Longrightarrow> (x, y) \<in> r\<^sup>\<oplus>"
  (*| into_overridecl2 [intro!, Pure.intro!]: "(x, y) \<in> r\<^sup>+ \<Longrightarrow>y \<notin> (Domain (r\<^sup>+)) \<Longrightarrow> (x, y) \<in> r\<^sup>\<oplus>"*)
  | overridecl_into_override_cl [Pure.intro]: "(y, z) \<in> r\<^sup>\<oplus> \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> (x, z) \<in> r\<^sup>\<oplus>"*)


lemma subset_overridecl1:  
  shows "{(x, y). (x, y) \<in> r \<and> (x = y \<or> x \<noteq> y \<and> y \<notin> Domain r)} \<subseteq> r\<^sup>\<oplus>"
proof (rule subrelI)
  fix x y 
  assume ha: "(x, y) \<in> {(x, y). (x, y) \<in> r \<and> (x = y \<or> x \<noteq> y \<and> y \<notin> Domain r)}"
  hence hb: "(x, y) \<in> r" by auto
  from ha have hc: "x = y \<or> x \<noteq> y \<and> y \<notin> Domain r" by auto
  then show "(x, y) \<in> r\<^sup>\<oplus>"
  proof
    assume "x = y"
    then show "(x, y) \<in> r\<^sup>\<oplus>"
      using hb by (simp add: overridecl_def)
  next
    assume "x \<noteq> y \<and> y \<notin> Domain r"
    then show "(x, y) \<in> r\<^sup>\<oplus>" 
      using hb by (auto simp add: overridecl_def)
  qed
qed

(*lemma in_domain_overridecl:  
  assumes "x \<in> Domain r"
  shows "x \<in> Domain (r\<^sup>\<oplus>)"
proof -
  from assms show ?thesis
  proof
    fix y
    assume ha: "(x, y) \<in> r"
    then show "x \<in> Domain (r\<^sup>\<oplus>)"
    proof (case_tac "x = y")
      assume "x = y"
      then show "x \<in> Domain (r\<^sup>\<oplus>)"
        using ha by (auto simp add: Domain_iff overridecl_def)
    next
      assume hb: "x \<noteq> y"
      then show "x \<in> Domain (r\<^sup>\<oplus>)"
      proof (case_tac "\<exists> z. z \<noteq> y \<and> (y, z) \<in> r")
        assume "\<exists>z. z \<noteq> y \<and> (y, z) \<in> r"
        then show "x \<in> Domain (r\<^sup>\<oplus>)"
        proof
          fix z
          assume "z \<noteq> y \<and> (y, z) \<in> r"
          then show "x \<in> Domain (r\<^sup>\<oplus>)" 
            using ha hb 
            by (auto simp add: overridecl_def Domain_iff)
        proof (case_tac "(y, y) \<in> r")
          assume "(y, y) \<in> r"
          then show "x \<in> Domain (r\<^sup>\<oplus>)" 
            using ha by (auto simp add: overridecl_def Domain_iff)
        next
          assume hd: "(y, y) \<notin> r"
          from hc show "x \<in> Domain (r\<^sup>\<oplus>)" 
          proof
            fix z
            assume "(y, z) \<in> r"
            then show "x \<in> Domain (r\<^sup>\<oplus>)" 
              using ha hd by (simp add: overridecl_def Domain_iff)
        hence "\<exists> z. (x, z) \<in> r\<^sup>+ \<and> z\<noteq>y"
          using ha hb by auto
        then show "x \<in> Domain (r\<^sup>\<oplus>)"
        
    proof (simp add: Domain_iff)
      fix z
      show "(x, z) \<in> r\<^sup>\<oplus>"
      
    proof (case_tac "x \<in> Domain (r O r)")
      assume "x \<in> Domain (r O r)"
      then show "x \<in> Domain (r\<^sup>\<oplus>)"
        using ha 
        by (auto simp add: Domain_iff into_overridecl relcomp_unfold)
      
    next
      assume "x \<notin> Domain (r O r)"
      hence "(x, y) \<in> r\<^sup>\<oplus>"
      using ha by (simp add: overridecl_x_not_in_domain_comp)
      then show "x \<in> Domain (r\<^sup>\<oplus>)"
        by (auto simp add: Domain_iff overridecl_x_not_in_domain_comp)
    
 
      proof (case_tac "\<exists> w. (y, w) \<in> r\<^sup>\<oplus>")
        assume "\<exists>w. (y, w) \<in> r\<^sup>\<oplus>" 
        then show "x \<in> Domain (r\<^sup>\<oplus>)"
        by (meson Domain_iff ha hb overridecl.into_overridecl2)
      next
        assume "\<nexists>w. (y, w) \<in> r\<^sup>\<oplus>"
        hence "\<forall> w. (y, w) \<notin> r\<^sup>\<oplus>" by auto
        then show "x \<in> Domain (r\<^sup>\<oplus>)"
        proof 
    next
      assume "y \<notin> Domain r"
      then show "x \<in> Domain (r\<^sup>\<oplus>)" 
        using ha by blast
    
      
  then show "(x, z) \<in> r\<^sup>\<oplus>"
  proof
    fix y
    assume "(x, y) \<in> r"
    then show "(x, z) \<in> r\<^sup>\<oplus>"*)
   
(*lemma in_overridecl:
  assumes "(x, y) \<in> r" 
  shows "\<exists> w. (x, w) \<in> r\<^sup>\<oplus>"
proof (case_tac "x \<in> Domain (r O r)")
  assume "x \<in> Domain (r O r)"
  
  then show "\<exists>w. (x, w) \<in> r\<^sup>\<oplus>"
  
  
  fix w
  show "(x, w) \<in> r\<^sup>\<oplus>"
  proof*)
    
end