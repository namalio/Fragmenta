theory Map_Extra
imports Main List_Extra "../Extra/Set_Extra"
begin

lemma map_comp_assoc: "(f \<circ>\<^sub>m g)\<circ>\<^sub>m h = f \<circ>\<^sub>m (g\<circ>\<^sub>m h)"
proof
  fix x
  show " (f \<circ>\<^sub>m g \<circ>\<^sub>m h) x = (f \<circ>\<^sub>m (g \<circ>\<^sub>m h)) x"
    by (auto simp add: map_comp_def option.case_eq_if)
qed

(*Goes from a partial function (a Isabelle map) to a relation*)
definition pfunToRel:: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<times>'b) set"
where
  "pfunToRel f \<equiv> {(x, y). f x = Some y}"

lemma pfunToRelEmpty[simp]: "pfunToRel Map.empty = {}"
  by (simp add: pfunToRel_def)

lemma pfunToRelSing: "pfunToRel [a\<mapsto>b] = {(a, b)}"
  by (auto simp add: pfunToRel_def split: if_splits)

lemma pfunToRel_map_comp: "pfunToRel (f \<circ>\<^sub>m g) = pfunToRel g O pfunToRel f"
proof
  show "pfunToRel (f \<circ>\<^sub>m g) \<subseteq> pfunToRel g O pfunToRel f"
    by (smt map_comp_Some_iff mem_Collect_eq pfunToRel_def prod.simps(2) relcomp.simps subrelI)
next
  show "pfunToRel g O pfunToRel f \<subseteq> pfunToRel (f \<circ>\<^sub>m g)"
  by (smt map_comp_def mem_Collect_eq option.case(2) pfunToRel_def prod.simps(2) relcompE subrelI)
qed

lemma pfunToRel_iff:
  "(x, y) \<in> pfunToRel f \<longleftrightarrow> f x = Some y"
  by (simp add: pfunToRel_def)

lemma Domain_is_dom:
  "Domain (pfunToRel f) = dom f"
  by (auto simp add: Domain_iff domIff pfunToRel_iff)
    
definition mid_on::"'a set \<Rightarrow> ('a \<rightharpoonup> 'a)"
  where
  "mid_on A \<equiv> \<lambda>x. if x \<in> A then Some x else None"

lemma mid_on_empty[simp]: "mid_on {} = Map.empty" 
  by (simp add: mid_on_def)

lemma dom_mid_on[simp]: "dom (mid_on A) = A"
  by (auto simp add: mid_on_def split: if_splits)

lemma ran_mid_on[simp]: "ran (mid_on A) = A"
  by (auto simp add: mid_on_def ran_def split: if_splits)

lemma mid_on_union: "mid_on (A \<union> B) = (mid_on A) ++ (mid_on B)"
by (auto simp add: mid_on_def map_add_def split: option.splits)

lemma mid_on_comp_f:"(mid_on (ran f))\<circ>\<^sub>m f = f"
  by (auto simp add: mid_on_def map_comp_def ran_def split: option.splits) 

lemma mid_on_comp_idemp1:
  assumes "ran f \<subseteq> A"
  shows "(mid_on A)\<circ>\<^sub>m f = f"
proof
  fix x
  show "(mid_on A \<circ>\<^sub>m f) x = f x"
  using assms 
  by (auto simp add: mid_on_def map_comp_def ran_def 
      split: option.splits)
qed

lemma mid_on_comp_idemp2:
  assumes "dom f \<subseteq> A"
  shows "f \<circ>\<^sub>m (mid_on A)= f"
proof
  fix x
  show "(f \<circ>\<^sub>m mid_on A) x = f x"
  proof (cases "x \<in> A")
    assume "x \<in> A"
    then show "(f \<circ>\<^sub>m mid_on A) x = f x" 
      using assms by (simp add: mid_on_def map_comp_def )
  next
    assume "x \<notin> A"
    hence "x\<notin> dom f" using assms by auto
    then show "(f \<circ>\<^sub>m mid_on A) x = f x" 
    by (auto simp add: mid_on_def map_comp_def)
  qed
qed

lemma f_comp_mid_on:"f \<circ>\<^sub>m (mid_on (dom f))  = f"
  by (auto simp add: mid_on_def map_comp_def dom_def 
      split: option.splits) 

definition mtotalise_in::"('a \<rightharpoonup> 'a) \<Rightarrow> 'a set\<Rightarrow>('a \<rightharpoonup> 'a)"
  where
  "mtotalise_in f A = (mid_on A) ++ f"

lemma mtotalise_in_in_empty[simp]:
  shows "mtotalise_in f {} = f"
  by (simp add: mtotalise_in_def) 

lemma mtotalise_empty_in_something[simp]:
  shows "mtotalise_in Map.empty s = (mid_on s)"
  by (simp add: mtotalise_in_def)

lemma mtotalise_in_in_union:
  shows "mtotalise_in f (A \<union> B) = mtotalise_in f A ++ mtotalise_in f B"
  by (metis map_add_assoc map_add_subsumed1 map_le_map_add mid_on_union mtotalise_in_def)

definition ftotal_on::"('a\<rightharpoonup>'b)\<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool"
where
  "ftotal_on f A B \<equiv> dom f = A \<and> ran f \<subseteq> B"

lemma ftotal_on_empty[simp]: "ftotal_on Map.empty {} {}"
  by (auto simp add: ftotal_on_def)

lemma ftotal_on_mid[simp]: "ftotal_on (mid_on A) A A"
  by (auto simp add: ftotal_on_def)

lemma ftotal_on_dom: "ftotal_on f A B \<Longrightarrow> dom f = A"
  by (auto simp add: ftotal_on_def)

lemma ftotal_on_ran: "ftotal_on f A B \<Longrightarrow> ran f \<subseteq> B"
  by (auto simp add: ftotal_on_def)

lemma app_ftotal: "ftotal_on f A B \<Longrightarrow> x \<in> A \<Longrightarrow> \<exists> y. f x = Some y"
  by (auto simp add: ftotal_on_def dom_def)

lemma ftotal_on_map_add: 
  assumes "ftotal_on f A B" and  "ftotal_on g C D"
    and "A \<inter> C = {}"
  shows "ftotal_on (f++g) (A \<union> C) (B \<union> D)"
  using assms 
  by (auto simp add: ftotal_on_def ran_map_add)

lemma ftotal_on_mcomp: 
  assumes "ftotal_on f A B" and "ftotal_on g B C"  
  shows "ftotal_on (g \<circ>\<^sub>m f) A C"
  using assms
  by (auto simp add: map_comp_def ftotal_on_def dom_def ran_def
      split: option.splits) 

definition fpartial_on::"('a\<rightharpoonup>'b)\<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool"
where
  "fpartial_on f A B \<equiv> dom f \<subseteq> A \<and> ran f \<subseteq> B"

lemma fpartial_on_map_add: 
  assumes "fpartial_on f A B" and "fpartial_on g C D"
  shows  "fpartial_on (f++g) (A \<union> C) (B \<union> D)"
  using assms 
  by (auto simp add: fpartial_on_def map_add_def dom_def ran_def split: option.splits)

lemma fpartial_on_sup: 
  assumes "fpartial_on f A B" and "A \<subseteq> C"
  shows  "fpartial_on f C B"
  using assms 
  by (auto simp add: fpartial_on_def map_add_def dom_def ran_def split: option.splits)

lemma not_fpartial_on_sub: 
  assumes "\<not>fpartial_on f C B" and "A \<subseteq> C"
  shows  "\<not>fpartial_on f A B"
  using assms 
  by (auto simp add: fpartial_on_def map_add_def dom_def ran_def split: option.splits)


definition injective::"('a\<rightharpoonup>'b)\<Rightarrow>bool"
  where
  "injective f \<equiv> \<forall> x y. {x, y} \<subseteq> dom f \<and> f x = f y \<longrightarrow> x = y"

lemma injective_map_add:
  assumes "injective f" and "injective g"
    and "ran f \<inter> ran g = {}"
  shows "injective (f ++ g)"
proof (simp only: injective_def, clarify)
  fix x y
  assume "{x, y} \<subseteq> dom (f ++ g)" and "(f ++ g) x = (f ++ g) y"
  hence "{x, y} \<subseteq> dom f \<union> dom g" by auto
  hence "x \<in> dom f \<or> x \<in> dom g" by auto
  show "x = y"
  proof (case_tac "x \<in> dom g")
    assume "x \<in> dom g"
    show "x = y"
    proof (case_tac "y \<in> dom g")
      assume "y \<in> dom g"
      then show "x = y"
        using assms(2) \<open>(f ++ g) x = (f ++ g) y\<close>
        \<open>x \<in> dom g\<close>
        by (auto simp add: injective_def dom_def split: option.splits)
    next
      assume "y \<notin> dom g"
      hence "y \<in> dom f" 
        using \<open>{x, y} \<subseteq> dom f \<union> dom g\<close>
        by auto
      then show "x = y"
        using  \<open>(f ++ g) x = (f ++ g) y\<close> \<open>x \<in> dom g\<close>
        assms
        by (auto simp add: injective_def ran_def dom_def map_add_def
            split: option.splits)
    qed
  next
    assume "x \<notin> dom g"
    hence "x \<in> dom f"
      using \<open>{x, y} \<subseteq> dom f \<union> dom g\<close>
      by auto
    show "x = y"
    proof (case_tac "y \<in> dom g")
      assume "y \<in> dom g"
      then show "x = y"
        by (metis \<open>(f ++ g) x = (f ++ g) y\<close> \<open>x \<notin> dom g\<close> assms(3) disjoint_iff domD 
            map_add_dom_app_simps(1) map_add_dom_app_simps(3) ranI)
    next
      assume "y \<notin> dom g"
      hence "y \<in> dom f" using \<open>{x, y} \<subseteq> dom f \<union> dom g\<close>
        by auto
      then show "x = y"
      using  \<open>(f ++ g) x = (f ++ g) y\<close> \<open>y \<in> dom f\<close>
        assms
        by (auto simp add: injective_def ran_def dom_def map_add_def
            split: option.splits)
    qed
  qed
qed

definition finj_on::"('a\<rightharpoonup>'b)\<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool"
  where
  "finj_on f A B \<equiv> ftotal_on f A B  \<and> injective f"

lemma finj_on_dist_map_add:
  assumes "finj_on f A B" and "finj_on g C D"
    and "disjoint [A, B, C, D]"
  shows "finj_on (f++g) (A \<union> C) (B \<union> D)"
proof-
  have "A \<inter> C = {}"
    using assms(3) by (auto)
  have "ran f \<inter> ran g = {}"
    using assms by (auto simp add: finj_on_def ftotal_on_def) 
  show ?thesis
    using assms(1) assms(2) \<open>A \<inter> C = {}\<close> \<open>ran f \<inter> ran g = {}\<close>
    by (simp add: finj_on_def ftotal_on_map_add injective_map_add)
qed

definition fbij_on::"('a\<rightharpoonup>'b)\<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool"
  where
  "fbij_on f A B \<equiv> finj_on f A B \<and> ran f = B" 

lemma fbij_on_dist_map_add:
  assumes "fbij_on f A B" and "fbij_on g C D"
    and "disjoint [A, B, C, D]"
  shows "fbij_on (f++g) (A \<union> C) (B \<union> D)"
proof -
  have "dom f \<inter> dom g = {}" 
    using assms by (auto simp add: fbij_on_def finj_on_def 
        ftotal_on_def)
  show ?thesis
  using assms \<open>dom f \<inter> dom g = {}\<close>
  by (simp add: fbij_on_def finj_on_dist_map_add ran_map_add)
qed

definition mrres::"('a\<rightharpoonup>'b)\<Rightarrow> 'b set \<Rightarrow> ('a\<rightharpoonup>'b)" (infixl "\<rhd>\<^sub>m" 100)
where
  "f \<rhd>\<^sub>m B = (\<lambda>x. if (f x) \<in> Some `B then f x else None)" 

lemma mrres_empty[simp]: "f \<rhd>\<^sub>m {} = Map.empty"
  by (simp add: mrres_def)

lemma mrres_emptyf[simp]: "Map.empty \<rhd>\<^sub>m A = Map.empty"
  by (simp add: mrres_def)

lemma mrres_ran_sub1: "ran(f \<rhd>\<^sub>m A) \<subseteq> A"
  by (auto simp add: mrres_def ran_def)

lemma dom_mrres_sub_dom:
  "dom (f \<rhd>\<^sub>m B) \<subseteq> dom f"
  by (simp add: domIff mrres_def subset_iff)

lemma map_add_mrres_un:
  assumes "dom f \<inter> dom g = {}" 
    and "A \<inter> ran g = {}" and "B \<inter> ran f = {}"
  shows "f ++ g \<rhd>\<^sub>m (A \<union> B) = (f \<rhd>\<^sub>m A) ++  (g \<rhd>\<^sub>m B)"
proof
  fix x
  show "(f ++ g \<rhd>\<^sub>m (A \<union> B)) x = ((f \<rhd>\<^sub>m A) ++ (g \<rhd>\<^sub>m B)) x"
  proof (case_tac "x \<in> dom g")
    assume "x \<in> dom g"
    hence h: "(f ++ g \<rhd>\<^sub>m (A \<union> B)) x = (g \<rhd>\<^sub>m (A \<union> B)) x"
      by (auto simp add: mrres_def)
    show "(f ++ g \<rhd>\<^sub>m (A \<union> B)) x = (f \<rhd>\<^sub>m A ++ (g \<rhd>\<^sub>m B)) x"
    proof (case_tac "g x \<in> Some `B")
      assume "g x \<in> Some `B"
      hence "g x \<in> Some ` (A \<union> B)" by auto
      hence "(g \<rhd>\<^sub>m (A \<union> B)) x = (g \<rhd>\<^sub>m B) x"
        using \<open>x \<in> dom g\<close> \<open>g x \<in> Some `B\<close>
        by (simp add: mrres_def )
      then show "(f ++ g \<rhd>\<^sub>m (A \<union> B)) x = (f \<rhd>\<^sub>m A ++ (g \<rhd>\<^sub>m B)) x"
        using \<open>x \<in> dom g\<close> \<open>g x \<in> Some `B\<close>
        by (auto simp add: h map_add_dom_app_simps(1) mrres_def)
    next
      assume "g x \<notin> Some `B"
      have "g x \<notin> Some ` (A \<union> B)"
      proof (rule ccontr)
        assume "\<not> g x \<notin> Some ` (A \<union> B)"
        hence "g x \<in> Some ` (A \<union> B)" by auto
        hence "g x \<in> Some ` A" 
          using \<open>g x \<notin> Some `B\<close> by auto
        then show "False"
          using assms(2) by (auto simp add: ran_def)
      qed
      hence h1: "(g \<rhd>\<^sub>m (A \<union> B)) x = None"
        by (simp add: mrres_def)
      have h2: "(f \<rhd>\<^sub>m A ++ (g \<rhd>\<^sub>m B)) x = None"
        using \<open>g x \<notin> Some `B\<close> \<open>x \<in> dom g\<close> assms(1)
        by (auto simp add: mrres_def)
      then show "(f ++ g \<rhd>\<^sub>m (A \<union> B)) x = (f \<rhd>\<^sub>m A ++ (g \<rhd>\<^sub>m B)) x"
        by (simp add: h h1 h2)
    qed
  next
    assume "x \<notin> dom g"
    then show "(f ++ g \<rhd>\<^sub>m (A \<union> B)) x = (f \<rhd>\<^sub>m A ++ (g \<rhd>\<^sub>m B)) x"
    proof (case_tac "f x \<in> Some ` A")
      assume "f x \<in> Some ` A"
      hence "f x \<in> Some ` (A \<union> B)" by auto
      hence "(f ++ g) x \<in> Some ` (A \<union> B)" 
        using \<open>f x \<in> Some ` A\<close> \<open>x \<notin> dom g\<close>
        by (simp add: map_add_dom_app_simps(3))
      hence h1: "(f ++ g \<rhd>\<^sub>m (A \<union> B)) x = (f \<rhd>\<^sub>m A) x"
        using \<open>f x \<in> Some ` A\<close> \<open>f x \<in> Some ` (A \<union> B)\<close> \<open>x \<notin> dom g\<close>
        by (simp add: map_add_dom_app_simps(3) mrres_def)
      have h2: "(f \<rhd>\<^sub>m A ++ (g \<rhd>\<^sub>m B)) x = (f \<rhd>\<^sub>m A) x"
        using \<open>x \<notin> dom g\<close>
        by (auto simp add: map_add_dom_app_simps(3) mrres_def domIff)
      show "(f ++ g \<rhd>\<^sub>m (A \<union> B)) x = (f \<rhd>\<^sub>m A ++ (g \<rhd>\<^sub>m B)) x"
        by (simp add: h1 h2)
    next
      assume "f x \<notin> Some ` A"
      hence h1: "(f ++ g \<rhd>\<^sub>m (A \<union> B)) x = None"
        using \<open>x \<notin> dom g\<close> assms(3)
        by (auto simp add: map_add_dom_app_simps(3) mrres_def ranI)
      have h2: "(f \<rhd>\<^sub>m A ++ (g \<rhd>\<^sub>m B)) x = None"
        using \<open>x \<notin> dom g\<close> \<open>f x \<notin> Some ` A\<close>
        by (auto simp add: map_add_dom_app_simps(3) mrres_def)
      then show "(f ++ g \<rhd>\<^sub>m (A \<union> B)) x = (f \<rhd>\<^sub>m A ++ (g \<rhd>\<^sub>m B)) x"
        by (simp add: h1 h2)
    qed
  qed
qed
 
lemma mrres_ran_sub2: 
  assumes "(ran f) \<subseteq> B"
  shows "ran(f \<rhd>\<^sub>m A) \<subseteq> B"
  using assms
  by (auto simp add: mrres_def ran_def)

definition mdsub::"'a set \<Rightarrow> ('a\<rightharpoonup>'b)\<Rightarrow>('a\<rightharpoonup>'b)" (infixl "\<unlhd>\<^sub>m" 100)
  where
  "A \<unlhd>\<^sub>m f = (\<lambda>x. if x \<in> A then None else f x)" 

lemma mdsub_empty[simp]: " {} \<unlhd>\<^sub>m f = f"
  by (simp add: mdsub_def)

lemma mdsub_emptyf[simp]: "A \<unlhd>\<^sub>m Map.empty  = Map.empty"
  by (simp add: mdsub_def)

lemma mdsub_map_add: "A \<unlhd>\<^sub>m(f ++g) = (A \<unlhd>\<^sub>mf)++(A \<unlhd>\<^sub>mg)"
  by (simp add: map_add_def mdsub_def fun_eq_iff)

lemma mdsub_map_add_absorb_1: 
  assumes "B \<inter> (dom f) = {}"
  shows "(A \<union> B) \<unlhd>\<^sub>m f = A \<unlhd>\<^sub>mf"
  using assms 
  by (simp add: domIff mdsub_def disjoint_iff fun_eq_iff)
  
lemma dom_mdsub_if:
  assumes "dom f = A" and "dom g \<subseteq> A" and "ran g \<subseteq> A"
  shows "dom ( (dom g - ran g)  \<unlhd>\<^sub>m f) = A - (dom g) \<union> (ran g)"
proof
  show "dom ((dom g - ran g) \<unlhd>\<^sub>m f) \<subseteq> A - dom g \<union> ran g"
    by (smt (verit, ccfv_SIG) DiffI UnI1 UnI2 assms(1) domIff mdsub_def subsetI)
next
  show "A - dom g \<union> ran g \<subseteq> dom ((dom g - ran g) \<unlhd>\<^sub>m f)"
  proof
    fix x
    assume "x \<in> A - dom g \<union> ran g"
    hence "x \<in> A \<and> x \<notin> dom g \<or> x \<in> ran g"
      by auto
    then show "x \<in> dom ((dom g - ran g) \<unlhd>\<^sub>m f)"
    proof
      assume "x \<in> A \<and> x \<notin> dom g"
      then show "x \<in> dom ((dom g - ran g) \<unlhd>\<^sub>m f)"
        using assms(1)
        by (auto simp add: mdsub_def dom_def)
    next
      assume "x \<in> ran g"
      hence "x \<in> A" using assms(3) by auto
      then show "x \<in> dom ((dom g - ran g) \<unlhd>\<^sub>m f)"
        using assms(1) \<open>x \<in> ran g\<close>
        by (auto simp add: mdsub_def)
    qed
  qed
qed

lemma ran_mdsub_sub:
  shows "ran (A  \<unlhd>\<^sub>m f) \<subseteq> ran f "
  by (auto simp add: mdsub_def ran_def)

lemma mdsub_not_in_dom:
  assumes "A \<inter> dom f = {}"
  shows "A \<unlhd>\<^sub>m f = f"
proof
  fix x
  show "(A \<unlhd>\<^sub>m f) x = f x" 
  proof (case_tac "x \<in> A")
    assume "x \<in> A"
    hence "x \<notin> dom f" using assms by auto
    then show "(A \<unlhd>\<^sub>m f) x = f x" 
      using assms by (auto simp add: mdsub_def)
  next
    assume "x \<notin> A"
    then show "(A \<unlhd>\<^sub>m f) x = f x" 
      using assms by (auto simp add: mdsub_def)
  qed
qed  

definition mrsub::"('a\<rightharpoonup>'b)\<Rightarrow>'b set \<Rightarrow> ('a\<rightharpoonup>'b)" (infixl "\<unrhd>\<^sub>m" 100)
  where
  "f \<unrhd>\<^sub>m B = (\<lambda>x. if f x \<in> (Some ` B) then None else f x)" 

lemma mrsub_empty[simp]: " f \<unrhd>\<^sub>m {} = f"
  by (simp add: mrsub_def)

lemma mrsub_emptym[simp]: "Map.empty \<unrhd>\<^sub>m B = Map.empty"
  by (simp add: mrsub_def)

lemma dom_mrsub_sub_dom:
  "dom (f \<unrhd>\<^sub>m B) \<subseteq> dom f"
  by (simp add: mrsub_def domIff subset_iff)
 

(*definition minv::"('a\<rightharpoonup>'b)\<Rightarrow>('b\<rightharpoonup>'a)" ("(_\<inverse>\<^sup>m)" [1000] 999)
  where
  " f\<inverse>\<^sup>m = (\<lambda>x. if x \<in> (ran f) then Some (the_elem (f -`{Some x})) else None)"

lemma 
  assumes "injective f"
  shows "f\<inverse>\<^sup>m \<circ>\<^sub>m f = mid_on (dom f)"
proof
  fix x
  show "(f\<inverse>\<^sup>m \<circ>\<^sub>m f) x = mid_on (dom f) x"
  proof (case_tac "x \<in> dom f")
    assume "x \<in> dom f"
    then show "(f\<inverse>\<^sup>m \<circ>\<^sub>m f) x = mid_on (dom f) x"
      using assms
      by (auto simp add: mid_on_def minv_def map_comp_def vimage_def
          the_elem_def ran_def injective_def dom_def split: option.splits)
*)

lemma map_add_disj_domf: 
  assumes "dom f \<inter> dom g = {}"
  shows "x \<in> dom f \<longrightarrow> (f++g)x = f x"
  using assms
  by (auto simp add: map_add_def split: option.splits)


lemma map_add_disj_dom2f: 
  assumes "dom f \<inter> dom g = {}"
  shows "x \<notin> dom g \<longrightarrow> (f++g)x = f x"
  proof
    fix x
    from assms show "x \<notin> dom g \<Longrightarrow> (f ++ g) x = f x"
      by (auto simp add: map_add_def split: option.splits)
  qed

lemma pfunToRel_map_add: 
  assumes "dom f \<inter> dom g = {}"
  shows "pfunToRel (f ++ g) = pfunToRel f \<union> pfunToRel g"
proof
  show "pfunToRel (f ++ g) \<subseteq> pfunToRel f \<union> pfunToRel g"
  proof (rule subrelI)
    fix x y
    assume "(x, y) \<in> pfunToRel (f ++ g)"
    hence "(f ++ g) x = Some y" by (simp only: pfunToRel_iff)
    then show "(x, y) \<in> pfunToRel f \<union> pfunToRel g"
    proof (case_tac "x \<in> dom f")
      assume "x \<in> dom f"
      hence "f x = Some y" 
        using assms \<open>(f ++ g) x = Some y\<close>
        by (auto simp add: map_add_def split: option.splits)
      then show "(x, y) \<in> pfunToRel f \<union> pfunToRel g"
        by (simp add: pfunToRel_iff)
    next
      assume "x \<notin> dom f"
      hence "g x = Some y" 
        using assms \<open>(f ++ g) x = Some y\<close>
        by (auto simp add: map_add_def split: option.splits)
      then show "(x, y) \<in> pfunToRel f \<union> pfunToRel g"
        by (simp add: pfunToRel_iff)
    qed
  qed
next
  show "pfunToRel f \<union> pfunToRel g \<subseteq> pfunToRel (f ++ g)"
  proof (rule subrelI)
    fix x y
    assume "(x, y) \<in> pfunToRel f \<union> pfunToRel g"
    then show "(x, y) \<in> pfunToRel (f ++ g)"
    proof
      assume "(x, y) \<in> pfunToRel f"
      hence "f x = Some y" by (simp only: pfunToRel_iff)
      hence "x \<in> dom f" by auto
      then show "(x, y) \<in> pfunToRel (f ++ g)"
        using assms \<open>f x = Some y\<close>
        by (simp add: pfunToRel_iff map_add_disj_domf)
    next
      assume "(x, y) \<in> pfunToRel g"
      hence "g x = Some y" by (simp only: pfunToRel_iff)
      hence "x \<in> dom g" by auto
      then show "(x, y) \<in> pfunToRel (f ++ g)"
        using assms \<open>g x = Some y\<close>
        by (simp add: pfunToRel_iff map_add_disj_domf)
    qed
  qed
qed

lemma in_union_if_is_map_add:
  shows "(\<lambda> x. if x \<in> A \<union> B then Some v else None) 
    = (\<lambda> x. if x \<in> A then Some v else None) 
      ++ (\<lambda> x. if x \<in> B then Some v else None)"
proof
  fix x
  show "(if x \<in> A \<union> B then Some v else None) =
         ((\<lambda>x. if x \<in> A then Some v else None) ++
          (\<lambda>x. if x \<in> B then Some v else None))
          x"
    by (smt (z3) Un_iff map_add_None map_add_Some_iff)
qed

lemma map_add_app_disj: 
  assumes h1: "dom f \<inter> dom g = {}"
  shows "(f++g) x = (if x \<in> dom f then f x else g x)"
  proof -
    fix x
    from h1 show "(f++g) x = (if x \<in> dom f then f x else g x)"
    proof (case_tac "x \<in> dom f")
      assume h2: "x \<in> dom f"
      from h2 show "(f++g) x = (if x \<in> dom f then f x else g x)"
        using h1 by (simp add: map_add_disj_domf)
    next
      assume h2: "x \<notin> dom f"
      show "(f++g) x = (if x \<in> dom f then f x else g x)"
      proof (case_tac "x \<in> dom g")
        assume h3: "x \<in> dom g"
        show "(f++g) x = (if x \<in> dom f then f x else g x)"
        using h1 h2 h3 by (simp add: map_add_dom_app_simps)
      next
        assume h3: "x \<notin> dom g"
        show "(f++g) x = (if x \<in> dom f then f x else g x)"
        using h1 h2 h3 by (auto simp add: map_add_def)
      qed
    qed
  qed

lemma map_add_comp_disj_1:
  shows "(f ++ g \<circ>\<^sub>m h) = (f \<circ>\<^sub>m h)++ (g \<circ>\<^sub>m h)"
  by (auto simp add: map_add_def map_comp_def option.case_eq_if)

lemma dom_map_comp_ran_sub_dom:
  assumes "ran h \<subseteq>dom f" 
  shows "dom (f \<circ>\<^sub>m h) = dom h"
  using assms 
  by (auto simp add: map_comp_def dom_def ran_def split: option.splits)

lemma ran_map_comp_ran_sub_dom:
  assumes "ran h \<subseteq>dom f" 
  shows "ran (f \<circ>\<^sub>m h) \<subseteq> ran f"
  using assms 
  by (auto simp add: map_comp_Some_iff ran_def dom_def)

lemma map_add_comp_disj:
  assumes "dom f \<inter> dom g = {}" and "dom h \<inter> dom k = {}" 
    and "ran h \<subseteq> dom f" and  "ran k \<subseteq> dom g"
  shows "(f ++ g) \<circ>\<^sub>m (h ++ k) = (f \<circ>\<^sub>m h)++(g \<circ>\<^sub>m k)"
proof
  fix x
  show "(f ++ g \<circ>\<^sub>m h ++ k) x = ((f \<circ>\<^sub>m h) ++ (g \<circ>\<^sub>m k)) x"
  proof (case_tac "x \<in> dom h")
    assume h: "x \<in> dom h"
    hence "x \<in> dom (f \<circ>\<^sub>m h)"
      using assms(3) ranI by fastforce     
    hence "(f ++ g \<circ>\<^sub>m h ++ k) x = (f \<circ>\<^sub>m h) x"
      by (metis assms(1) assms(2) h map_add_comm map_add_comp_disj_1 
          map_add_dom_app_simps(1) map_comp_def)
    then show "(f ++ g \<circ>\<^sub>m h ++ k) x = ((f \<circ>\<^sub>m h) ++ (g \<circ>\<^sub>m k)) x"
      by (metis assms(2) disjoint_iff domIff h map_add_dom_app_simps(3) map_comp_simps(1))
  next
    assume h: "x \<notin> dom h" 
    then show "(f ++ g \<circ>\<^sub>m h ++ k) x = ((f \<circ>\<^sub>m h) ++ (g \<circ>\<^sub>m k)) x"
      by (smt (verit, ccfv_threshold) assms(4) domIff map_add_None 
          map_add_comp_disj_1 map_add_dom_app_simps(1) 
          map_comp_None_iff map_comp_def ranI subset_eq)
  qed
qed


lemma ftotal_on_munion: 
  assumes "ftotal_on f A B" and "ftotal_on g C D"
    and "disjoint [A, B, C, D]"
  shows "ftotal_on (f ++ g) (A \<union> C) (B \<union> D)"
  using assms
    by (simp add: ftotal_on_def ran_map_add)(blast)

lemma map_add_restrict_dist: "(f++g)|`A = f|`A ++ g|`A"
  by (auto simp add: restrict_map_def map_add_def)

lemma map_add_image_dist: 
  assumes "A \<subseteq> dom f" and "dom f \<inter> dom g = {}"
  shows "(f++g)`A = f`A"
  using assms 
  by (auto simp add: image_def map_add_def split: option.splits)

lemma map_add_image_dist2: 
  assumes h1: "A \<subseteq> dom g" and h2: "dom f \<inter> dom g = {}"
  shows "(f++g)`A = g`A"
  proof
    from h1 show "f ++ g ` A \<subseteq> g ` A"
    proof (simp add: less_eq_set_def le_fun_def, clarify)
      fix xa
      assume "xa \<in> A"
      then show "(f ++ g) xa \<in> g ` A"
      using h2 h1 by (auto simp add: image_def map_add_def split: option.splits)(force)
    qed
  next
    show "g ` A \<subseteq> f ++ g ` A"
      using h1 h2 by (auto simp add: map_add_def image_def split: option.splits)
  qed

(*lemma map_add_image_dist: "(f++g)`A = f`A \<union> g`A"
proof
  show "f ++ g ` A \<subseteq> f ` A \<union> g ` A"
  proof
    fix x
    assume "x \<in> f ++ g ` A"
    then show "x \<in> f ` A \<union> g ` A"
    proof (case_tac 
      by (auto simp add: map_add_def image_def split: option.splits)
qed*)

lemma ran_map_add_sub:
  shows "ran (f++g) \<subseteq> ran f \<union> ran g"
  proof
    fix x
    assume "x \<in> ran (f ++ g)"
    then show "x \<in> ran f \<union> ran g"
      by (auto simp add: map_add_def ran_def split: option.splits)
  qed

lemma ran_map_add_disj_ran_f: "ran f \<inter> ran g = {} \<Longrightarrow> y \<in> ran f \<Longrightarrow> (f++g) x = Some y 
  \<Longrightarrow> x \<in> dom f"
   by (auto simp add: map_add_def dom_def ran_def split: option.splits)

lemma ran_map_add_disj_ran_g: "ran f \<inter> ran g = {} \<Longrightarrow> y \<in> ran g \<Longrightarrow> (f++g) x = Some y 
  \<Longrightarrow> x \<in> dom g"
   by (auto simp add: map_add_def dom_def ran_def split: option.splits)

lemma ran_restrict_sub: "ran (f |`A) \<subseteq> ran f"
  by (auto simp add: restrict_map_def ran_def split: if_splits)

lemma ran_map_add_eq:
  shows "ran (f++g) = ran ((dom g) \<unlhd>\<^sub>m f) \<union> ran g"
proof
  show "ran (f ++ g) \<subseteq> ran (dom g \<unlhd>\<^sub>m f) \<union> ran g"
    by (smt (z3) UnI1 dom_def map_add_Some_iff mdsub_def mem_Collect_eq ran_def subsetI sup_commute)
next
  show "ran (dom g \<unlhd>\<^sub>m f) \<union> ran g \<subseteq> ran (f ++ g)"
    by (smt (z3) disjoint_iff_not_equal dom_def map_add_Some_iff mdsub_def mem_Collect_eq ran_def ran_map_add subsetI)
qed

lemma ran_mtotalise_in_if_dom_sub:
  shows "ran(mtotalise_in f A) = A - dom f \<union> ran f"
proof 
  show "ran (mtotalise_in f A) \<subseteq> A - dom f \<union> ran f"
    by (smt (verit, ccfv_threshold) Diff_iff Un_iff dom_def map_add_dom_app_simps(3) map_le_def map_le_map_add mem_Collect_eq mid_on_def mtotalise_in_def option.simps(1) ran_def subsetI)
next
  show "A - dom f \<union> ran f \<subseteq> ran (mtotalise_in f A)"
  proof
    fix y
    assume "y \<in> A - dom f \<union> ran f"
    hence "y \<in> A \<and> y \<notin> dom f \<or> y\<in> ran f" by auto
    then show "y \<in> ran (mtotalise_in f A)"
    proof
      assume "y \<in> A \<and> y \<notin> dom f"
      hence "mtotalise_in f A y = Some y"
        by (simp add: mtotalise_in_def map_add_def dom_def
           mid_on_def)
      then show "y \<in> ran (mtotalise_in f A)"
        by (simp add: mtotalise_in_def ranI)
    next
      assume "y \<in> ran f"
      from \<open>y \<in> ran f\<close> obtain x where "f x = Some y" 
        by (auto simp add: ran_def)
      hence "mtotalise_in f A x = Some y"
        by (simp add: mtotalise_in_def map_add_def dom_def
           mid_on_def)
      then show "y \<in> ran (mtotalise_in f A)"
        by (simp add: mtotalise_in_def ranI)
    qed
  qed
qed
  
lemma vimage_in_dom:
  assumes "dom f = A"
  shows "f-`(Some ` B) \<subseteq> A"
  using assms
  by (auto simp add: vimage_def dom_def)

lemma vimage_is_dom_rres:
  "f -` (Some ` B) = dom (f \<rhd>\<^sub>m B)"
proof
  show "f -` Some ` B \<subseteq> dom (f \<rhd>\<^sub>m B)"
  proof
    fix x
    assume "x \<in> f -` Some ` B"
    from \<open>x \<in> f -` Some ` B\<close> obtain y where "f x = Some y \<and> y \<in> B"
      by (auto simp add: vimage_def image_def)
    then show "x \<in> dom (f \<rhd>\<^sub>m B)"
      by (simp add: mrres_def dom_def)
  qed
next
  show "dom (f \<rhd>\<^sub>m B) \<subseteq> f -` Some ` B"
    by (auto simp add: mrres_def subsetI dom_def)
qed

lemma vimage_disj_ran_1:
  assumes "ran f \<inter> ran g = {}" and "dom f \<inter> dom g = {}" and "x \<in> ran f"
  shows "(f++g) -`{Some x} = f -`{Some x}"
  by (smt (verit, ccfv_SIG) Int_commute assms disjoint_iff 
      inf_sup_absorb map_add_Some_iff map_add_comm ranI 
      vimage_insert vimage_inter_cong vimage_singleton_eq)

lemma vimage_disj_ran_2:
  assumes "ran f \<inter> ran g = {}" and "dom f \<inter> dom g = {}" and "x \<in> ran g"
  shows "(f++g) -`{Some x} = g -`{Some x}"
  by (metis assms inf_sup_aci(1) map_add_comm vimage_disj_ran_1)

lemma mdsub_vimage_is_int:
  "A \<unlhd>\<^sub>m f -` (Some ` B) = dom (f \<rhd>\<^sub>m B) - A"
proof
  show "A \<unlhd>\<^sub>m f -` Some ` B \<subseteq> dom (f \<rhd>\<^sub>m B) - A"
  proof
    fix x
    assume "x \<in> A \<unlhd>\<^sub>m f -` Some ` B"
    hence "x \<notin> A \<and> x \<in> f -` Some ` B" 
      by (auto  simp add: mdsub_def image_def split: if_splits)
    then show "x \<in> dom (f \<rhd>\<^sub>m B) - A"
      by (simp add: vimage_is_dom_rres)
  qed
next
  show "dom (f \<rhd>\<^sub>m B) - A \<subseteq> A \<unlhd>\<^sub>m f -` Some ` B"
  proof
    fix x
    assume "x \<in> dom (f \<rhd>\<^sub>m B) - A"
    hence "x \<notin> A \<and> x \<in> f -` Some ` B"
      by (simp add: vimage_is_dom_rres)
    then show "x \<in> A \<unlhd>\<^sub>m f -` Some ` B"
      by (simp add: mdsub_def)
  qed
qed 

lemma map_add_dists_vimage: "\<lbrakk>None \<notin> A; dom f \<inter> dom g = {}\<rbrakk>\<Longrightarrow>(f++g)-`A =f-`A \<union> g-`A"
  proof -
    assume h1: "None \<notin> A"
    assume h3: "dom f \<inter> dom g = {}"
    show "(f++g)-`A =f-`A \<union> g-`A"
    proof
      show "f ++ g -` A \<subseteq> f -` A \<union> g -` A"
      proof
        fix x
        show "x \<in> f ++ g -` A \<Longrightarrow> x \<in> f -` A \<union> g -` A"
          by (auto simp add: map_add_def split: option.splits)
      qed
      next
      show "f -` A \<union> g -` A \<subseteq> f ++ g -` A"
      proof
        fix x
        show "x \<in> f -` A \<union> g -` A \<Longrightarrow> x \<in> f ++ g -` A"
        proof (simp add: vimage_def)
          assume h5: "f x \<in> A \<or> g x \<in> A"
          have h5a: "f x \<noteq> None \<or> g x \<noteq> None" 
            using h1 h5 by (auto)
          show "(f ++ g) x \<in> A"
          proof (case_tac "g x = None")
            assume h6: "g x = None"
            show "(f ++ g) x \<in> A"
              using h1 h3 h5a h5 h6 
              by (auto simp add: vimage_def map_add_def split: option.splits)
         next
            assume h7: "g x \<noteq> None"
            show "(f ++ g) x \<in> A"
            proof (case_tac "f x = None")
              assume h8: "f x = None"
              show "(f ++ g) x \<in> A" 
                using h1 h5 h5a h7 h8 
                by (auto simp add: vimage_def map_add_def split: option.splits)
              next
              assume h9: "f x \<noteq> None"
              show "(f ++ g) x \<in> A" 
                using h7 h9 h3
                by (auto simp add: vimage_def map_add_def split: option.splits)
           qed
        qed
     qed
   qed
 qed
qed

lemma retrict_Un:
  assumes "B \<inter> dom f = {}" 
  shows "f|`(A\<union>B) = f |`A"
proof -
  show ?thesis
  proof
    fix x
    show "(f |` (A \<union> B)) x = (f |` A) x"
      using assms
      by (auto simp add: restrict_map_def)
  qed
qed

lemma inj_on_map_dist_on_disj_doms:
  assumes h1: "A \<subseteq> dom f" and h2: "B \<subseteq> dom g" and h3: "dom f \<inter> dom g = {}"
    and h4: "ran f \<inter> ran g = {}"
  shows "inj_on (f ++g) (A \<union> B) = ((inj_on f A) \<and> (inj_on g B))"
  proof
    assume h5: "inj_on (f ++ g) (A \<union> B)"
    show "inj_on f A \<and> inj_on g B"
    proof
      show "inj_on f A"
      proof (simp add: inj_on_def)
        apply_end(clarify)
        fix x y
        assume h6a: "x \<in> A"
        hence h6b: "x \<in> (dom f)" using h1 by auto
        from h6a have h6c: "x \<in> A \<union> B" by auto
        assume h6d: "y \<in> A"
        hence h6e: "y \<in> (dom f)" using h1 by auto
        assume h6f: "f x = f y"
        from h6b h6e h6f h3 have h6g: "(f++g) x = (f++g) y"
          by (simp add: map_add_app_disj)
        from h5 show "x = y" 
          using h6a h6b h6c h6d h6e h6f h6g inj_on_eq_iff[of "f++g" "A \<union> B" x y]
          by (simp)
      qed
    next
      show "inj_on g B" 
      proof (simp add: inj_on_def)
        apply_end(clarify)
        fix x y
        assume h6a: "x \<in> B"
        hence h6b: "x \<notin> (dom f)" using h1 h2 h3 by auto
        from h6a have h6c: "x \<in> A \<union> B" by auto
        assume h6d: "y \<in> B"
        hence h6e: "y \<notin> (dom f)" using h1 h2 h3 by auto
        assume h6f: "g x = g y"
        from h6b h6e h6f h3 have h6g: "(f++g) x = (f++g) y"
          by (simp add: map_add_app_disj)
        from h5 show "x = y" 
          using h6a h6b h6c h6d h6e h6f h6g inj_on_eq_iff[of "f++g" "A \<union> B" x y]
          by (simp)
      qed
    qed
  next
    apply_end(clarify)
    assume h4a: "inj_on f A"
    assume h4b: "inj_on g B"
    show "inj_on (f ++ g) (A \<union> B)"
    proof (simp add: inj_on_def)
      apply_end(clarify)
      fix x y
      assume h5a: "x \<in> A \<union> B"
      assume h5b: "y \<in> A \<union> B"
      assume h5c: "(f ++ g) x = (f ++ g) y"
      from h5a show "x = y"
      proof 
        assume h6a: "x \<in> A"
        hence h6b: "x \<in> (dom f)" using h1 by auto
        from h5b show "x = y"
        proof
          assume h7a: "y \<in> A"
          hence h7b: "y \<in> (dom f)" using h1 by auto
          from h5c h6b h7b h3 have h7c: "f x = f y"
            by (simp add: map_add_app_disj)
          from h7c h4a h6a h7a show "x = y" 
            by (auto simp add: inj_on_def)
        next
          assume h7a: "y \<in> B"
          hence h7b: "y \<notin> (dom f)" using h1 h2 h3 by auto
          from h5c h6b h7b h3 have h7c: "f x = g y"
            by (simp add: map_add_app_disj)
          show "x = y"
          proof (rule ccontr)
            assume h8: "x \<noteq> y"
            from h7c h4 h8 h6b show "False" by (auto intro!: ranI domI)
          qed
        qed
      next
        assume h6a: "x \<in> B"
        hence h6b: "x \<notin> dom f" using h1 h2 h3 by auto
        from h5b show "x = y"
        proof
          assume h7a: "y \<in> A"
          hence h7b: "y \<in> (dom f)" using h1 by auto
          from h5c h6b h7b h3 have h7c: "g x = f y"
            by (simp add: map_add_app_disj)
          show "x = y"
          proof (rule ccontr)
            assume h8: "x \<noteq> y"
            from h7c h4 h8 h7b show "False" by (auto intro!: ranI domI)
          qed
        next
          assume h7a: "y \<in> B" 
          hence h7b: "y \<notin> (dom f)" using h1 h2 h3 by auto
          from h5c h6b h7b h3 have h7c: "g x = g y"
            by (simp add: map_add_app_disj)
          from h7c h4b h6a h7a show "x = y" 
            by (auto simp add: inj_on_def)
        qed
      qed
    qed
 qed

lemma map_of_zip_eq:
  shows "map_of (zip L1 L2) = (\<lambda> x. (if x \<in> set L1 then (nth_opt L2 (the(pos L1 x))) else None))"
  proof -
    show ?thesis
    proof (induct L1 L2 rule:list_induct2', simp)
      fix a L1'
      show "map_of (zip (a # L1') []) =
        (\<lambda>x. if x \<in> set (a # L1') then nth_opt [] (the (pos (a # L1') x)) else None)"
      by auto
    next
      fix a' L2'
      show "map_of (zip [] (a' # L2')) = (\<lambda>x. if x \<in> set [] then nth_opt (a' # L2') (the (pos [] x)) else None)"
        by auto
    next
      fix a a' L1' L2'
      assume "map_of (zip L1' L2') = (\<lambda>x. if x \<in> set L1' then nth_opt L2' (the (pos L1' x)) else None)"
      then show "map_of (zip (a # L1') (a' # L2')) =
       (\<lambda>xa. if xa \<in> set (a # L1') then nth_opt (a' # L2') (the (pos (a # L1') xa)) else None)"
       by (auto simp add: the_pos_in fun_eq_iff)
    qed
  qed

end
