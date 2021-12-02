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
  
(*lemma mtotalise_map_add_dist: 
  "mtotalise_in (f++g) (A = (mtotalise_in f A)++(mtotalise_in g A)"*)

(*primrec pfunToListPairs::"('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<times>'b) list"
  where
    "pfunToListPairs Map.empty = []" |
    "pfunToListPairs (f(a\<mapsto>b)) = (a, b)#(pfunToListPairs f)"*)

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

definition mrres::"('a\<rightharpoonup>'b)\<Rightarrow> 'b set \<Rightarrow> ('a\<rightharpoonup>'b)" (infixl "\<rhd>\<^sub>m" 100)
where
  "f \<rhd>\<^sub>m B = (\<lambda>x. if (f x) \<in> Some `B then f x else None)" 

lemma mrres_empty[simp]: "f \<rhd>\<^sub>m {} = Map.empty"
  by (simp add: mrres_def)

lemma mrres_emptyf[simp]: "Map.empty \<rhd>\<^sub>m A = Map.empty"
  by (simp add: mrres_def)

lemma mrres_ran_sub1: "ran(f \<rhd>\<^sub>m A) \<subseteq> A"
  by (auto simp add: mrres_def ran_def)

lemma mrres_ran_sub2: 
  assumes "(ran f) \<subseteq> B"
  shows "ran(f \<rhd>\<^sub>m A) \<subseteq> B"
  using assms
  by (auto simp add: mrres_def ran_def)

definition mdsub::"'a set \<Rightarrow> ('a\<rightharpoonup>'b)\<Rightarrow>('a\<rightharpoonup>'b)" (infixl "\<unlhd>\<^sub>m" 100)
  where
  "A \<unlhd>\<^sub>m f = (\<lambda>x. if x \<in> A then None  else f x)" 

lemma mdsub_empty[simp]: " {} \<unlhd>\<^sub>m f = f"
  by (simp add: mdsub_def)

lemma mdsub_emptyf[simp]: "A \<unlhd>\<^sub>m Map.empty  = Map.empty"
  by (simp add: mdsub_def)

(*definition set_to_ls :: "'a set \<Rightarrow>'a list"
where
  "set_to_ls s \<equiv> (SOME l. set l = s)"

lemma set_set_to_ls:
   "finite s \<Longrightarrow> set (set_to_ls s) = s"
   unfolding set_to_ls_def by (metis (mono_tags) finite_list some_eq_ex)

definition funRelToMap:: "('a \<times>'b) set \<Rightarrow> ('a \<rightharpoonup>'b)"
where
  "funRelToMap r \<equiv> map_of(set_to_ls r)"

theorem "funRelToMap {(1::nat, 2)} = [1\<mapsto>2]"
  by (auto simp add: funRelToMap_def set_to_ls_def)  *)

lemma map_add_disj_domf: 
  assumes h1: "dom f \<inter> dom g = {}"
  shows "x \<in> dom f \<longrightarrow> (f++g)x = f x"
  proof
    fix x
    from assms show "x \<in> dom f \<Longrightarrow> (f ++ g) x = f x"
      by (auto simp add: map_add_def split: option.splits)
  qed

lemma map_add_disj_dom2f: 
  assumes h1: "dom f \<inter> dom g = {}"
  shows "x \<notin> dom g \<longrightarrow> (f++g)x = f x"
  proof
    fix x
    from assms show "x \<notin> dom g \<Longrightarrow> (f ++ g) x = f x"
      by (auto simp add: map_add_def split: option.splits)
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

lemma dom_map_comp_dom_eq_ran:
  assumes "dom f = ran h" 
  shows "dom (f \<circ>\<^sub>m h) = dom h"
  using assms 
  by (auto simp add: map_comp_def dom_def ran_def split: option.splits)

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
      by (metis assms(1) assms(2) h map_add_comm map_add_comp_disj_1 map_add_dom_app_simps(1) map_comp_def)
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



lemma vimage_in_dom:
  assumes h1: "None \<notin> B" and "dom f = A"
  shows "f-`B \<subseteq> A"
  proof
    fix x
    from assms show "x \<in> f -` B \<Longrightarrow> x \<in> A"
    by (auto simp add: vimage_def dom_def)
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
