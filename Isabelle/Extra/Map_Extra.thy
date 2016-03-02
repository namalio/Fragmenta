theory Map_Extra
imports Main List_Extra
begin

(*Converts a partial function (a map in Isabelle) to a relation*)
definition pfunToRel:: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<times>'b) set"
where
  "pfunToRel f \<equiv> {(x, y). f x = Some y}"

lemma pfunToRelEmpty[simp]: "pfunToRel empty = {}"
  by (simp add: pfunToRel_def)

lemma pfunToRelSing: "pfunToRel [a\<mapsto>b] = {(a, b)}"
  by (auto simp add: pfunToRel_def split: if_splits)

definition ftotal_on::"('a\<rightharpoonup>'b)\<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool"
where
  "ftotal_on f A B \<equiv> dom f = A \<and> ran f \<subseteq> B"

lemma ftotal_on_dom: "ftotal_on f A B \<Longrightarrow> dom f = A"
  by (auto simp add: ftotal_on_def)

lemma ftotal_on_ran: "ftotal_on f A B \<Longrightarrow> ran f \<subseteq> B"
  by (auto simp add: ftotal_on_def)

lemma app_ftotal: "ftotal_on f A B \<Longrightarrow> x \<in> A \<Longrightarrow> \<exists> y. f x = Some y"
  by (auto simp add: ftotal_on_def dom_def)

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

(*lemma map_add_disj_domg: 
  assumes "x \<in> dom g"
  shows "(f++g)x = g x"
  proof -
    fix x
    from assms show ?thesis
      by (auto simp add: map_add_def split: option.splits)
  qed*)

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

lemma map_add_restrict_dist: "(f++g)|`A = f|`A ++ g|`A"
  proof
    fix x
    show "((f ++ g) |` A) x = (f |` A ++ g |` A) x"
      by (simp add: restrict_map_def map_add_def)
  qed

lemma map_add_image_dist: 
  assumes h1: "A \<subseteq> dom f" and h2: "dom f \<inter> dom g = {}"
  shows "(f++g)`A = f`A"
  using h1 h2 by (auto simp add: image_def map_add_def split: option.splits)

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

lemma ran_map_add_dist[simp]:
  assumes "dom f \<inter> dom g = {}"
  shows "ran (f++g) = ran f \<union> ran g"
  proof
    show "ran (f++g) \<subseteq> ran f \<union> ran g"
      by (auto simp add: map_add_def ran_def split: option.split)
  next
    show "ran f \<union> ran g \<subseteq> ran (f ++ g)"
    proof
      fix x
      assume h2: "x \<in> ran f \<union> ran g"
      have h2a: "x \<in> ran f \<or> x \<in> ran g" using h2 by (simp)
      show "x \<in> ran (f ++ g)"
      proof (case_tac "x \<in> ran f")
        assume h3: "x \<in> ran f"
        from assms show "x \<in> ran (f ++ g)" 
          using h3 by (auto simp add: ran_def dom_def map_add_def split: option.split)
      next
        assume h3: "x \<notin> ran f"
        have h3a: "x \<in> ran g" using h3 h2a by (simp) 
        from assms show "x \<in> ran (f ++ g)" 
          using h3 h3a by (auto simp add: ran_def dom_def map_add_def split: option.split)
     qed
  qed
qed

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
  proof
    fix x
    assume h1: "x \<in> ran (f |` A)"
    then show "x \<in> ran f" by (auto simp add: restrict_map_def ran_def split: if_splits)
  qed

lemma ran_restrict_in: 
  assumes "x \<in> ran (f |`A)"
  shows "x \<in> ran f"
  proof -
    from assms show ?thesis
      using ran_restrict_sub[where f="f" and A="A"]
      by (auto)
  qed

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

lemma disj_fun_vimage_Un:
  assumes h1: "B \<inter> dom f = {}" and h2: "A \<subseteq> dom f"
  shows "f|`(A\<union>B) = f |`A"
  proof -
    show ?thesis
    proof
      fix x
      show "(f |` (A \<union> B)) x = (f |` A) x"
      proof (case_tac "x \<in> A")
        assume h3: "x \<in> A"
        show "(f |` (A \<union> B)) x = (f |` A) x"
        proof (case_tac "x \<in> B")
          assume h4: "x \<in> B"
          from h1 h2 h3 h4 show "(f |` (A \<union> B)) x = (f |` A) x"
          by (auto simp add: restrict_map_def)
        next
          assume h4: "\<not> x \<in> B"
          from h1 h2 h3 h4 show "(f |` (A \<union> B)) x = (f |` A) x"
          by (auto simp add: restrict_map_def)
        qed
      next
        assume h3: "\<not> x \<in> A"
        from h1 h2 h3 show "(f |` (A \<union> B)) x = (f |` A) x"
        by (auto simp add: restrict_map_def)
      qed
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
