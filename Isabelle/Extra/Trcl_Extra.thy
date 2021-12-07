theory Trcl_Extra
imports Main Rel_Extra Set_Extra

begin

lemma rtrancl_id[simp]: "Id\<^sup>* = Id"
proof (rule equalityI)
  show "Id\<^sup>* \<subseteq> Id"
  proof (rule subrelI)
    fix x y
    assume "(x, y) \<in> Id\<^sup>*"
    then show "(x, y) \<in> Id"
    by (induct) simp_all
 qed
 next 
    show "Id \<subseteq> Id^*"
    proof (rule subrelI)
    fix x y
    assume "(x, y) \<in> Id"
    then show "(x, y) \<in> Id^*"
    by (auto) 
    qed
qed

theorem rtrancl_subsetid: 
  assumes "r \<subseteq> Id"
  shows "r\<^sup>* = Id"
proof 
  show "r\<^sup>* \<subseteq>  Id"
  proof (rule subrelI)
    fix x y
    assume "(x, y) \<in> r\<^sup>*"
    then show "(x, y) \<in> Id"
    using assms by (induct) blast+
  qed
  next
  show "Id \<subseteq> r^*" by blast
qed

theorem rtrancl_minus_subsetid:
  assumes "s \<subseteq> Id"
  shows "(r-s)\<^sup>* = r\<^sup>*"
proof (rule sym)
  show "r\<^sup>* = (r-s)\<^sup>*"
  proof (rule rtrancl_subset)
    show "r-s \<subseteq> r" by blast
  next
  show "r \<subseteq> (r - s)\<^sup>*"
  proof (rule subrelI)
    fix x y
    assume "(x, y) \<in> r"
    then show "(x, y) \<in> (r-s)\<^sup>*"
    using assms by (induct) blast
 qed
 qed
qed

lemma rtrancl_unfold_Id: "(r \<union> s\<^sup>=)\<^sup>* = (r \<union> s)\<^sup>*"
  proof -
    have h1: "(r \<union> s\<^sup>=) = r \<union> s \<union> Id"
    by (auto)
    show "(r \<union> s\<^sup>=)\<^sup>* = (r \<union> s)\<^sup>*"
    using h1
    by (simp add: rtrancl_r_diff_Id)
qed

lemma rtrancl_cpm_of_Un_in_Un: "r^* \<subseteq> (r \<union> s)^*"
  using rtrancl_Un_subset[where R="r"] by simp

lemma rtrancl_Un_sym: "(r \<union> s)^* = (s \<union> r)^*"
  proof
    show "(r \<union> s)\<^sup>* \<subseteq> (s \<union> r)\<^sup>*"
    proof (rule subrelI)
      fix x y
      assume "(x, y) \<in> (r \<union> s)\<^sup>*"
      then show "(x, y) \<in> (s \<union> r)\<^sup>*"
      proof (induct) 
        show "(x, x) \<in> (s \<union> r)\<^sup>*" by simp
      next
        fix y z
        assume h1: "(x, y) \<in> (r \<union> s)\<^sup>*"
        assume h2: "(y, z) \<in> r \<union> s" 
        from h2 have h2a: "(y, z) \<in> s \<union> r" by auto
        assume h3: "(x, y) \<in> (s \<union> r)\<^sup>*"
        from h1 h2a h3 show "(x, z) \<in> (s \<union> r)\<^sup>*" by (simp add: rtrancl_into_rtrancl)
      qed
    qed
  next
    show "(s \<union> r)\<^sup>* \<subseteq> (r \<union> s)\<^sup>*" 
    proof (rule subrelI)
      fix x y
      assume "(x, y) \<in> (s \<union> r)\<^sup>*"
      then show "(x, y) \<in> (r \<union> s)\<^sup>*"
      proof (induct) 
        show "(x, x) \<in> (r \<union> s)\<^sup>*" by simp
      next
        fix y z
        assume h1: "(x, y) \<in> (s \<union> r)\<^sup>*"
        assume h2: "(y, z) \<in> s \<union> r" 
        from h2 have h2a: "(y, z) \<in> r \<union> s" by auto
        assume h3: "(x, y) \<in> (r \<union> s)\<^sup>*"
        from h1 h2a h3 show "(x, z) \<in> (r \<union> s)\<^sup>*" by (simp add: rtrancl_into_rtrancl)
      qed
    qed  
 qed  

lemma in_rel_in_field: "(x, y) \<in> r \<Longrightarrow> x \<in> Field r \<and> y \<in> Field r"
  by (auto simp add: Field_def)

lemma not_in_field_not_in_rel: "x \<notin> Field r \<or> y \<notin> Field r \<Longrightarrow> (x, y) \<notin> r"
  by (auto simp add: in_rel_in_field)

lemma in_trancl_in_field: "(x, y) \<in> r\<^sup>+ \<Longrightarrow> x \<in> Field r \<and> y \<in> Field r"
proof - 
  assume "(x, y) \<in> r\<^sup>+"
  then show "x \<in> Field r \<and> y \<in> Field r"
  proof (induct)
    case base
    fix x y
    assume "(x, y) \<in> r"
    then show "x \<in> Field r \<and> y \<in> Field r" by (simp add: in_rel_in_field)
  next
    case step
    fix x y z
    show "(x, y) \<in> r\<^sup>+ \<Longrightarrow> (y, z) \<in> r \<Longrightarrow> x \<in> Field r \<and> y \<in> Field r \<Longrightarrow> x \<in> Field r \<and> z \<in> Field r"
    by (simp add: in_rel_in_field)
  qed
qed

(*lemma in_rtrancl_in_field: 
  assumes h1: "(x, y) \<in> r\<^sup>*"
  shows "(x = y) \<or> x \<noteq> y \<and> x \<in> Field r \<and> y \<in> Field r"
proof - 
  from h1 have h2: "(x = y) \<or> x \<noteq> y \<and> (x, y) \<in> r\<^sup>+" 
    by (simp add: rtrancl_eq_or_trancl)
  then show ?thesis
  proof
    assume "(x = y)"
    then show ?thesis by auto
  next
    assume "x \<noteq> y \<and> (x, y) \<in> r\<^sup>+"
    then show ?thesis by (auto simp add: in_trancl_in_field)
  qed
qed*)


lemma in_trancl_in_Domain: 
  assumes "(x, y) \<in> r\<^sup>+"
  shows "x \<in> Domain r"
  proof -
    from assms show ?thesis 
    by (induct) auto
  qed

lemma in_trancl_in_Range: 
  assumes "(x, y) \<in> r\<^sup>+"
  shows "y \<in> Range r"
  using assms by (induct) auto

lemma trcl_parts_in_whole: "(r\<^sup>+ \<union> s\<^sup>+) \<subseteq> (r \<union> s)\<^sup>+"
  proof (rule subrelI)
    fix x y
    assume h1: "(x, y) \<in> (r\<^sup>+ \<union> s\<^sup>+)"
    then show "(x, y) \<in> (r \<union> s)\<^sup>+"
      by (auto simp add: trancl_mono)
  qed
  
lemma trancl_disj_dist_Un: 
  assumes "Field r \<inter> Field s = {}"
  shows "(r \<union> s)\<^sup>+ = r\<^sup>+ \<union> s\<^sup>+"
  proof
    show "(r \<union> s)\<^sup>+ \<subseteq> r\<^sup>+ \<union> s\<^sup>+"
    proof (rule subrelI)
      fix x y
      assume "(x, y) \<in> (r \<union> s)\<^sup>+"
      then show "(x, y) \<in> r\<^sup>+ \<union> s\<^sup>+"
      proof (induct)
        case base
        fix x y
        assume "(x, y) \<in> r \<union> s"
        then show "(x, y) \<in> r\<^sup>+ \<union> s\<^sup>+" by (auto)
      next
        case step
        fix x y z
        assume h2: "(x, y) \<in> (r \<union> s)\<^sup>+" 
        assume h3: "(y, z) \<in> r \<union> s" 
        assume h4: "(x, y) \<in> r\<^sup>+ \<union> s\<^sup>+"
        show "(x, z) \<in> r\<^sup>+ \<union> s\<^sup>+" 
        proof (case_tac "{x, y} \<subseteq> Field r")
          assume h5: "{x, y} \<subseteq> Field r"
          have h6: "(y, z) \<in> r" using h3 assms h5 by (auto simp add: Field_def)
          have h7: "(x, y) \<in> r\<^sup>+" 
            using h4 assms h5 in_trancl_in_field[where r="s" and x="x" and y="y"] 
            by (simp) (erule disjE, auto)
          show "(x, z) \<in> r\<^sup>+ \<union> s\<^sup>+" 
            using h6 h7 h4 by (auto)
        next
          assume h5: "\<not> {x, y} \<subseteq> Field r"
          show "(x, z) \<in> r\<^sup>+ \<union> s\<^sup>+" 
          proof (case_tac "{x, y} \<subseteq> Field s")
            assume h6: "{x, y} \<subseteq> Field s" 
            have h7: "(y, z) \<in> s" using h3 assms h6 by (auto simp add: Field_def)
            have h8: "(x, y) \<in> s\<^sup>+" 
            using h4 assms h6 in_trancl_in_field[where r="r" and x="x" and y="y"] 
              by (simp) (erule disjE, auto)
            show "(x, z) \<in> r\<^sup>+ \<union> s\<^sup>+" 
              using h7 h8 h4 by (simp) (rule disjI2, auto)
          next
            assume h6: "\<not> {x, y} \<subseteq> Field s"
            show "(x, z) \<in> r\<^sup>+ \<union> s\<^sup>+" 
            proof (rule ccontr)
              assume h7: "(x, z) \<notin> r\<^sup>+ \<union> s\<^sup>+"
              have h8: "x \<in> Field (r \<union> s)" 
                using assms h2 in_trancl_in_field[where r="r \<union> s"] by (simp)
              then show "False"
                using h5 h6 h7 h3 h4 h8 
                  in_trancl_in_field[where r="r" and x="x" and y="y"] 
                  in_trancl_in_field[where r="s" and x="x" and y="y"] by (auto)
            qed
          qed
        qed
      qed
    qed
  next
  show "r\<^sup>+ \<union> s\<^sup>+ \<subseteq> (r \<union> s)\<^sup>+"
    by (simp only: trcl_parts_in_whole)
qed

lemma rtrancl_disj_dist_Un: 
  assumes "Field r \<inter> Field s = {}"
  shows "(r \<union> s)\<^sup>* = r\<^sup>* \<union> s\<^sup>*"
  using assms 
  by (auto simp add: rtrancl_eq_or_trancl trancl_disj_dist_Un)

lemma trancl_disj_dist_Un_2: 
  assumes h1: "Domain r \<inter> Domain s = {}" and h2: "Range s  \<inter> Domain r = {}"
  shows "(r \<union> s)\<^sup>+ = r\<^sup>+ \<union> s\<^sup>+ \<union> (r\<^sup>+ O Range r \<lhd> s\<^sup>+)"
  proof
    show "(r \<union> s)\<^sup>+ \<subseteq> r\<^sup>+ \<union> s\<^sup>+ \<union> (r\<^sup>+ O Range r \<lhd> s\<^sup>+)"
    proof (rule subrelI)
      fix x y
      assume "(x, y) \<in> (r \<union> s)\<^sup>+"
      then show "(x, y) \<in> r\<^sup>+ \<union> s\<^sup>+ \<union> (r\<^sup>+ O Range r \<lhd> s\<^sup>+)"
      proof (induct)
        case base
        fix x y
        assume "(x, y) \<in> r \<union> s"
        then show "(x, y) \<in> r\<^sup>+ \<union> s\<^sup>+ \<union> (r\<^sup>+ O Range r \<lhd> s\<^sup>+)" by (auto)
      next
        case step
        fix x y z
        assume h3: "(x, y) \<in> (r \<union> s)\<^sup>+" 
        assume h4: "(y, z) \<in> r \<union> s" 
        assume h5: "(x, y) \<in> r\<^sup>+ \<union> s\<^sup>+ \<union> (r\<^sup>+ O Range r \<lhd> s\<^sup>+)"
        show "(x, z) \<in> r\<^sup>+ \<union> s\<^sup>+ \<union> (r\<^sup>+ O Range r \<lhd> s\<^sup>+)" 
        proof (case_tac "{x, y} \<subseteq> Domain r")
          assume h6: "{x, y} \<subseteq> Domain r"
          have h7: "(y, z) \<in> r" using h4 h1 h6 by (auto)
          have h8: "(x, y) \<in> r\<^sup>+ \<union> (r\<^sup>+ O Range r \<lhd> s\<^sup>+)" 
            using h5 h1 h6 in_trancl_in_Domain[where r="s" and x="x" and y="y"] 
            by (simp) (erule disjE, auto simp add: dres_def)
          have h9: "(x, z) \<in> r\<^sup>+ \<union> (r\<^sup>+ O Range r \<lhd> s\<^sup>+)" 
            using h7 h8 h5 h1 h2 by (auto simp add: relcomp_unfold dres_def Field_def 
              intro: in_trancl_in_Domain in_trancl_in_Range)
          show "(x, z) \<in> r\<^sup>+ \<union> s\<^sup>+ \<union> (r\<^sup>+ O Range r \<lhd> s\<^sup>+)" 
            using h9 by auto
        next
            assume h6: "\<not> {x, y} \<subseteq> Domain r"
            show "(x, z) \<in> r\<^sup>+ \<union> s\<^sup>+ \<union> (r\<^sup>+ O Range r \<lhd> s\<^sup>+)" 
            proof (case_tac "{x, y} \<subseteq> Domain s")
              assume h7: "{x, y} \<subseteq> Domain s" 
              have h8: "(y, z) \<in> s" 
                using h4 h1 h7 by (auto)
              from h8 have h8b: "(y, z) \<in> s\<^sup>+"
                by auto
              have h9: "(x, y) \<in> s\<^sup>+ \<union> (r\<^sup>+ O Range r \<lhd> s\<^sup>+)" 
                using h5 h1 h7 in_trancl_in_Domain[where r="r" and x="x" and y="y"] 
                by (simp) (erule disjE, auto simp add: dres_def)
              show "(x, z) \<in> r\<^sup>+ \<union> s\<^sup>+ \<union> (r\<^sup>+ O Range r \<lhd> s\<^sup>+)" 
              using h7 h8b h9 h1 h5 h4
              by (simp)(rule disjI2, auto simp add: relcomp_unfold dres_def)
            next
              assume h7: "\<not> {x, y} \<subseteq> Domain s"
              from h3 have h3a: "(x, y) \<in> (r \<union> s) \<or> (x, y) \<in> (r \<union> s)\<^sup>+O (r \<union> s)"
                using trancl_unfold[where r="r \<union> s"]
                by (auto)
              from h3 show "(x, z) \<in> r\<^sup>+ \<union> s\<^sup>+ \<union> r\<^sup>+ O Range r \<lhd> s\<^sup>+"
                using h6 h7 h4 h5 h2
                  by (auto simp add: dres_def Field_def 
                    intro: in_trancl_in_Domain in_trancl_in_Range)
            qed
          qed
        qed
      qed
    next 
      show "r\<^sup>+ \<union> s\<^sup>+ \<union> r\<^sup>+ O Range r \<lhd> s\<^sup>+ \<subseteq> (r \<union> s)\<^sup>+"
      proof (rule subrelI)
        fix x y
        assume "(x, y) \<in> r\<^sup>+ \<union> s\<^sup>+ \<union> r\<^sup>+ O Range r \<lhd> s\<^sup>+"
        then show "(x, y) \<in> (r \<union> s)\<^sup>+"
        proof 
          assume "(x, y) \<in> r\<^sup>+ \<union> s\<^sup>+"
          then show "(x, y) \<in> (r \<union> s)\<^sup>+"
            by (simp)(erule disjE, auto intro: trancl_mono)
        next
          assume "(x, y) \<in> r\<^sup>+ O Range r \<lhd> s\<^sup>+"
          then show "(x, y) \<in> (r \<union> s)\<^sup>+"
            by (simp add: dres_def relcomp_unfold) (erule exE, 
              subgoal_tac "(x, ya) \<in> (r \<union> s)\<^sup>+ \<and> (ya, y) \<in> (r \<union> s)\<^sup>+", 
              auto intro: trancl_mono)
        qed
    qed
  qed

lemma rtrancl_disj_dist_Un_2: 
  assumes h1: "Domain r \<inter> Domain s = {}" and h2: "Range s  \<inter> Domain r = {}"
  shows "(r \<union> s)\<^sup>* = r\<^sup>* \<union> s\<^sup>* \<union> (r\<^sup>+ O Range r \<lhd> s\<^sup>+)"
    using h1 h2 by (auto simp add: rtrancl_eq_or_trancl trancl_disj_dist_Un_2)

lemma rtrancl_in_Un:
  assumes h1: "x \<in> Domain r" and h2: "x \<notin> Domain s" and h3: "(x, y) \<in> (r \<union> s)\<^sup>*"
    and h4: "Range r  \<inter> Domain s = {}"
  shows "(x, y) \<in> r\<^sup>*"
  proof -
    from h3 show ?thesis
    proof (induct)
      show "(x, x) \<in> r\<^sup>*" by auto
    next
      fix y z
      assume "(x, y) \<in> (r \<union> s)\<^sup>*"
      assume h5a: "(y, z) \<in> r \<union> s"
      assume h5b: "(x, y) \<in> r\<^sup>*"
      from h5a show "(x, z) \<in> r\<^sup>*"
      proof
        assume "(y, z) \<in> r"
        then show "(x, z) \<in> r\<^sup>*" using h5b by auto
      next
        assume h6a: "(y, z) \<in> s"
        from h5b have "x = y \<or> x \<noteq> y \<and> (x, y) \<in> r\<^sup>+" by (simp add: rtrancl_eq_or_trancl)
        then show "(x, z) \<in> r\<^sup>*"
        proof
          assume "x = y"
          then show "(x, z) \<in> r\<^sup>*" using h6a h2 by auto
        next
          assume "x \<noteq> y \<and> (x, y) \<in> r\<^sup>+"
          hence "y \<in> Range(r\<^sup>+)" by (blast)
          hence h6b: "y \<in> Range r" by (simp)
          from h6a have h6c: "y \<in> Domain s" by auto
          show "(x, z) \<in> r\<^sup>*" using h6c h6b h4 by auto
        qed
      qed
    qed
  qed

(*lemma trancl_disj_dist_Un_2: 
  assumes h1: "\<forall> x y. (x, y) \<in> s \<longrightarrow> (y, x) \<notin> r\<^sup>*"
  shows "(r \<union> s)\<^sup>+ = r\<^sup>+ \<union> s\<^sup>+"
  proof 
    show "(r \<union> s)\<^sup>+ \<subseteq> r\<^sup>+ \<union> s\<^sup>+"
    proof (rule subrelI)
      fix x y
      assume "(x, y) \<in> (r \<union> s)\<^sup>+"
      then show " (x, y) \<in> r\<^sup>+ \<union> s\<^sup>+"
      proof (induct)
        case base
        fix x y
        assume "(x, y) \<in> r \<union> s"
        then show "(x, y) \<in> r\<^sup>+ \<union> s\<^sup>+" by (auto)
      next
        case step
        fix x y z
        assume h2: "(x, y) \<in> (r \<union> s)\<^sup>+" 
        assume h3: "(y, z) \<in> r \<union> s" 
        assume h4: "(x, y) \<in> r\<^sup>+ \<union> s\<^sup>+"
        from h3 have h3a: "(y, z) \<in> r \<or> (y, z) \<in> s" by simp
        from h4 have h4a: "(x, y) \<in> r\<^sup>+ \<or> (x, y) \<in> s\<^sup>+" by simp
        from h3a show "(x, z) \<in> r\<^sup>+ \<union> s\<^sup>+" 
        proof 
          assume h5: "(y, z) \<in> r"
          from h4a show "(x, z) \<in> r\<^sup>+ \<union> s\<^sup>+" 
          proof
            assume "(x, y) \<in> r\<^sup>+"
            hence "(x, z) \<in> r\<^sup>+" using h5 by auto
            then show "(x, z) \<in> r\<^sup>+ \<union> s\<^sup>+" by auto
          next
            assume "(x, y) \<in> s\<^sup>+"
          qed
      qed
  qed *)

lemma trancl_gen_Un: 
shows "(r \<union> s)\<^sup>+ = (r\<^sup>+ \<union> s\<^sup>+)\<^sup>+"
  proof 
    show "(r \<union> s)\<^sup>+ \<subseteq> (r\<^sup>+ \<union> s\<^sup>+)\<^sup>+"
      proof (rule subrelI)
        fix x y 
        assume h1: "(x, y) \<in> (r \<union> s)\<^sup>+"
        then show "(x, y) \<in> (r\<^sup>+ \<union> s\<^sup>+)\<^sup>+"
        proof (induct)
          case base
          fix x y
          assume "(x, y) \<in> r \<union> s"
          then show "(x, y) \<in> (r\<^sup>+ \<union> s\<^sup>+)\<^sup>+" by auto
        next
          case step
          fix x y z
          assume h2: "(y, z) \<in> r \<union> s"
          from h1 h2 have h2a: "(y, z) \<in> r\<^sup>+ \<union> s\<^sup>+" 
            by auto
          assume h3: "(x, y) \<in> (r\<^sup>+ \<union> s\<^sup>+)\<^sup>+"
          from h2a h3 show "(x, z) \<in> (r\<^sup>+ \<union> s\<^sup>+)\<^sup>+"
            by (simp add: trancl_into_trancl)
        qed
      qed
  next
    show "(r\<^sup>+ \<union> s\<^sup>+)\<^sup>+ \<subseteq> (r \<union> s)\<^sup>+"
    proof (rule subrelI)
      fix x y
      assume h1: "(x, y) \<in> (r\<^sup>+ \<union> s\<^sup>+)\<^sup>+"
      then show "(x, y) \<in> (r \<union> s)\<^sup>+"
      proof (induct)
        case base
        fix x y
        assume h2: "(x, y) \<in> r\<^sup>+ \<union> s\<^sup>+"
        then show "(x, y) \<in> (r \<union> s)\<^sup>+" 
          by (auto simp add: trancl_mono)
      next 
        case step
        fix x y z
        assume h2: "(y, z) \<in> r\<^sup>+ \<union> s\<^sup>+"
        from h2 have h2a: "(y, z) \<in> (r \<union> s)\<^sup>+" 
          by (auto simp add: trancl_mono)
        assume h3: "(x, y) \<in> (r \<union> s)\<^sup>+"
        from h2a h3 show "(x, z) \<in> (r \<union> s)\<^sup>+" 
          by auto
      qed
    qed
  qed


definition is_reachable_from_in :: "('a\<times>'a) \<Rightarrow> ('a\<times>'a) \<Rightarrow> ('a\<times>'a) set \<Rightarrow> bool"
where
  "is_reachable_from_in p1 p2 r \<equiv> ((fst p1, fst p2) \<in> r\<^sup>+ \<or> fst p1= fst p2) 
    \<and> ((snd p1, snd p2) \<in> r\<^sup>+ \<or> snd p1= snd p2)"

lemma in_trcl_is_reachable: 
   assumes h1: "(x, y) \<in> r\<^sup>+"
   shows "\<exists> w z. is_reachable_from_in (x, y) (w, z) r"
   proof -
    from h1 have h1a: "(x, y) \<in> r \<or> (x, y) \<in> r\<^sup>+O r"
      using trancl_unfold[where r="r"] by auto
    from h1a show ?thesis
    proof
      assume h2: "(x, y) \<in> r"
      from h2 show ?thesis
        by (simp add: is_reachable_from_in_def) (rule conjI, rule exI[where x="x"], simp, 
            rule exI[where x="y"], simp)
    next
      assume h2: "(x, y) \<in> r\<^sup>+ O r"
      from h2 have h2a: "\<exists> z. (x, z) \<in> r\<^sup>+ \<and> (z, y) \<in> r"
        by auto
      from h2a show ?thesis
      proof
        apply_end(clarify)
        fix z
        assume h3: "(x, z) \<in> r\<^sup>+"
        assume h4: "(z, y) \<in> r"
        from h4 have h4a: "(z, y) \<in> r\<^sup>+" by auto
        from h3 h4a show ?thesis
          by (simp add: is_reachable_from_in_def)
          (rule conjI, rule exI[where x="z"], simp, rule exI[where x="y"], simp)
      qed
    qed
qed

definition reachable_from :: "('a\<times>'a) set \<Rightarrow> ('a\<times>'a) \<Rightarrow> ('a\<times>'a) set"
where
  "reachable_from r p \<equiv> {(a, b). (fst p, a) \<in> r\<^sup>* \<and> (snd p, b) \<in> r\<^sup>*}"

lemma acyclic_disj_dist: 
  assumes h1: "Field r \<inter> Field s = {}"
  shows "acyclic (r \<union> s) = (acyclic r \<and> acyclic s)"
  proof -
    show ?thesis
    proof
      assume "acyclic (r \<union> s)"
      then show "acyclic r \<and> acyclic s"
        by (simp add: acyclic_subset)
    next
      show "acyclic r \<and> acyclic s \<Longrightarrow> acyclic (r \<union> s)"
        using h1 by (simp add: acyclic_def trancl_disj_dist_Un)
    qed
  qed

lemma acyclic_Un:
  assumes h1: "acyclic r" and h2: "acyclic s"
    and h3: "Domain r \<inter> Domain s = {}" and h4: "Range s \<inter> Domain r = {}"
  shows "acyclic (r \<union> s)"
  proof -
    show ?thesis
    proof (rule ccontr)
      assume h5: "\<not> acyclic (r \<union> s)"
      from h5 have h5a: "\<exists> x. (x, x) \<in> (r \<union> s)\<^sup>+"  by (simp add: acyclic_def)
      from h5a h3 h4 have h5b: "\<exists> x. (x, x) \<in> r\<^sup>+ \<union> s\<^sup>+ \<union> (r\<^sup>+ O Range r \<lhd> s\<^sup>+)"
        by (simp add: trancl_disj_dist_Un_2)
      from h5b show "False"
      proof
        apply_end(simp)
        fix x
        assume h6: "(x, x) \<in> r\<^sup>+ \<or> (x, x) \<in> s\<^sup>+ \<or> (x, x) \<in> r\<^sup>+ O Range r \<lhd> s\<^sup>+"
        from h6 show "False"
        proof
          assume "(x, x) \<in> r\<^sup>+"
          then show "False" using h1 by (simp add: acyclic_def)
        next
          apply_end(erule disjE)
          assume "(x, x) \<in> s\<^sup>+"
          then show "False" using h2 by (simp add: acyclic_def)
        next
          assume "(x, x) \<in> r\<^sup>+ O Range r \<lhd> s\<^sup>+"
          then show "False" 
            using h4 
            by (auto simp add: relcomp_unfold dres_def Field_def 
              intro: in_trancl_in_Range in_trancl_in_Domain)
        qed
      qed
    qed
  qed

lemma rel_subset_acyclic_trcl:
  assumes h1: "acyclic s" and h2: "r \<subseteq> s\<^sup>+"
  shows "acyclic r"
  proof -
    from assms show ?thesis
    proof (simp add: acyclic_def)
      apply_end(rule allI)
      fix x
      assume "\<forall>x. (x, x) \<notin> s\<^sup>+"
      hence h3: "(x, x) \<notin> s\<^sup>+" by (frule_tac spec[where x="x"], auto)
      from h2 h3 have h4:"(x, x) \<notin> r" by auto
      show "(x, x) \<notin> r\<^sup>+" 
      proof (rule ccontr)
        apply_end(simp)
        assume "(x, x) \<in> r\<^sup>+"
        hence "(x, x) \<in> (s\<^sup>+)\<^sup>+" using h2 by (simp only: trancl_mono)
        hence h5: "(x, x) \<in> s\<^sup>+" by simp
        from h3 h5 show "False" by simp
      qed
    qed
 qed

definition rel1:: "(nat\<times>nat) set"
where
  "rel1 \<equiv> {(1::nat, 2), (2, 3), (3, 4)}"

definition rel2:: "(nat\<times>nat) set"
where
  "rel2 \<equiv> {(5::nat, 6), (6, 7), (7, 3)}"

lemma "{3} = Field rel1 \<inter> Field rel2"
  by (auto simp add: rel1_def rel2_def)

lemma "(7::nat, 3) \<in> at_intersec_rel rel1 rel2"
  by (simp add: at_intersec_rel_def rel1_def rel2_def dres_def rres_def)

lemma "at_intersec_rel rel1 rel2 = {(7::nat, 3), (2, 3), (3, 4)}"
  proof
    show "at_intersec_rel rel1 rel2 \<subseteq> {(7, 3), (2, 3), (3, 4)}"
      by (rule subrelI)(auto simp add: at_intersec_rel_def rel1_def rel2_def dres_def rres_def)
  next
    show "{(7, 3), (2, 3), (3, 4)} \<subseteq> at_intersec_rel rel1 rel2"
      by (simp add: at_intersec_rel_def rel1_def rel2_def dres_def rres_def)
  qed

lemma single_valued_relcomp:
  assumes h1: "single_valued r"
  shows "single_valued (r O r)"
  proof -
    from assms show ?thesis
    proof (simp add: relcomp_unfold single_valued_def)
      apply_end(clarify)
      fix x y1 y2 y y'
      assume h2a: "(x, y) \<in> r"
      assume h2b: "(y, y1) \<in> r"
      assume h2c: "(x, y') \<in> r"
      assume h2d: "(y', y2) \<in> r"
      from h2a h2c have "y = y'" using h1 by (auto simp add: single_valued_def)
      then show "y1 = y2" using h2d h2b h1 by (auto simp add: single_valued_def)
    qed
  qed

lemma single_valued_rel_trcl_eq:
  assumes h1: "single_valued r" and h2: "v1 \<notin> (Domain r)" and h3: "v2 \<notin> (Domain r)"
    and h4: "(v, v1) \<in> r\<^sup>+" and h5: "(v, v2) \<in> r\<^sup>+"
  shows "v1 = v2"    
  proof (rule ccontr)
    assume h6a: "v1\<noteq>v2"
    from h4 show "False"
    proof (rule tranclE)
      assume h6b: "(v, v1) \<in> r"
      from h5 show "False"
      proof (rule converse_tranclE)
        assume h7a: "(v, v2) \<in> r"
        from h6b h7a h1 h6a show "False" by (simp add: single_valued_def)
      next
        fix c
        assume h7a: "(v, c) \<in> r"
        assume h7b: "(c, v2) \<in> r\<^sup>+"
        from h7a h6b h1 have "c = v1" by (simp add: single_valued_def)
        hence "v1 \<in> Domain r" using h7b by (auto simp add: Domain_unfold dest: tranclD)
        then show "False" using h2 by simp
      qed
    next
      fix c
      assume h6b: "(v, c) \<in> r\<^sup>+"
      assume h6c: "(c, v1) \<in> r"
      from h6b have h6d: "\<exists> z. (v, z) \<in> r \<and> (z, c) \<in> r\<^sup>*" by (simp add: tranclD)
      from h5 show "False"
      proof (rule tranclE)
        assume h7a: "(v, v2) \<in> r"
        hence "(v2, c) \<in> r\<^sup>*" using h1 h6d by (auto simp add: single_valued_def)
        hence "v2 = c" using h3 by (simp add: Not_Domain_rtrancl)
        hence "v2 \<in> Domain r" using h6c by (auto simp add: Domain_unfold)
        then show "False" using h3 by simp
      next
        fix c'
        assume h7a: "(v, c') \<in> r\<^sup>+"
        assume h7b: "(c', v2) \<in> r"
        show "False"
        proof (case_tac "c = c'")
          assume "c = c'"
          then show "False" using h7b h6c h6a h1 by (simp add: single_valued_def)
        next
          assume h8a: "c \<noteq> c'"
          from h6d show "False"
          proof
            apply_end(clarify)
            fix y
            assume h8b: "(v, y) \<in> r"
            assume h8c: "(y, c) \<in> r\<^sup>*"
            from h7a have "\<exists> z. (v, z) \<in> r \<and> (z, c') \<in> r\<^sup>*" by (simp add: tranclD)
            then show "False"
            proof
              apply_end(clarify)
              fix y2
              assume h8d: "(v, y2) \<in> r"
              assume h8e: "(y2, c') \<in> r\<^sup>*"
              from h8d h8b h8e h1 have "(y, c') \<in> r\<^sup>*" by (auto simp add: single_valued_def)
              hence "(c, c') \<in> r\<^sup>* \<or> (c', c) \<in> r\<^sup>*" 
                using h1 h8c by (simp add: single_valued_confluent)
              then show "False"
              proof
                assume "(c, c') \<in> r\<^sup>*"
                hence "(c, c') \<in> r\<^sup>+" using h8a by (simp add: rtrancl_eq_or_trancl)
                then show "False"
                proof (rule converse_tranclE)
                  assume h8b: "(c, c') \<in> r"
                  hence "(v1, v2) \<in> r" using h7b h6c h1 by (auto simp add: single_valued_def)
                  then show "False" using h2 by (auto simp add: Domain_unfold)
                next
                  fix y
                  assume h8c: "(c, y) \<in> r"
                  assume h8d: "(y, c') \<in> r\<^sup>+"
                  from h8c h6c h1 h8d have "(v1, c') \<in> r\<^sup>+" 
                    by (auto simp add: single_valued_def)
                  hence "(v1, v2) \<in> r\<^sup>+" using h7b by auto
                    then show "False" using h2 by (auto simp add: Domain_unfold dest: tranclD)
                qed
              next
                assume "(c', c) \<in> r\<^sup>*"
                hence "(c', c) \<in> r\<^sup>+" using h8a by (simp add: rtrancl_eq_or_trancl)
                then show "False"
                proof (rule converse_tranclE)
                  assume h8b: "(c', c) \<in> r"
                  hence "(v2, v1) \<in> r" 
                  using h7b h6c h1 by (auto simp add: single_valued_def)
                  then show "False" using h3 by (auto simp add: Domain_unfold)
                next
                  fix y
                  assume h8c: "(c', y) \<in> r"
                  assume h8d: "(y, c) \<in> r\<^sup>+"
                  from h8c h7b h1 h8d have "(v2, c) \<in> r\<^sup>+" 
                    by (auto simp add: single_valued_def)
                  hence "(v2, v1) \<in> r\<^sup>+" using h6c by auto
                  then show "False" using h3 by (auto simp add: Domain_unfold dest: tranclD)
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed

lemma in_rtrcl_in_Range_if_neq:
  assumes "(x, y) \<in> r\<^sup>*" and "x \<noteq> y"
  shows "y \<in> Range r"
  using assms by (auto simp add: Range_iff elim: rtranclE)

lemma in_rtrcl_in_Domain_if_neq:
  assumes "(x, y) \<in> r\<^sup>*" and "x \<noteq> y"
  shows "x \<in> Domain r"
proof (rule ccontr)
  assume "x \<notin> Domain r"
  hence "x = y" 
    using assms(1) by (simp add: Not_Domain_rtrancl)
  then show "False" using assms(2) by auto
qed    
  

end
