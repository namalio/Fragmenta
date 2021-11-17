theory List_Extra
imports Main
begin

definition enum :: "'a list => ('a \<times> nat) list" where
  "enum xs = zip xs [0..<length xs]"

(*primrec find_fst_in_pair_ls :: "('a \<times> nat) list => 'a \<Rightarrow> ('a \<times> nat)"
where
   "find_fst_in_pair_ls []

primrec pos :: "'a list => 'a \<Rightarrow> nat" 
where
  "pos [] e = 0"
  | "pos (a#l) e = (if a = e then 1 else pos l e)"

(*    (let n = (pos ls e) in
      (if n > 0 then 1 + n else 0)))"*)

value "enum [1, 2]"
value "pos [1, 2] 1"*)


lemma singSet_eq_singL:
  assumes h1: "{a} = set L" and h2: "distinct L"
  shows "L = [a]"
  by (metis distinct_insert distinct_length_2_or_more h1 h2 
    in_set_insert insertI1 insert_Nil neq_Nil_conv 
    not_in_set_insert singletonD)
  

lemma fold_union: "fold union LS S = S \<union> fold union LS {}"
  by (metis Sup_set_fold Un_empty_right Union_insert fold_simps(2) list.simps(15))

lemma fold_big_union: "fold union LS S = (\<Union>x\<in>set (LS). x) \<union> S"
  by (metis SUP_identity_eq Sup_set_fold fold_union sup.commute)

primrec pos0 :: "'a list => 'a \<Rightarrow> nat" 
where
  "pos0 [] e = Suc 0"
  | "pos0 (a#l) e = (if a = e then 0 else Suc(pos0 l e))"

definition pos :: "'a list => 'a \<Rightarrow> nat option"
where
  "pos l e \<equiv> (if (pos0 l e)\<ge> length l then None else Some (pos0 l e))"

primrec nth_opt:: "'a list \<Rightarrow> nat \<Rightarrow> 'a option"
where
  "nth_opt [] n = None" |
  "nth_opt (x#xs) n  = (case n of 0 => Some x | Suc k => nth_opt xs k)"

lemma pos_hd[simp]: "pos (a#l) a = Some 0"
  by (induct l, simp_all add: pos_def)

lemma pos0_of_in_lt_length:
  assumes h1: "x \<in> (set l)"
  shows "(pos0 l x) < length l"
  proof -
    from h1 show ?thesis
    proof (induct l, simp)
      fix a l
      assume h2: "x \<in> set l \<Longrightarrow> pos0 l x < length l"
      and h3: "x \<in> set (a # l)"
      then show "pos0 (a # l) x < length (a # l)"
      proof (case_tac "x = a")
        assume "x = a"
        then show "pos0 (a # l) x < length (a # l)"
          by auto
      next
        assume "x \<noteq> a"
        then show "pos0 (a # l) x < length (a # l)"
          using h2 h3 by auto
      qed
    qed
  qed

lemma the_pos_in: 
  assumes h1: "x \<in> (set l)"
  shows "the(pos l x) = pos0 l x"
  proof -
    from h1 show ?thesis
    proof (induct l, simp)
      fix a' l'
      assume h2: "(x \<in> set l' \<Longrightarrow> the (pos l' x) = pos0 l' x)"
        and h3: "x \<in> set (a' # l')"
      then show "the (pos (a' # l') x) = pos0 (a' # l') x"
      proof (case_tac "x = a'")
        assume "x = a'"
        then show "the (pos (a' # l') x) = pos0 (a' # l') x"
        by (simp)
      next
        assume "x \<noteq> a'" 
        then show "the (pos (a' # l') x) = pos0 (a' # l') x"
        using h2 h3 pos0_of_in_lt_length[of "x" "l'"] by (simp add: pos_def )
      qed
    qed
  qed

lemma pos_map_fst: 
  assumes h1: "x \<in> (set l)" and h2: "distinct (map fst l)"
  shows "pos0 (map fst l) (fst x) = pos0 l x"
  proof -
    from assms show ?thesis
    proof (induct l, simp)
      fix a l
      assume h3: "x \<in> set l \<Longrightarrow> distinct (map fst l) 
        \<Longrightarrow> pos0 (map fst l) (fst x) = pos0 l x"
      and h4: "x \<in> set (a # l)"
      and h5: "distinct (map fst (a # l))"
      then show "pos0 (map fst (a # l)) (fst x) = pos0 (a # l) x"
      proof (case_tac "x=a")
        assume "x=a"
        then show "pos0 (map fst (a # l)) (fst x) = pos0 (a # l) x"
        by auto
      next
        assume "x\<noteq>a"
        then show "pos0 (map fst (a # l)) (fst x) = pos0 (a # l) x"
        using h3 h4 h5 by (auto)
      qed
    qed
  qed

lemma the_pos_map: 
  assumes h1: "x \<in> (set l)" 
  shows "the(pos (map fst l) (fst x)) = pos0 (map fst l) (fst x)"
  proof -
    from h1 show ?thesis
    proof (induct l, simp)
      fix a l 
      assume h2: "x \<in> set l \<Longrightarrow> the (pos (map fst l) (fst x)) = pos0 (map fst l) (fst x)"
        and h3: "x \<in> set (a # l)"
      then show "the (pos (map fst (a # l)) (fst x)) = pos0 (map fst (a # l)) (fst x)"
      proof (case_tac "x = a")
        assume "x = a"
        then show "the (pos (map fst (a # l)) (fst x)) = pos0 (map fst (a # l)) (fst x)"
          by (simp)
      next
        assume "x \<noteq> a"
        then have h4: "x \<in> set l" using h3 by auto
        then have "fst x \<in> set(map fst l)" by simp
        from h4 have "fst x \<in> set (map fst (a # l))" by simp
        then show "the (pos (map fst (a # l)) (fst x)) = pos0 (map fst (a # l)) (fst x)"
          using h2 h3 by (simp only: the_pos_in)
      qed
    qed
  qed

lemma the_nth_opt_in:
  assumes "n < length l"
  shows "the (nth_opt l n) = l!n"
  proof -
    from assms show ?thesis
    proof (induct l arbitrary:n, simp)
      fix a l n
      assume h1: "\<And>n. n < length l \<Longrightarrow> the (nth_opt l n) = l ! n"
      and h2: "n < length (a # l)"
      then show "the (nth_opt (a # l) n) = (a # l) ! n"
      proof (case_tac "n = 0")
        assume "n = 0"
        then show "the (nth_opt (a # l) n) = (a # l) ! n"
          by (simp)
      next
        assume h3: "n \<noteq> 0" 
        then show "the (nth_opt (a # l) n) = (a # l) ! n"
        using h1[of "n-1"] h2 by (auto split:nat.split)
      qed
    qed
  qed

lemma nth_pos_map_fst:
  assumes "x \<in> (set l)" and "distinct (map fst l)"
  shows "l!pos0(map fst l) (fst x) = x"
proof -
  from assms show ?thesis
  proof (induct l, simp)
    fix a l
    assume h1: "x \<in> set l \<Longrightarrow> distinct (map fst l) \<Longrightarrow> l ! pos0 (map fst l) (fst x) = x"
    and h2: "x \<in> set (a # l)"
    and h3: "distinct (map fst (a # l))"
    then show "(a # l) ! pos0 (map fst (a # l)) (fst x) = x"
    proof (case_tac "x=a")
      assume "x=a"
      then show "(a # l) ! pos0 (map fst (a # l)) (fst x) = x"
        by auto
    next
      assume "x \<noteq> a"
      then show "(a # l) ! pos0 (map fst (a # l)) (fst x) = x"  
        using h1 h2 h3 by (auto simp add: pos_map_fst)
    qed
  qed
qed

fun invert::"('a\<times>'b) list \<Rightarrow> ('b\<times>'a) list"
where
  "invert l = zip (map snd l)(map fst l)"

lemma set_list_inv_eq: "(set l)\<inverse> = set (zip (map snd l) (map fst l))"
  by (induct l) auto

lemma in_invert: "(x, y) \<in> set l = ((y, x) \<in> set (invert l))"
  using set_list_inv_eq by auto

primrec comp_with_pair:: "('a\<times>'b) \<Rightarrow> ('b\<times>'a) list \<Rightarrow> ('a\<times>'a) list"
  where
    "comp_with_pair p [] = []" |
    "comp_with_pair p (p'#l)  = (if snd p = fst p' then (fst p, snd p')#comp_with_pair p l else comp_with_pair p l)"

primrec relcomp_ls:: "('a\<times>'b) list \<Rightarrow> ('b\<times>'a) list \<Rightarrow> ('a\<times>'a) list"
  where
    "relcomp_ls [] l' = []" |
    "relcomp_ls (p#l) l' = (comp_with_pair p l')@(relcomp_ls l l')"

lemma set_ls_cons_is_cup: "set (p # l) = {p} \<union> set l"
  by (induct l) auto

lemma comp_with_pair_eq:
  "set (comp_with_pair p rl) = ({p} O set rl)"
proof
  show "set (comp_with_pair p rl) \<subseteq> {p} O set rl"
  proof (rule subrelI)
    fix x y
    assume "(x, y) \<in> set (comp_with_pair p rl)"
    hence "\<exists> z. (x, z) \<in> {p} \<and> (z, y) \<in> set rl" 
    proof (induct rl) 
      case Nil
      then show ?case by auto
    next
      fix p' rl'
      assume h1: "(x, y) \<in> set (comp_with_pair p rl') \<Longrightarrow> \<exists>z. (x, z) \<in> {p} \<and> (z, y) \<in> set rl'"
        and h2: "(x, y) \<in> set (comp_with_pair p (p' # rl'))"
      show "\<exists>z. (x, z) \<in> {p} \<and> (z, y) \<in> set (p' # rl')"
      proof (case_tac "snd p = fst p'")
        assume h3: "snd p = fst p'"
        hence "(x, y) \<in> {(fst p, snd p')} \<or> (x, y) \<in> set(comp_with_pair p rl')" using h2 by auto
        then show "\<exists>z. (x, z) \<in> {p} \<and> (z, y) \<in> set (p' # rl')"
        proof
          assume "(x, y) \<in> {(fst p, snd p')}"
          hence "\<exists>z. (x, z) \<in> {p} \<and> (z, y) \<in> {p'}"
            by (metis Pair_inject h3 insert_iff prod.collapse singletonD)
          then show "\<exists>z. (x, z) \<in> {p} \<and> (z, y) \<in> set (p' # rl')" by auto
        next
          assume "(x, y) \<in> set (comp_with_pair p rl')"
          hence "\<exists>z. (x, z) \<in> {p} \<and> (z, y) \<in> set rl'" using h1 by simp
          then show "\<exists>z. (x, z) \<in> {p} \<and> (z, y) \<in> set (p' # rl')" by auto
        qed
      next
        assume h4: " snd p \<noteq> fst p'"
        hence "(x, y) \<in> set(comp_with_pair p rl')" using h2 by auto
        hence "\<exists>z. (x, z) \<in> {p} \<and> (z, y) \<in> set rl'" using h1 by simp
        then show "\<exists>z. (x, z) \<in> {p} \<and> (z, y) \<in> set (p' # rl')" by auto
      qed
    qed
    then show "(x, y) \<in> {p} O set rl" by auto
  qed
next
  show "{p} O set rl \<subseteq> set (comp_with_pair p rl)"
  proof (rule subrelI)
    fix x y 
    assume h1: "(x, y) \<in> {p} O set rl"
    hence "x = fst p \<and> (snd p, y) \<in> set rl" by auto
    then show "(x, y) \<in> set (comp_with_pair p rl)" by (induct rl) auto
  qed
qed

lemma relcomp_ls_eq:
  shows "(set rl) O (set rl') = set (relcomp_ls rl rl')"
proof 
  show "set rl O set rl' \<subseteq> set (relcomp_ls rl rl')"
  proof (rule subrelI)
    fix x y
    assume "(x, y) \<in> set rl O set rl'"
    hence "\<exists> z. (x, z) \<in> set rl \<and> (z, y) \<in> set rl'" by auto
    then show "(x, y) \<in> set (relcomp_ls rl rl')"
    proof
      fix z 
      assume "(x, z) \<in> set rl \<and> (z, y) \<in> set rl'"
      then show "(x, y) \<in> set (relcomp_ls rl rl')"
      proof (induct rl)
        case Nil
        then show ?case by auto
      next
        fix p rl2
        assume h: "((x, z) \<in> set rl2 \<and> (z, y) \<in> set rl' \<Longrightarrow> (x, y) \<in> set (relcomp_ls rl2 rl'))"
        assume "(x, z) \<in> set (p # rl2) \<and> (z, y) \<in> set rl'" 
        hence "((x, z) \<in> {p} \<or> (x, z) \<in> set rl2) \<and> (z, y) \<in> set rl'" 
          by (simp add: set_ls_cons_is_cup)
        hence "(x, z) = p \<and> (z, y) \<in> set rl' \<or> (x, z) \<in> set rl2 \<and> (z, y) \<in> set rl'" by auto
        then show "(x, y) \<in> set (relcomp_ls (p # rl2) rl')"
        proof
          assume h1: "(x, z) = p \<and> (z, y) \<in> set rl'"
          hence "(x, y) \<in> set (comp_with_pair (x, z) rl')" by (induct rl') auto
          then show "(x, y) \<in> set (relcomp_ls (p # rl2) rl')" using h1 by auto
        next
          assume "(x, z) \<in> set rl2 \<and> (z, y) \<in> set rl'"
          hence "(x, y) \<in> set (relcomp_ls rl2 rl')" using h by simp
          then show "(x, y) \<in> set (relcomp_ls (p # rl2) rl')" by auto 
        qed
      qed
    qed
  qed
next
  show "set (relcomp_ls rl rl') \<subseteq> set rl O set rl'"
  proof(rule subrelI)
    fix x y
    assume "(x, y) \<in> set (relcomp_ls rl rl')"
    then show "(x, y) \<in> set rl O set rl'"
    proof (induct rl)
      case Nil
      then show ?case by auto
    next
      fix p rl2 
      assume h: "((x, y) \<in> set (relcomp_ls rl2 rl') \<Longrightarrow> (x, y) \<in> set rl2 O set rl')"
      assume "(x, y) \<in> set (relcomp_ls (p # rl2) rl')"
      hence "(x, y) \<in> set(comp_with_pair p rl') \<or> (x, y) \<in> set(relcomp_ls rl2 rl')" by auto
      then show "(x, y) \<in> set (p # rl2) O set rl'"
      proof
        assume "(x, y) \<in> set (comp_with_pair p rl')"
        hence "(x, y) \<in> ({p} O set rl')" by (simp add: comp_with_pair_eq)
        then show "(x, y) \<in> set (p # rl2) O set rl'" by auto
      next
        assume "(x, y) \<in> set (relcomp_ls rl2 rl')"
        hence "(x, y) \<in> set rl2 O set rl'" using h by simp
        then show "(x, y) \<in> set (p # rl2) O set rl'" by auto
      qed
    qed
  qed
qed

end