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
    by (metis card_empty card_insert_disjoint distinct_card finite.emptyI h1 h2 
      insert_absorb insert_not_empty length_0_conv length_Suc_conv the_elem_eq the_elem_set)

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

primrec nth_opt:: "'a list => nat => 'a option"
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

(*List concatenation *)
(*lemma setConcatEqUnion:"set(l1@l2) = set(l1) \<union> set(l2)"
  
lemma "(x, y) \<in> set(l1@l2) \<longleftrightarrow> (x, y) \<in> (set l1) \<or> (x, y) \<in> (set l2)"
proof
  assume "(x, y) \<in> set (l1 @ l2)"
  then show "(x, y) \<in> set l1 \<or> (x, y) \<in> set l2"
  by (simp)*)
lemma set_list_inv_eq: "(set l)\<inverse> = set (zip (map snd l) (map fst l))"
  by (induct l) auto  

value "pos [] 2"
value "pos [''1'', ''2'', ''3''] ''4''"
value "enum [1, 2, 3]"
value "nth [1,2,3] 0"
value "nth_opt [1,2,3] 0"
value "nth_opt [] 1"

end