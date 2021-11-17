theory Set_Extra
imports Main
begin

primrec disjoint_aux :: "'a set \<Rightarrow>('a set) list \<Rightarrow>bool"
where
  disjoint_aux_base: "disjoint_aux A [] \<longleftrightarrow> True" |
  disjoint_aux_induct: "disjoint_aux A (B#Xs) \<longleftrightarrow> A \<inter> B = {} \<and> disjoint_aux A Xs"

primrec disjoint :: "('a set) list \<Rightarrow>bool"
where
  disjoint_base: "disjoint [] \<longleftrightarrow> True" |
  disjoint_induct:  "disjoint (A#Xs) \<longleftrightarrow> disjoint_aux A Xs \<and> disjoint Xs"

lemma disjoint_sym: "disjoint [A, B] = disjoint [B, A]"
   proof 
    assume "disjoint [A, B]"
    then show "disjoint [B, A]"
      by (auto simp add: disjoint_def)
   next
    assume "disjoint [B, A]"
    then show "disjoint [A, B]"
      by (simp add: disjoint_def, blast)
   qed

lemma disjoint_bin[simp]: "(disjoint [A, B]) = (A \<inter> B = {})"
  by (auto simp add: disjoint_def)

(*definition set_to_ls :: "'a set \<Rightarrow>'a list"
where
  "set_to_ls s \<equiv> (SOME l. set l = s)"

lemma set_set_to_ls:
   "finite s \<Longrightarrow> set (set_to_ls s) = s"
   unfolding set_to_ls_def by (metis (mono_tags) finite_list some_eq_ex)

lemma set_to_ls_empty[simp]: "set_to_ls {} = []"
  by (auto simp add: set_to_ls_def)

primrec insert_allL :: "'a list \<Rightarrow>('a set) \<Rightarrow>('a set)"
where
  "insert_allL [] A = A" |
  "insert_allL (e#es) A = insert e (insert_allL es A)"

lemma insert_one: "insert_allL [a] A = insert a A"
  by auto

definition insert_all :: "'a set \<Rightarrow>('a set) \<Rightarrow>('a set)"
where
  "insert_all es A \<equiv> insert_allL (set_to_ls es) A"

lemma insert_all_thm: 
  assumes "A = set lA"
  shows "A \<union> B = insert_allL lA B"
  using assms by (induction) auto*)

end