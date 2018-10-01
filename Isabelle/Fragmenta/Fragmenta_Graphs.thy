(*  Title:      Fragmenta Theory of Graphs
    Description: 'Fragmenta' theory of Graphs as per Models 2015 paper.
    Author:     Nuno Amálio
*)

theory Fragmenta_Graphs
imports Base_Graphs "../Extra/Trcl_Extra"
begin

definition cupG :: "'a Gr_scheme \<Rightarrow> 'a Gr_scheme \<Rightarrow> Gr" (infixl "UG" 100)
where
  "G1 UG G2 \<equiv> \<lparr>Ns = Ns G1 \<union> Ns G2, Es = Es G1 \<union> Es G2, src = src G1 ++ src G2, 
    tgt = tgt G1 ++ tgt G2\<rparr>"

lemma Ns_GUn[simp]: "Ns (G1 UG G2) = Ns G1 \<union> Ns G2"
  by (simp add: cupG_def)

lemma Es_GUn[simp]: "Es (G1 UG G2) = Es G1 \<union> Es G2"
  by (simp add: cupG_def)

lemma src_GUn[simp]: "src (G1 UG G2) = src G1 ++ src G2"
  by (simp add: cupG_def)

lemma tgt_GUn[simp]: "tgt (G1 UG G2) = tgt G1 ++ tgt G2"
  by (simp add: cupG_def)

definition disjEsGs :: "'a Gr_scheme \<Rightarrow> 'a Gr_scheme \<Rightarrow> bool" 
where
  "disjEsGs G1 G2 \<equiv> disjoint [(Es G1),(Es G2)]"

lemma disjEsGs_sym:"disjEsGs G1 G2 = disjEsGs G2 G1"
  by (auto simp add: disjEsGs_def disjoint_sym)

definition disjGs :: "'a Gr_scheme \<Rightarrow> 'a Gr_scheme \<Rightarrow> bool" 
where
  "disjGs G1 G2 \<equiv> disjoint[(Ns G1), (Ns G2), (Es G1), (Es G2)]"

(*primrec disjGsL_aux :: "'a Gr_scheme list \<Rightarrow> string set list"
where
  "disjGsL_aux [] = []"
  | "disjGsL_aux (G#Gs) = [(Ns G), (Es G)]@disjGsL_aux Gs"*)

definition disjGsL :: "'a Gr_scheme list \<Rightarrow> bool" 
where
  "disjGsL Gs \<equiv>  disjoint ((map Ns Gs)@(map Es Gs))"

lemma disjGs_sym:"disjGs G1 G2 = disjGs G2 G1"
  proof
    assume "disjGs G1 G2"
    then show "disjGs G2 G1"
      by (simp add: disjGs_def disjoint_def, blast)
  next
    assume "disjGs G2 G1"
    then show "disjGs G1 G2"
       by (simp add: disjGs_def disjoint_def, blast)
  qed

lemma disjGs_imp_disjEsGs: 
  assumes h1: "disjGs G1 G2"
  shows "disjEsGs G1 G2"
  proof -
    from h1 have h1a: "(Es G1) \<inter> (Es G2) = {}" 
      by (simp add: disjGs_def disjoint_def)
    from h1a show ?thesis
      by (simp add: disjEsGs_def)
  qed

lemma cupG_sym:
  assumes h1: "is_wf_g G1" and h2: "is_wf_g G2" and h3: "disjEsGs G1 G2"
  shows "G1 UG G2 = G2 UG G1"
  proof -
    from h1 have h1a: "dom (src G1) = Es G1" by (simp add: is_wf_g_def ftotal_on_def)
    from h1 have h1b: "dom (tgt G1) = Es G1" by (simp add: is_wf_g_def ftotal_on_def)
    from h2 have h2a: "dom (src G2) = Es G2" by (simp add: is_wf_g_def ftotal_on_def)
    from h2 have h2b: "dom (tgt G2) = Es G2" by (simp add: is_wf_g_def ftotal_on_def)
    from h3 have h3a: "Es G1 \<inter> Es G2 = {}" by (simp add: disjEsGs_def)
    show "G1 UG G2 = G2 UG G1"
    proof (auto simp add: cupG_def)
      show "src G1 ++ src G2 = src G2 ++ src G1"
      proof
        fix x
        show "(src G1 ++ src G2) x = (src G2 ++ src G1) x"
        using h1a h2a h3a by (auto simp add: map_add_def split: option.splits)
      qed
      next
      show "tgt G1 ++ tgt G2 = tgt G2 ++ tgt G1"
      proof
        fix x
        show "(tgt G1 ++ tgt G2) x = (tgt G2 ++ tgt G1) x"
        using h1b h2b h3a by (auto simp add: map_add_def split: option.splits)
      qed
   qed
qed
   
lemma adjacent_dist: "\<lbrakk>is_wf_g G1; is_wf_g G2; disjEsGs G1 G2\<rbrakk> 
  \<Longrightarrow> adjacent x y (G1 UG G2) \<longrightarrow>(adjacent x y G1 \<or> adjacent x y G2)"
proof 
  fix x y
  assume h1: "disjEsGs G1 G2"
  have h1a: "Es G1 \<inter> Es G2 = {}" 
    using h1 by (simp add: disjEsGs_def disjoint_def)
  assume h2: "is_wf_g G1"
  have h2a: "ftotal_on (src G1) (Es G1) (Ns G1)"  
    using h2 by (simp add: is_wf_g_def)
  have h2b: "dom (src G1) = Es G1" 
    using h2a by (simp add: ftotal_on_dom)
  have h2c: "ran (src G1) \<subseteq> Ns G1" 
    using h2a by (simp add: ftotal_on_def)
  have h2d: "ftotal_on (tgt G1) (Es G1) (Ns G1)"  
    using h2 by (simp add: is_wf_g_def)
  have h2e: "ran (tgt G1) \<subseteq> Ns G1" 
    using h2d by (simp add: ftotal_on_def)
  have h2f: "dom (tgt G1) = Es G1" 
    using h2d by (simp add: ftotal_on_dom)
  assume h3: "is_wf_g G2"
  have h3a: "ftotal_on (src G2) (Es G2) (Ns G2)"  
    using h3 by (simp add: is_wf_g_def)
  have h3b: "dom (src G2) = Es G2" 
    using h3a by (simp add: ftotal_on_dom)
  have h3c: "ran (src G2) \<subseteq> Ns G2" 
    using h3a by (simp add: ftotal_on_def)
  have h3d: "ftotal_on (tgt G2) (Es G2) (Ns G2)"  
    using h3 by (simp add: is_wf_g_def)
  have h3e: "ran (tgt G2) \<subseteq> Ns G2" 
    using h3d by (simp add: ftotal_on_def)
  have h3f: "dom (tgt G2) = Es G2" 
    using h3d by (simp add: ftotal_on_dom)
  assume h4: "adjacent x y (G1 UG G2)"
  from h4 h1a h2b h3b h2f h3f h3c h3e show "adjacent x y G1 \<or> adjacent x y G2" 
    by (simp add: cupG_def adjacent_def, erule_tac exE)
      (simp add: map_add_app_disj, auto intro: ranI split: if_splits)
qed

lemma adj_G_is_adj_U1: "\<lbrakk>is_wf_g G1; is_wf_g G2; disjEsGs G1 G2\<rbrakk> 
  \<Longrightarrow> adjacent x y G1 \<longrightarrow> adjacent x y (G1 UG G2)"
proof -
  fix x y
  assume h1: "disjEsGs G1 G2"
  have h1a: "Es G1 \<inter> Es G2 = {}" 
    using h1 by (simp add: disjEsGs_def disjoint_def)
  assume h2: "is_wf_g G1"
  have h2a: "ftotal_on (src G1) (Es G1) (Ns G1)"  
    using h2 by (simp add: is_wf_g_def)
  have h2b: "dom (src G1) = Es G1" 
    using h2a by (simp add: ftotal_on_dom)
  have h2c: "ftotal_on (tgt G1) (Es G1) (Ns G1)"  
    using h2 by (simp add: is_wf_g_def)
  have h2d: "dom (tgt G1) = Es G1" 
    using h2c by (simp add: ftotal_on_def)
  assume h3: "is_wf_g G2"
  have h3a: "ftotal_on (src G2) (Es G2) (Ns G2)"  
    using h3 by (simp add: is_wf_g_def)
  have h3b: "dom (src G2) = Es G2" 
    using h3a by (simp add: ftotal_on_dom)
  have h3c: "ftotal_on (tgt G2) (Es G2) (Ns G2)"  
    using h3 by (simp add: is_wf_g_def)
  have h3d: "dom (tgt G2) = Es G2" 
    using h3c by (simp add: ftotal_on_def)
  show "adjacent x y G1 \<longrightarrow> adjacent x y (G1 UG G2)"
  proof
    assume h4: "adjacent x y G1"
    show "adjacent x y (G1 UG G2)" 
    proof (rule ccontr)
      assume h5: "\<not> adjacent x y (G1 UG G2)"
      show "False"
        using h1a h4 h5 h2b h3b h2d h3d
        by (auto simp add: adjacent_def cupG_def, erule_tac allE, auto simp add: map_add_disj_domf)
    qed
  qed
qed

lemma adj_G_is_adj_U2: "\<lbrakk>is_wf_g G1; is_wf_g G2; disjEsGs G1 G2\<rbrakk> 
  \<Longrightarrow> adjacent x y G2 \<longrightarrow> adjacent x y (G1 UG G2)"
proof 
  fix x y
  assume h1: "disjEsGs G1 G2"
  have h1a: "disjEsGs G2 G1" using h1 by (simp add: disjEsGs_sym)
  assume h2: "is_wf_g G1"
  assume h3: "is_wf_g G2"
  assume h4: "adjacent x y G2"
  have h5: "G1 UG G2 = G2 UG G1" using h2 h3 h1 by (rule cupG_sym)
  show "adjacent x y (G1 UG G2)"  
    using h1a h2 h3 h4 by (simp add: h5 adj_G_is_adj_U1)
qed

lemma relOfGr_UG: "\<lbrakk>is_wf_g G1; is_wf_g G2; disjEsGs G1 G2\<rbrakk>  
    \<Longrightarrow> relOfGr (G1 UG G2) = relOfGr  G1 \<union> relOfGr G2"
  proof -
    assume h1: "disjEsGs G1 G2"
    assume h2: "is_wf_g G1"
    assume h3: "is_wf_g G2"
    show "relOfGr (G1 UG G2) = relOfGr G1 \<union> relOfGr G2"
    proof
      show "relOfGr (G1 UG G2) \<subseteq> relOfGr G1 \<union> relOfGr G2"
      proof (rule subrelI)
        fix x y
        show "(x, y) \<in> relOfGr (G1 UG G2) \<Longrightarrow> (x, y) \<in> relOfGr G1 \<union> relOfGr G2"
          using h1 h2 h3 by (simp add: relOfGr_def adjacent_dist)
      qed
      next
      show "relOfGr G1 \<union> relOfGr G2 \<subseteq> relOfGr (G1 UG G2)"
      proof (rule subrelI)
        fix x y
        show "(x, y) \<in> relOfGr G1 \<union> relOfGr G2 \<Longrightarrow> (x, y) \<in> relOfGr (G1 UG G2)"
        proof (simp add: relOfGr_def, erule disjE)
          assume h4: "adjacent x y G1"
          show "adjacent x y (G1 UG G2)" 
            using h1 h2 h3 h4 by (simp add: adj_G_is_adj_U1)
        next
          assume h4: "adjacent x y G2"
          show "adjacent x y (G1 UG G2)" 
            using h1 h2 h3 h4 by (simp add: adj_G_is_adj_U2)
        qed
     qed
  qed
qed

lemma relOfGr_disj_Gs: 
  assumes h1: "disjGs G1 G2" and h2: "is_wf_g G1" and h3: "is_wf_g G2"
  shows "Field (relOfGr G1) \<inter> Field (relOfGr G2) = {}"
  proof -
    from h1 have h1a: "Ns G1 \<inter> Ns G2 = {}" by (simp add: disjGs_def disjoint_def)
    from h2 have h2a: "ran (src G1) \<subseteq> Ns G1" by (simp add: is_wf_g_def ftotal_on_def)
    from h2 have h2b: "ran (tgt G1) \<subseteq> Ns G1" by (simp add: is_wf_g_def ftotal_on_def)
    from h3 have h3a: "ran (src G2) \<subseteq> Ns G2" by (simp add: is_wf_g_def ftotal_on_def)
    from h3 have h3b: "ran (tgt G2) \<subseteq> Ns G2" by (simp add: is_wf_g_def ftotal_on_def)
    show ?thesis
    proof
      show "Field (relOfGr G1) \<inter> Field (relOfGr G2) \<subseteq> {}"
      proof
        fix x 
        show "x \<in> Field (relOfGr G1) \<inter> Field (relOfGr G2) \<Longrightarrow> x \<in> {}"
        using h1a h2a h3a h2b h3b
          by (auto simp add: relOfGr_def adjacent_def Field_def intro!: ranI)
      qed
    next
      show "{} \<subseteq> Field (relOfGr G1) \<inter> Field (relOfGr G2)" by auto  
    qed
  qed

lemma acyclic_Gr_dist_disj: 
  assumes h1: "disjGs G1 G2" and h2: "is_wf_g G1" and h3: "is_wf_g G2" 
  shows "acyclicGr (G1 UG G2) = (acyclicGr G1 \<and> acyclicGr G2)"
  proof -
    from h1 have h1a: "disjEsGs G1 G2" by (simp add: disjGs_imp_disjEsGs)
    show "acyclicGr (G1 UG G2) = (acyclicGr G1 \<and> acyclicGr G2)"
    proof
      assume h4a: "acyclicGr (G1 UG G2)"
      show "acyclicGr G1 \<and> acyclicGr G2"
      proof 
        from h4a show "acyclicGr G1"
        using h1a h2 h3 by (simp add: acyclicGr_def relOfGr_UG acyclic_subset)
      next
        from h4a show "acyclicGr G2"
        using h1a h2 h3 by (simp add: acyclicGr_def relOfGr_UG acyclic_subset)
      qed
    next
      assume h4: "acyclicGr G1 \<and> acyclicGr G2"
      have h5: "Field (relOfGr  G1) \<inter> Field(relOfGr G2) = {}"  
        using h1 h2 h3 by (simp add: relOfGr_disj_Gs)
      show "acyclicGr (G1 UG G2)"
      using h1a h2 h3 h4 h5 by (simp add: acyclicGr_def relOfGr_UG acyclic_disj_dist)
   qed
qed

definition rst_fun:: "E set \<Rightarrow> (E \<rightharpoonup> V) \<Rightarrow>(E \<rightharpoonup> V)"
where
  "rst_fun es f \<equiv> f |` (es \<inter> dom f)"

lemma dom_rst_fun[simp]: "dom (rst_fun es f) = es \<inter> dom f"
  by (auto simp add: rst_fun_def)

lemma ran_rst_fun[simp]: "ran (rst_fun es f) = ran (f |` (es \<inter> dom f))"
  by (auto simp add: rst_fun_def)

lemma rst_fun_dist_map_add: "rst_fun es (f++g) = rst_fun es f ++ rst_fun es g"
  proof 
    fix x
    show "rst_fun es (f ++ g) x = (rst_fun es f ++ rst_fun es g) x"
    proof (case_tac "x \<in> es")
      assume h1: "x \<in> es"
      show "rst_fun es (f ++ g) x = (rst_fun es f ++ rst_fun es g) x"
      proof (case_tac "x \<in> dom f")
        assume h2: "x \<in> dom f"
        from h1 h2 show "rst_fun es (f ++ g) x = (rst_fun es f ++ rst_fun es g) x"
          by (auto simp add: rst_fun_def restrict_map_def map_add_def)
      next
        assume h2: "x \<notin> dom f"
        from h1 h2 show "rst_fun es (f ++ g) x = (rst_fun es f ++ rst_fun es g) x"
          by (auto simp add: rst_fun_def restrict_map_def map_add_def)
      qed
    next
      assume h1: "x \<notin> es"
      from h1 show "rst_fun es (f ++ g) x = (rst_fun es f ++ rst_fun es g) x"
        by (auto simp add: rst_fun_def restrict_map_def map_add_def) 
    qed
  qed

lemma rst_fun_eq: "(rst_fun es1 f = rst_fun es2 f) = (es1 \<inter> dom f = es2 \<inter> dom f)"
  proof 
    show "rst_fun es1 f = rst_fun es2 f \<Longrightarrow> es1 \<inter> dom f = es2 \<inter> dom f"
    proof
      show "rst_fun es1 f = rst_fun es2 f \<Longrightarrow> es1 \<inter> dom f \<subseteq> es2 \<inter> dom f"
      proof (rule subsetI, case_tac "x \<in> es1")
        fix x
        assume h1: "x \<in> es1"
        show "rst_fun es1 f = rst_fun es2 f \<Longrightarrow> x \<in> es1 \<inter> dom f \<Longrightarrow>x \<in> es2 \<inter> dom f"
        proof (case_tac "x \<in> es2")
          assume h2: "x \<in> es2"
          from h1 h2 show "rst_fun es1 f = rst_fun es2 f \<Longrightarrow> x \<in> es1 \<inter> dom f \<Longrightarrow>x \<in> es2 \<inter> dom f"
          by (simp add: rst_fun_def)
        next
          assume h2: "x \<notin> es2"
          assume h3: "rst_fun es1 f = rst_fun es2 f"
          from h3 have h3a: "(rst_fun es1 f) x = (rst_fun es2 f) x" by (simp)
          assume h4: "x \<in> es1 \<inter> dom f"
          from h1 h2 h3a h4 show "x \<in> es2 \<inter> dom f"
          by (auto simp add: rst_fun_def restrict_map_def split: if_splits)
        qed
      next
        fix x
        assume h1: "x \<notin> es1"
        assume h2: "rst_fun es1 f = rst_fun es2 f"
        from h2 have h2a: "(rst_fun es1 f) x = (rst_fun es2 f) x" by (simp)
        from h1 h2a show "x \<in> es1 \<inter> dom f \<Longrightarrow>x \<in> es2 \<inter> dom f" by (auto)
      qed
    next
      show "rst_fun es1 f = rst_fun es2 f \<Longrightarrow> es2 \<inter> dom f \<subseteq> es1 \<inter> dom f"
      proof (rule subsetI, case_tac "x \<in> es2")
        fix x
        assume h1: "x \<in> es2"
        show "rst_fun es1 f = rst_fun es2 f \<Longrightarrow> x \<in> es2 \<inter> dom f \<Longrightarrow>x \<in> es1 \<inter> dom f"
        proof (case_tac "x \<in> es1")
          assume h2: "x \<in> es1"
          from h1 h2 show "rst_fun es1 f = rst_fun es2 f \<Longrightarrow> x \<in> es2 \<inter> dom f \<Longrightarrow>x \<in> es1 \<inter> dom f"
          by (simp add: rst_fun_def)
        next
          assume h2: "x \<notin> es1"
          assume h3: "rst_fun es1 f = rst_fun es2 f"
          from h3 have h3a: "(rst_fun es1 f) x = (rst_fun es2 f) x" by (simp)
          assume h4: "x \<in> es2 \<inter> dom f"
          from h1 h2 h3a h4 show "x \<in> es1 \<inter> dom f"
          by (auto simp add: rst_fun_def restrict_map_def split: if_splits)
        qed
      next
        fix x
        assume h1: "x \<notin> es2"
        assume h2: "rst_fun es1 f = rst_fun es2 f"
        from h2 have h2a: "(rst_fun es1 f) x = (rst_fun es2 f) x" by (simp)
        from h1 h2a show "x \<in> es2 \<inter> dom f \<Longrightarrow> x \<in> es1 \<inter> dom f" by (auto)
      qed
    qed
  next
    assume h1: "es1 \<inter> dom f = es2 \<inter> dom f"
    show "rst_fun es1 f = rst_fun es2 f"
    proof
      fix x
      show "rst_fun es1 f x = rst_fun es2 f x"
      proof (case_tac "x \<in> es1")
        assume h2: "x \<in> es1"
        from h1 h2 show "rst_fun es1 f x = rst_fun es2 f x" by (simp add: rst_fun_def)
      next
        assume h2: "x \<notin> es1"
        from h1 h2 show "rst_fun es1 f x = rst_fun es2 f x" by (simp add: rst_fun_def)
      qed
    qed
  qed

lemma rst_fun_Un_neutral: 
  assumes h1: "es2 \<inter> (dom f) = {}"  and h2: "es1 \<subseteq> dom f"
  shows "rst_fun (es1 \<union> es2) f = rst_fun es1 f"
  proof
    fix x
    show "rst_fun (es1 \<union> es2) f x = rst_fun es1 f x"
    proof (case_tac "x \<in> es1")
      assume "x \<in> es1"
      then show "rst_fun (es1 \<union> es2) f x = rst_fun es1 f x"
      using assms by (auto simp add: rst_fun_def restrict_map_def split: if_splits)
    next
      assume "x \<notin> es1"
      then show "rst_fun (es1 \<union> es2) f x = rst_fun es1 f x"
      using assms by (auto simp add: rst_fun_def restrict_map_def split: if_splits)
    qed
  qed
  

definition rst_Ns:: "'a Gr_scheme \<Rightarrow> E set \<Rightarrow> V set"
where
  "rst_Ns G es \<equiv> ran ((src G) |` es) \<union> ran((tgt G) |` es)"

lemma rst_Ns_dist_UG: 
  assumes h1: "is_wf_g G1" and h2: "is_wf_g G2" and h3: "disjEsGs G1 G2"
  shows "rst_Ns (G1 UG G2) es = rst_Ns G1 es \<union> rst_Ns G2 es"
  proof -
    from h1 have h1a: "dom (src G1) = Es G1" 
      by (simp add: is_wf_g_def ftotal_on_def)
    from h1 have h1b: "dom (tgt G1) = Es G1"
      by (simp add: is_wf_g_def ftotal_on_def)
    from h2 have h2a: "dom (src G2) = Es G2" 
      by (simp add: is_wf_g_def ftotal_on_def)
    from h2 have h2b: "dom (tgt G2) = Es G2"
      by (simp add: is_wf_g_def ftotal_on_def)
    from h3 have h3a: "Es G1 \<inter> Es G2 = {}" 
      by (simp add: disjEsGs_def)
    from h1a h2a h3a have h4: "dom (src G1|` es) \<inter> dom (src G2|` es) = {}" 
      by auto
    from h1b h2b h3a have h5: "dom (tgt G1|` es) \<inter> dom (tgt G2|` es) = {}" 
      by auto
    from h4 h5 show ?thesis
      by (auto simp add: cupG_def rst_Ns_def map_add_restrict_dist)
  qed

lemma rst_Ns_disj: 
  assumes h1: "is_wf_g G1" and h2: "is_wf_g G2" and h3: "disjGs G1 G2"
  shows "rst_Ns G1 es1 \<inter> rst_Ns G2 es2 = {}"
  proof -
    from h1 have h1a: "ran (src G1) \<subseteq> Ns G1" 
      by (simp add: is_wf_g_def ftotal_on_def)
    from h1 have h1b: "ran (tgt G1) \<subseteq> Ns G1" 
      by (simp add: is_wf_g_def ftotal_on_def)
    from h2 have h2a: "ran (src G2) \<subseteq> Ns G2" 
      by (simp add: is_wf_g_def ftotal_on_def)
    from h2 have h2b: "ran (tgt G2) \<subseteq> Ns G2" 
      by (simp add: is_wf_g_def ftotal_on_def)
    show ?thesis
    proof
      show "rst_Ns G1 es1 \<inter> rst_Ns G2 es2 \<subseteq> {}"
      proof
        fix x
        assume ha: "x \<in> rst_Ns G1 es1 \<inter> rst_Ns G2 es2"
        hence hb: "x \<in> Ns G1" 
          using h1a h1b ran_restrict_sub[of "src G1" "es1"] 
          ran_restrict_sub[of "tgt G1" "es1"]
          by (auto simp add: rst_Ns_def)
        from ha have hc: "x \<in> Ns G2" 
          using h2a h2b ran_restrict_sub[of "src G2" "es2"] 
          ran_restrict_sub[of "tgt G2" "es2"]
          by (auto simp add: rst_Ns_def)
        from hb hc h3 show "x \<in> {}" by (auto simp add: disjGs_def)
      qed
    next
      show "{} \<subseteq> rst_Ns G1 es1 \<inter> rst_Ns G2 es2" by auto
    qed
 qed

lemma rst_Ns_sub: 
  assumes h1: "is_wf_g G" 
  shows "rst_Ns G es \<subseteq> Ns G"
  proof -
    from h1 have h1a: "ran (src G) \<subseteq> Ns G" 
      by (simp add: is_wf_g_def ftotal_on_def)
    from h1 have h1b: "ran (tgt G) \<subseteq> Ns G" 
      by (simp add: is_wf_g_def ftotal_on_def)
    from h1a h1b show ?thesis
      using ran_restrict_sub[of "src G" "es"] ran_restrict_sub[of "tgt G" "es"]
      by (auto simp add: rst_Ns_def)
  qed

lemma rst_Ns_Un_neutral: 
  assumes h1: "is_wf_g G" and h2: "es2 \<inter> Es G = {}"  and h3: "es1 \<subseteq> Es G"
  shows "rst_Ns G (es1 \<union> es2) = rst_Ns G es1"
  proof -
    from h1 have h1a: "dom (src G) = Es G"
      by (auto simp add: is_wf_g_def ftotal_on_def)
    from h1 have h1b: "dom (tgt G) = Es G"
      by (auto simp add: is_wf_g_def ftotal_on_def)
    have ha: "src G |` (es1 \<union> es2) = src G |` es1"
      using h2 h3 h1a by (simp add: disj_fun_vimage_Un)
    have hb: "tgt G |` (es1 \<union> es2) = tgt G |` es1"
      using h2 h3 h1b by (simp add: disj_fun_vimage_Un)
    show ?thesis
      using ha hb by (simp add: rst_Ns_def)
  qed

(*Yields a graph that is built from another one, by restricting to a set of edges*)
definition restrict :: "'a Gr_scheme \<Rightarrow> E set \<Rightarrow> Gr"
where
    "restrict G es \<equiv> \<lparr>Ns = rst_Ns G es, 
      Es = (Es G) \<inter> es, src = rst_fun es (src G), 
      tgt = rst_fun es (tgt G) \<rparr>"

lemma Ns_restrict[simp]: "Ns (restrict G es) = rst_Ns G es"
  by (simp add: restrict_def)

lemma Es_restrict[simp]:"Es (restrict G es) = (Es G) \<inter> es"
  by (simp add: restrict_def)

lemma src_restrict[simp]:"src (restrict G es) = rst_fun es (src G)"
  by (simp add: restrict_def)

lemma tgt_restrict[simp]:"tgt (restrict G es) = rst_fun es (tgt G)"
  by (simp add: restrict_def)

lemma restrict_dist_cup: 
  assumes h1: "is_wf_g G1" and h2: "is_wf_g G2" and h3: "disjEsGs G1 G2"
  shows "restrict (G1 UG G2) es = restrict G1 es UG restrict G2 es"
  using assms by (simp add: restrict_def rst_Ns_dist_UG rst_fun_dist_map_add)
    (auto simp add: cupG_def)

lemma is_src_es_simp[simp]: 
  assumes h1: "is_wf_g G"
  shows "src G |` (es \<inter> Es G) = src G |` es"
  proof -
    from h1 have h1a: "dom (src G) = Es G"
      by (simp add: is_wf_g_def ftotal_on_def)
    show ?thesis
    proof
      fix x
      show "(src G |` (es \<inter> Es G)) x = (src G |` es) x"
      proof (case_tac "x \<in> Es G")
        assume "x \<in> Es G"
        then show "(src G |` (es \<inter> Es G)) x = (src G |` es) x"
        by (auto simp add: restrict_map_def split: if_splits)
      next
        assume "x \<notin> Es G"
        hence "x \<notin> dom (src G)" using h1a by auto
        then show "(src G |` (es \<inter> Es G)) x = (src G |` es) x"
          by (auto simp add: restrict_map_def split: if_splits)
      qed
    qed
 qed

lemma is_tgt_es_simp[simp]: 
  assumes h1: "is_wf_g G"
  shows "tgt G |` (es \<inter> Es G) = tgt G |` es"
  proof -
    from h1 have h1a: "dom (tgt G) = Es G"
      by (simp add: is_wf_g_def ftotal_on_def)
    show ?thesis
    proof
      fix x
      show "(tgt G |` (es \<inter> Es G)) x = (tgt G |` es) x"
      proof (case_tac "x \<in> Es G")
        assume "x \<in> Es G"
        then show "(tgt G |` (es \<inter> Es G)) x = (tgt G |` es) x"
        by (auto simp add: restrict_map_def split: if_splits)
      next
        assume "x \<notin> Es G"
        hence "x \<notin> dom (tgt G)" using h1a by auto
        then show "(tgt G |` (es \<inter> Es G)) x = (tgt G |` es) x"
          by (auto simp add: restrict_map_def split: if_splits)
      qed
    qed
 qed

lemma is_wf_restrict: 
  assumes h1: "is_wf_g G"
  shows "is_wf_g (restrict G es)"
    using ran_restrict_sub[where f="src G" and A="es"] 
    ran_restrict_sub[where f="tgt G" and A="es"] assms
    by (auto simp add: is_wf_g_def ftotal_on_def rst_fun_def rst_Ns_def)
  
lemma is_disj_restrict: 
  assumes h1: "is_wf_g G1" and h2: "is_wf_g G2" and h3: "disjGs G1 G2"
  shows "disjGs (restrict G1 es1) (restrict G2 es2)"
  proof -
    from h1 have h1a: "ran (src G1)\<subseteq> Ns G1" 
      by (simp add: is_wf_g_def ftotal_on_def)
    from h1 have h1b: "ran (tgt G1)\<subseteq> Ns G1" 
      by (simp add: is_wf_g_def ftotal_on_def)
    from h2 have h2a: "ran (src G2)\<subseteq> Ns G2" 
      by (simp add: is_wf_g_def ftotal_on_def)
    from h2 have h2b: "ran (tgt G2)\<subseteq> Ns G2" 
      by (simp add: is_wf_g_def ftotal_on_def)
    from h3 have h3a: "Ns G1 \<inter> Ns G2 = {}" by (simp add: disjGs_def)
    from h3 have h3b: "Es G1 \<inter> Es G2 = {}" by (simp add: disjGs_def)
    from h3a h3b h1a h2a show ?thesis
    proof (simp add: disjGs_def rst_Ns_def)
      apply_end (rule conjI)
      show "(ran (src G1 |` es1) \<union> ran (tgt G1 |` es1)) 
        \<inter> (ran (src G2 |` es2) \<union> ran (tgt G2 |` es2)) = {}"
      proof
        show "(ran (src G1 |` es1) \<union> ran (tgt G1 |` es1)) 
          \<inter> (ran (src G2 |` es2) \<union> ran (tgt G2 |` es2)) \<subseteq> {}"
        proof
          fix x
          assume "x \<in> (ran (src G1 |` es1) \<union> ran (tgt G1 |` es1)) \<inter>
            (ran (src G2 |` es2) \<union> ran (tgt G2 |` es2))"
          hence "x \<in> (ran (src G1) \<union> ran (tgt G1)) \<inter>
            (ran (src G2) \<union> ran (tgt G2 ))"
            using ran_restrict_sub[of "src G2" "es2"] 
              ran_restrict_sub[of "src G1" "es1"]
              ran_restrict_sub[of "tgt G2" "es2"] 
              ran_restrict_sub[of "tgt G1" "es1"] by auto
            then show "x \<in> {}"
            using h3a h3b h1a h1b h2a h2b
            by (auto)
        qed
      next
        show "{} \<subseteq> (ran (src G1 |` es1) \<union> ran (tgt G1 |` es1)) 
          \<inter> (ran (src G2 |` es2) \<union> ran (tgt G2 |` es2))"
            by auto
      qed
    next
      apply_end (rule conjI)
      show "(ran (src G1 |` es1) \<union> ran (tgt G1 |` es1)) \<inter> (Es G1 \<inter> es1) = {}"
      proof
        show "(ran (src G1 |` es1) \<union> ran (tgt G1 |` es1)) \<inter> (Es G1 \<inter> es1) \<subseteq> {}"
        proof
          fix x
          assume "x \<in> (ran (src G1 |` es1) \<union> ran (tgt G1 |` es1)) \<inter> (Es G1 \<inter> es1)"
          hence "x \<in> (ran (src G1) \<union> ran (tgt G1)) \<inter> (Es G1 \<inter> es1)"
            using ran_restrict_sub[of "src G1" "es1"] ran_restrict_sub[of "tgt G1" "es1"]
            by auto
          hence "x \<in> Ns G1 \<inter> (Es G1 \<inter> es1)"
          using h1a h1b by auto
          then show "x \<in> {}" 
            using h3a h1 h2 disj_V_E
            by (auto simp add: is_wf_g_def ftotal_on_def)
       qed
      next
        show "{} \<subseteq> (ran (src G1 |` es1) \<union> ran (tgt G1 |` es1)) \<inter> (Es G1 \<inter> es1)"
          by auto
      qed
    next
      apply_end(rule conjI)
      show "(ran (src G1 |` es1) \<union> ran (tgt G1 |` es1)) \<inter> (Es G2 \<inter> es2) = {}"
      proof
        show "(ran (src G1 |` es1) \<union> ran (tgt G1 |` es1)) \<inter> (Es G2 \<inter> es2) \<subseteq> {}"
        proof
          fix x
          assume "x \<in> (ran (src G1 |` es1) \<union> ran (tgt G1 |` es1)) \<inter> (Es G2 \<inter> es2)"
          hence "x \<in> (ran (src G1) \<union> ran (tgt G1)) \<inter> (Es G2 \<inter> es2)"
            using ran_restrict_sub[of "src G1" "es1"] ran_restrict_sub[of "tgt G1" "es1"]
            by auto
          hence "x \<in> Ns G1 \<inter> (Es G2 \<inter> es2)" 
            using h1a h1b by auto
          then show "x \<in> {}"
            using h3a h1 h2 disj_V_E
            by (auto simp add: is_wf_g_def ftotal_on_def)
        qed
      next
        show "{} \<subseteq> (ran (src G1 |` es1) \<union> ran (tgt G1 |` es1)) \<inter> (Es G2 \<inter> es2)" by simp
      qed
    next
      apply_end(rule conjI)
      show "(ran (src G2 |` es2) \<union> ran (tgt G2 |` es2)) \<inter> (Es G1 \<inter> es1) = {}"
      proof
        show "(ran (src G2 |` es2) \<union> ran (tgt G2 |` es2)) \<inter> (Es G1 \<inter> es1) \<subseteq> {}"
        proof
          fix x
          assume "x \<in> (ran (src G2 |` es2) \<union> ran (tgt G2 |` es2)) \<inter> (Es G1 \<inter> es1)"
          hence "x \<in> (ran (src G2) \<union> ran (tgt G2)) \<inter> (Es G1 \<inter> es1)"
            using ran_restrict_sub[of "src G2" "es2"] ran_restrict_sub[of "tgt G2" "es2"]
            by auto
          hence "x \<in> Ns G2 \<inter> (Es G1 \<inter> es1)" 
            using h2a h2b by auto
          then show "x \<in> {}"
            using h3a h1 h2 disj_V_E
            by (auto simp add: is_wf_g_def ftotal_on_def)
        qed
      next
        show "{} \<subseteq> (ran (src G2 |` es2) \<union> ran (tgt G2 |` es2)) \<inter> (Es G1 \<inter> es1)" 
          by auto
      qed
    next
      apply_end(rule conjI)
      show "(ran (src G2 |` es2) \<union> ran (tgt G2 |` es2)) \<inter> (Es G2 \<inter> es2) = {}"
      proof
        show "(ran (src G2 |` es2) \<union> ran (tgt G2 |` es2)) \<inter> (Es G2 \<inter> es2) \<subseteq> {}"
        proof
          fix x
          assume "x \<in> (ran (src G2 |` es2) \<union> ran (tgt G2 |` es2)) \<inter> (Es G2 \<inter> es2)"
          hence "x \<in> (ran (src G2) \<union> ran (tgt G2)) \<inter> (Es G2 \<inter> es2)"
            using ran_restrict_sub[of "src G2" "es2"] ran_restrict_sub[of "tgt G2" "es2"]
            by auto
          hence "x \<in> Ns G2 \<inter> (Es G2 \<inter> es2)" 
            using h2a h2b by auto
          then show "x \<in> {}"
            using h3a h1 h2 disj_V_E
            by (auto simp add: is_wf_g_def ftotal_on_def)
        qed
      next
        show "{} \<subseteq> (ran (src G2 |` es2) \<union> ran (tgt G2 |` es2)) \<inter> (Es G2 \<inter> es2)"
          by auto
      qed
    next
      from h3b show "Es G1 \<inter> es1 \<inter> (Es G2 \<inter> es2) = {}"
        by auto
    qed
  qed 

(*definition rmv_EsOfNs:: "(E \<rightharpoonup> V) \<Rightarrow> (E \<rightharpoonup> V) \<Rightarrow> V set \<Rightarrow> (E \<rightharpoonup> V)"
where
  "rmv_EsOfNs f g ns \<equiv> (\<lambda> e. if f e \<in> (Some ` ns) \<or>  g e \<in> (Some ` ns) then None else f e)"

lemma dom_rmv_EsOfNs[simp]:
  "dom (rmv_EsOfNs f g ns) = dom f - (f-`(Some ` ns) \<union> g-`(Some ` ns))"
  by (auto simp add: rmv_EsOfNs_def vimage_def split: if_splits)

lemma ran_rmv_EsOfNs: "ran (rmv_EsOfNs f g ns) \<subseteq> ran f - ns"
  proof
    fix v
    assume "v \<in> ran (rmv_EsOfNs f g ns)"
    then have "\<exists> e. (rmv_EsOfNs f g ns) e = Some v" 
      by (simp add: ran_def)
    then show "v \<in> ran f - ns"
    proof
      fix e
      assume "(rmv_EsOfNs f g ns) e = Some v"
      then show "v \<in> ran f - ns"
        by (auto simp add: rmv_EsOfNs_def split: if_splits intro: ranI)
    qed
  qed

(*Yields a graph that is built from another one by all edges that are connected to some nodes*)
definition removeNs :: "'a Gr_scheme => V set => Gr"
where
    "removeNs G ns \<equiv> \<lparr>Ns = Ns G - ns, 
      Es = (Es G) - ((src G)-`(Some ` ns) \<union> (tgt G)-`(Some ` ns)), 
      src = rmv_EsOfNs (src G) (tgt G) ns, 
      tgt = rmv_EsOfNs (tgt G) (src G) ns \<rparr>"

lemma Ns_removeNs[simp]: "Ns (removeNs G ns) = Ns G - ns"
  by (simp add: removeNs_def)

lemma Es_removeNs[simp]:"Es (removeNs G ns) = (Es G) - ((src G)-`(Some ` ns) \<union> (tgt G)-`(Some ` ns))"
  by (simp add: removeNs_def)

lemma src_removeNs[simp]:"src (removeNs G ns) = rmv_EsOfNs (src G) (tgt G) ns"
  by (simp add: removeNs_def)

lemma tgt_removeNs[simp]:"tgt (removeNs G ns) = rmv_EsOfNs (tgt G) (src G) ns"
  by (simp add: removeNs_def)

lemma is_wf_remove:
  assumes h1: "is_wf_g G"
  shows "is_wf_g (removeNs G ns)"
  proof (simp add: is_wf_g_def, rule conjI)
    show "Ns G - ns \<subseteq> V_V"
      using h1 by (auto simp add: is_wf_g_def)
  next
    apply_end (rule conjI)
    show "Es G - (src G -` Some ` ns \<union> tgt G -` Some ` ns) \<subseteq> V_E"
      using h1 by (auto simp add: is_wf_g_def)
  next
    apply_end (rule conjI)
    show "ftotal_on (rmv_EsOfNs (src G) (tgt G) ns) (Es G - (src G -` Some ` ns \<union> tgt G -` Some ` ns))
     (Ns G - ns)"
     using h1 ran_rmv_EsOfNs[where f="src G" and g="(tgt G)" and ns ="ns"]
     by (auto simp add: ftotal_on_def is_wf_g_def)
  next
    show "ftotal_on (rmv_EsOfNs (tgt G) (src G) ns) (Es G - (src G -` Some ` ns \<union> tgt G -` Some ` ns))
     (Ns G - ns)"
    using h1 ran_rmv_EsOfNs[where f="tgt G" and g="(src G)" and ns ="ns"]
    by (auto simp add: ftotal_on_def is_wf_g_def)
  qed*)

(**** 
Function to be used in the graph replacement function.
****)
definition replace_emap:: "(E \<rightharpoonup> V) \<Rightarrow> (V \<rightharpoonup> V) \<Rightarrow> (E \<rightharpoonup> V)"
where
  "replace_emap f sub \<equiv> (\<lambda>e. if (\<exists>v1. v1 \<in> dom sub \<and> (f e) = Some v1) 
    then sub(the (f e)) else f e)"

lemma replace_emap_reduce: 
assumes "replace_emap f sub e = Some v"
shows "(\<exists> v0. sub v0 = Some v \<and> f e = Some v0) \<or> (the (f e) \<notin> dom sub \<and>f e = Some v)"
  using assms by (auto simp add: replace_emap_def split: if_splits)

lemma dom_replace_emap[simp]: "dom (replace_emap f sub) = dom f"
  by (auto simp add: replace_emap_def split: if_splits)

lemma ran_replace_emap[simp]: 
  assumes h1: "dom sub \<inter> ran sub = {}"
  shows "ran (replace_emap f sub) = ran f \<union> ran (sub |`ran f) - dom sub"
  proof
    show "ran (replace_emap f sub) \<subseteq> ran f \<union> ran (sub |` ran f) - dom sub"
      using h1 by (auto simp add: replace_emap_def ran_def restrict_map_def split: if_splits)
  next
    show "ran f \<union> ran (sub |` ran f) - dom sub \<subseteq> ran (replace_emap f sub)"
    proof
      fix x
      assume "x \<in> ran f \<union> ran (sub |` ran f) - dom sub"
      then have "x \<in> ran f \<and> x \<notin> dom sub \<or> x \<in> ran (sub |` ran f) " by auto
      then show "x \<in> ran (replace_emap f sub)"
      proof 
        assume h2: "x \<in> ran f \<and> x \<notin> dom sub"
        hence "\<exists> y. f y = Some x \<and> x \<notin> dom sub" by (simp add: ran_def)
        then show "x \<in> ran (replace_emap f sub)"
        proof
          fix y
          assume "f y = Some x \<and> x \<notin> dom sub"
          then show "x \<in> ran (replace_emap f sub)"
          by (simp add: replace_emap_def ran_def)(rule_tac exI[where x="y"], auto )
        qed
      next
        assume "x \<in> ran (sub |` ran f)"
        hence "\<exists> e y. sub y = Some x \<and> f e = Some y" 
          by (auto simp add: ran_def restrict_map_def split: if_splits)
        then show "x \<in> ran (replace_emap f sub)"
        proof
          apply_end(erule exE, erule conjE)
          fix e y
          assume h2: "sub y = Some x"
          assume h3: "f e = Some y"
          from h2 h3 show "x \<in> ran (replace_emap f sub)"
          by (auto simp add: replace_emap_def ran_def split: if_splits)
            (rule_tac exI[where x="e"], auto)
        qed
      qed
   qed
 qed

lemma replace_emap_dist_map_add: "replace_emap (f++g) sub
  = (replace_emap f sub) ++ (replace_emap g sub)"
  proof
    fix x
    show "replace_emap (f ++ g) sub x = (replace_emap f sub ++ replace_emap g sub) x"
      by (auto simp add: replace_emap_def map_add_def split: option.splits)
  qed

lemma replace_emap_neutral:
  assumes h1: "dom sub \<inter> ran f = {}"
  shows "replace_emap f sub = f"
  using h1 by (auto simp add: replace_emap_def fun_eq_iff split: if_splits intro: ranI)

(*Yields a graph that is built from another one, by replacing the target of edges*)
definition replaceGr :: "'a Gr_scheme => (V \<rightharpoonup> V) => Gr"
where
    "replaceGr G sub \<equiv> \<lparr>Ns = Ns G - dom sub \<union> ran (sub |` (Ns G)), Es = Es G, 
      src = replace_emap (src G) sub, 
      tgt = replace_emap (tgt G) sub\<rparr>"

lemma Ns_replace[simp]: "Ns (replaceGr G sub) = Ns G - dom sub \<union> ran (sub |` Ns G)"
  by (simp add: replaceGr_def)

lemma Es_replace[simp]:"Es (replaceGr G sub) = Es G"
  by (simp add: replaceGr_def)

lemma src_replace[simp]:"src (replaceGr G sub) = replace_emap (src G) sub"
  by (simp add: replaceGr_def)

lemma tgt_replace[simp]:"tgt (replaceGr G sub) = replace_emap (tgt G) sub"
  by (simp add: replaceGr_def)

lemma replace_dist_cup[simp]: "replaceGr (G1 UG G2) sub = (replaceGr G1 sub) UG (replaceGr G2 sub)"
  by (auto simp add: cupG_def replaceGr_def replace_emap_dist_map_add restrict_map_def ran_def 
    split: if_splits)

lemma is_wf_replace: 
  assumes h1: "is_wf_g G" and h2: "dom sub \<subseteq> V_A" and h3: "ran sub \<subseteq> V_A" 
    and h4: "dom sub \<inter> ran sub = {}"
  shows "is_wf_g (replaceGr G sub)"
  proof -
    from h1 have h1a: "ran (src G) \<subseteq> Ns G" 
      by (auto simp add: is_wf_g_def ftotal_on_def)
    from h1 have h1b: "dom (src G) = Es G" 
      by (auto simp add: is_wf_g_def ftotal_on_def)
    from h1 have h1c: "ran (tgt G) \<subseteq> Ns G" 
      by (auto simp add: is_wf_g_def ftotal_on_def)
    from h1 have h1d: "dom (tgt G) = Es G" 
      by (auto simp add: is_wf_g_def ftotal_on_def)
    show ?thesis
    proof (simp add: is_wf_g_def, rule conjI)
      from h1 h2 show "Ns G - dom sub \<subseteq> V_A" by (auto simp add: is_wf_g_def)
    next
      apply_end(rule conjI)
      from h1 h3 show "ran (sub |` Ns G) \<subseteq> V_A" 
        by (auto simp add: is_wf_g_def restrict_map_def ran_def split: if_splits)
    next
      apply_end(rule conjI)
      from h1 h3 show "Es G \<subseteq> E_A" by (auto simp add: is_wf_g_def)
    next
      apply_end(rule conjI)
      from h1a h1b h4 show "ftotal_on (replace_emap (src G) sub) (Es G) (Ns G - dom sub \<union> ran (sub |` Ns G))"
        using ran_replace_emap[where f="src G" and sub="sub"] h2 h3 
        by (auto simp add: ftotal_on_def ran_def restrict_map_def split: if_splits)   
    next
      from h1c h1d h4 show "ftotal_on (replace_emap (tgt G) sub) (Es G) (Ns G - dom sub \<union> ran (sub |` Ns G))"
        using ran_replace_emap[where f="tgt G" and sub="sub"] h2
         by (auto simp add: ftotal_on_def ran_def restrict_map_def split: if_splits) 
    qed
  qed

lemma disjEs_replace:
  assumes h: "disjEsGs G1 G2"
  shows "disjEsGs (replaceGr G1 sub) (replaceGr G2 sub)"
  using h by (simp add: disjEsGs_def)

lemma replace_neutral:
  assumes h1: "is_wf_g G" and h2: "dom sub \<inter> Ns G = {}" 
  shows "replaceGr G sub = G"
  proof -
    from h1 have h1a: "ran (src G) \<subseteq> Ns G" 
      by (simp add: is_wf_g_def ftotal_on_def)
    from h1 have h1b: "ran (tgt G) \<subseteq> Ns G" 
      by (simp add: is_wf_g_def ftotal_on_def)
    from h2 have h2a: "Ns G - dom sub \<union> ran (sub |` Ns G) = Ns G"
      by (auto simp add: restrict_map_def ran_def split: if_splits)
    from h2 h1a have h2b: "dom sub \<inter> ran (src G) = {}" by auto
    from h2 h1b have h2c: "dom sub \<inter> ran (tgt G) = {}" by auto
    show ?thesis
    using h2 h2a h2b h2c 
    by (auto simp add: replaceGr_def replace_emap_neutral split: if_splits)
  qed

lemma relOfGr_replace:
  shows "relOfGr(replaceGr G sub) = {(x, y). \<exists> e. e \<in> Es G 
    \<and> replace_emap (src G) sub e = Some x \<and> replace_emap (tgt G) sub e = Some y}"
  proof -
    show ?thesis
    proof
      show "relOfGr (replaceGr G sub) \<subseteq> {(x, y). \<exists>e. e \<in> Es G 
        \<and> replace_emap (src G) sub e = Some x \<and> replace_emap (tgt G) sub e = Some y}"
      proof (rule subrelI)
        fix x y
        assume "(x, y) \<in> relOfGr (replaceGr G sub)"
        hence "\<exists> e. e \<in> (Es G) \<and> replace_emap (src G) sub e = Some x 
          \<and> replace_emap (tgt G) sub e = Some y" 
          by (auto simp add: relOfGr_def adjacent_def replace_emap_def split: if_splits)
        then show "(x, y) \<in> {(x, y). \<exists>e. e \<in> Es G 
            \<and> replace_emap (src G) sub e = Some x \<and> replace_emap (tgt G) sub e = Some y}"
            by auto
      qed
    next
      show "{(x, y). \<exists>e. e \<in> Es G \<and> replace_emap (src G) sub e = Some x \<and> replace_emap (tgt G) sub e = Some y}
        \<subseteq> relOfGr (replaceGr G sub)"
        proof (rule subrelI, clarsimp)
          fix x y e
          assume h3: "e \<in> Es G"
          assume h4: "replace_emap (src G) sub e = Some x"
          assume h5: "replace_emap (tgt G) sub e = Some y"
          from h3 h4 h5 show "(x, y) \<in> relOfGr (replaceGr G sub)"
            by (simp add: relOfGr_def adjacent_def)(rule_tac exI[where x="e"], auto)
        qed
    qed
  qed

lemma is_wf_g_Un: 
  assumes h1: "is_wf_g G1" and h2: "is_wf_g G2" 
  shows "is_wf_g (G1 UG G2)"
  proof -
    from h1 have h1a: "ftotal_on (src G1) (Es G1) (Ns G1)"
      by (simp add: is_wf_g_def)
    from h1 have h1b: "ftotal_on (tgt G1) (Es G1) (Ns G1)"
      by (simp add: is_wf_g_def)
    from h1a have h1c : "dom (src G1) = Es G1" by (simp add: ftotal_on_dom) 
    from h1b have h1d : "dom (tgt G1) = Es G1" by (simp add: ftotal_on_dom)
    from h1 have h1e: "(Ns G1) \<inter> (Es G1) = {}" using disjoint_WF_G by (simp)
    have h2a: "ftotal_on (src G2) (Es G2) (Ns G2)"
      using h2 by (simp add: is_wf_g_def)
    have h2b: "ftotal_on (tgt G2) (Es G2) (Ns G2)"
      using h2 by (simp add: is_wf_g_def)
    have h2c : "dom (src G2) = Es G2" using h2a by (simp add: ftotal_on_dom) 
    have h2d : "dom (tgt G2) = Es G2" using h2b by (simp add: ftotal_on_dom) 
    from h2 have h2e: "(Ns G2) \<inter> (Es G2) = {}" using disjoint_WF_G by (simp)
    show "is_wf_g (G1 UG G2)"
    proof (simp add: is_wf_g_def cupG_def, rule conjI)
      from h1 show "Ns G1 \<subseteq> V_A" by (simp add: is_wf_g_def)
    next
      apply_end(rule conjI)
      from h2 show "Ns G2 \<subseteq> V_A" by (simp add: is_wf_g_def)
    next 
      apply_end(rule conjI)
      from h1 show "Es G1 \<subseteq> E_A" by (simp add: is_wf_g_def)
    next
      apply_end(rule conjI)
      from h2 show "Es G2 \<subseteq> E_A" by (simp add: is_wf_g_def)
    next
      apply_end(rule conjI)
      show "ftotal_on (src G1 ++ src G2) (Es G1 \<union> Es G2) (Ns G1 \<union> Ns G2)"
      using h1a h2a h1c h2c
        ran_map_add_sub[where f="src G1" and g="src G2"]
        by (auto simp add: ftotal_on_def)
    next
      show "ftotal_on (tgt G1 ++ tgt G2) (Es G1 \<union> Es G2) (Ns G1 \<union> Ns G2)"
      using h1b h2b h1d h2d
        ran_map_add_sub[where f="tgt G1" and g="tgt G2"]
        by (auto simp add: ftotal_on_def)
   qed
 qed

(*A representation of morphisms*)
record Morph =
  fV :: "V\<rightharpoonup>V"
  fE :: "E\<rightharpoonup>E"

lemma Morph_eq: 
  shows "(M1 = M2) \<longleftrightarrow> fV M1 = fV M2 \<and> fE M1 = fE M2 \<and> Morph.more M1 = Morph.more M2"
    by (auto)

definition morphGr :: "'a Gr_scheme \<Rightarrow> 'a Gr_scheme \<Rightarrow> Morph set"
where
  "morphGr G1 G2 \<equiv> {r. ftotal_on (fV r) (Ns G1) (Ns G2) 
      \<and> ftotal_on (fE r) (Es G1) (Es G2) \<and> (fV r) \<circ>\<^sub>m (src G1) = (src G2) \<circ>\<^sub>m (fE r) 
      \<and> (fV r) \<circ>\<^sub>m (tgt G1) = (tgt G2) \<circ>\<^sub>m (fE r)}"

definition morphGrComp :: "Morph \<Rightarrow> Morph \<Rightarrow> Morph"
where
  "morphGrComp MG1 MG2 \<equiv> \<lparr>fV = (fV MG2) \<circ>\<^sub>m (fV MG1), fE = (fE MG2) \<circ>\<^sub>m (fE MG1) \<rparr>"

(*The empty graph morphism*)
definition emptyGM :: "Morph"
where
  "emptyGM \<equiv> \<lparr>fV = empty, fE = empty \<rparr>"

definition UGrM :: "'a Morph_scheme  \<Rightarrow> 'a Morph_scheme \<Rightarrow> Morph" (infixl "UGM" 100)
where
  "MG1 UGM MG2 \<equiv> \<lparr>fV= (fV MG1)++(fV MG2), fE = (fE MG1)++(fE MG2)\<rparr>"

lemma fVL_UGM[simp]: "fV (ML1 UGM ML2) = (fV ML1)++(fV ML2)"
  by (simp add: UGrM_def)

lemma fEL_UGM[simp]: "fE (ML1 UGM ML2) = (fE ML1)++(fE ML2)"
  by (simp add: UGrM_def)

end
