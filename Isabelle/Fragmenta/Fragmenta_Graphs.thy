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
  assumes "disjGs G1 G2"
  shows "disjEsGs G1 G2"
  using assms by (simp add: disjGs_def disjEsGs_def)

lemma dom_src_G:
  assumes "wf_g G"
  shows "dom (src G) = Es G"
  using assms by (simp add: wf_g_def ftotal_on_def)

lemma ran_src_G:
  assumes "wf_g G"
  shows "ran (src G) \<subseteq> Ns G"
  using assms by (simp add: wf_g_def ftotal_on_def)

lemma dom_tgt_G:
  assumes "wf_g G"
  shows "dom (tgt G) = Es G"
  using assms by (simp add: wf_g_def ftotal_on_def)

lemma ran_tgt_G:
  assumes "wf_g G"
  shows "ran (tgt G) \<subseteq> Ns G"
  using assms by (simp add: wf_g_def ftotal_on_def)

lemma es_disj_Ga_Gb:
  assumes "disjEsGs Ga Gb"
  shows "Es Ga \<inter> Es Gb = {}" 
  using assms by (simp add: disjEsGs_def)

lemma ns_disj_Ga_Gb:
  assumes "disjGs Ga Gb"
  shows "Ns Ga \<inter> Ns Gb = {}" 
  using assms by (simp add: disjGs_def)

lemma cupG_sym:
  assumes "wf_g Ga" and "wf_g Gb" and "disjEsGs Ga Gb"
  shows "Ga UG Gb = Gb UG Ga"
  proof (auto simp add: cupG_def)
     show "src Ga ++ src Gb = src Gb ++ src Ga"
     proof
        fix x
        show "(src Ga ++ src Gb) x = (src Gb ++ src Ga) x"
        using assms dom_src_G[of Ga] 
        dom_src_G[where G = Gb] 
        es_disj_Ga_Gb[of Ga Gb] 
        by (auto simp add: map_add_def split: option.splits)
     qed
   next
     show "tgt Ga ++ tgt Gb = tgt Gb ++ tgt Ga"
     proof
        fix x
        show "(tgt Ga ++ tgt Gb) x = (tgt Gb ++ tgt Ga) x"
          using assms dom_tgt_G[where G = Ga] 
            dom_tgt_G[where G = Gb] 
            es_disj_Ga_Gb[where Ga = Ga and Gb = Gb]
          by (auto simp add: map_add_def split: option.splits)
     qed
   qed

lemma Ug_Id[simp]:
  shows "G UG emptyG = G"
  by (simp add: cupG_def emptyG_def)

lemma adjacent_dist: 
  assumes "wf_g G1" and "wf_g G2" and "disjEsGs G1 G2"
  shows "adjacent x y (G1 UG G2) \<longrightarrow> adjacent x y G1 \<or> adjacent x y G2"
proof -
  fix x y
  show ?thesis
    using assms dom_src_G[where G = G1] dom_tgt_G[where G = G1] 
    dom_src_G[where G = G2] dom_tgt_G[where G = G2] 
    ran_src_G[where G = G2] es_disj_Ga_Gb[where Ga = G1 and Gb = G2]
    by (simp add: adjacent_def map_add_app_disj, auto intro: ranI split: if_splits)
qed

lemma adj_G_is_adj_U1: 
  assumes "wf_g G1" and "wf_g G2" and "disjEsGs G1 G2"
  shows "adjacent x y G1 \<longrightarrow> adjacent x y (G1 UG G2)"
proof -
  fix x y
  show ?thesis
    using assms es_disj_Ga_Gb[of G1 G2]
    dom_src_G[where G = G1] dom_tgt_G[where G = G1] 
    dom_src_G[where G = G2] dom_tgt_G[where G = G2] 
    by (auto simp add: adjacent_def map_add_disj_domf)
qed

lemma adj_G_is_adj_U2: 
  assumes "wf_g G1" and "wf_g G2" and "disjEsGs G1 G2"
  shows "adjacent x y G2 \<longrightarrow> adjacent x y (G1 UG G2)"
proof -
  fix x y
  show ?thesis
  using assms adj_G_is_adj_U1[of G2 G1]
  by (simp add: cupG_sym disjEsGs_sym)
qed

lemma adjacent_equiv:
  assumes "wf_g G1" and "wf_g G2" and "disjEsGs G1 G2"
  shows "adjacent x y (G1 UG G2) \<longleftrightarrow> adjacent x y G1 \<or> adjacent x y G2"
proof
  fix x y
  assume "adjacent x y (G1 UG G2)"
  then show "adjacent x y G1 \<or> adjacent x y G2"
    using assms 
    by (simp add: adjacent_dist)
next
  fix x y 
  assume "adjacent x y G1 \<or> adjacent x y G2"
  then show "adjacent x y (G1 UG G2)"
    using assms adj_G_is_adj_U1[of G1 G2 x y] 
     adj_G_is_adj_U2[of G1 G2 x y] 
    by (auto)
qed

lemma relOfGr_UG: 
  assumes "wf_g G1" and "wf_g G2" and "disjEsGs G1 G2" 
  shows "relOfGr (G1 UG G2) = relOfGr  G1 \<union> relOfGr G2"
proof 
  show "relOfGr (G1 UG G2) \<subseteq> relOfGr G1 \<union> relOfGr G2"
  proof (rule subrelI)
    fix x y
    assume "(x, y) \<in> relOfGr (G1 UG G2)"
    then show "(x, y) \<in> relOfGr G1 \<union> relOfGr G2"
    using assms by (simp add: relOfGr_def adjacent_dist)
  qed
next
  show "relOfGr G1 \<union> relOfGr G2 \<subseteq> relOfGr (G1 UG G2)"
  proof (rule subrelI)
     fix x y
     show "(x, y) \<in> relOfGr G1 \<union> relOfGr G2 \<Longrightarrow> (x, y) \<in> relOfGr (G1 UG G2)"
     proof (simp add: relOfGr_def, erule disjE)
        assume "adjacent x y G1"
        then show "adjacent x y (G1 UG G2)" 
            using assms by (simp add: adj_G_is_adj_U1)
     next
       assume "adjacent x y G2"
       then show "adjacent x y (G1 UG G2)" 
            using assms by (simp add: adj_G_is_adj_U2)
     qed
   qed
qed

lemma relOfGr_disj_Gs: 
  assumes "disjGs G1 G2" and "wf_g G1" and "wf_g G2"
  shows "Field (relOfGr G1) \<inter> Field (relOfGr G2) = {}"
proof
  show "Field (relOfGr G1) \<inter> Field (relOfGr G2) \<subseteq> {}"
  proof
    fix x 
    show "x \<in> Field (relOfGr G1) \<inter> Field (relOfGr G2) \<Longrightarrow> x \<in> {}"
    using assms ns_disj_Ga_Gb[of G1 G2] 
      ran_src_G[of G1] ran_src_G[of G2] 
      ran_tgt_G[of G1] ran_tgt_G[of G2]
      by (auto simp add: relOfGr_def adjacent_def Field_def intro!: ranI)
  qed
  next
     show "{} \<subseteq> Field (relOfGr G1) \<inter> Field (relOfGr G2)" by auto  
qed

lemma acyclic_Gr_dist_disj: 
  assumes "disjGs G1 G2" and "wf_g G1" and "wf_g G2" 
  shows "acyclicGr (G1 UG G2) = (acyclicGr G1 \<and> acyclicGr G2)"
proof 
   assume "acyclicGr (G1 UG G2)"
   then show "acyclicGr G1 \<and> acyclicGr G2"
     using assms disjGs_imp_disjEsGs[of G1 G2]
     by (simp add: acyclicGr_def relOfGr_UG acyclic_subset)
 next
   apply_end(clarsimp)
   assume "acyclicGr G1" and "acyclicGr G2"
   then show "acyclicGr (G1 UG G2)"
     using assms disjGs_imp_disjEsGs[of G1 G2]
      relOfGr_disj_Gs[of G1 G2]
     by (simp add: acyclicGr_def relOfGr_UG acyclic_disj_dist)
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
  assumes "wf_g G1" and "wf_g G2" and "disjEsGs G1 G2"
  shows "rst_Ns (G1 UG G2) es = rst_Ns G1 es \<union> rst_Ns G2 es"
  proof -
    from assms have h4: "dom (src G1|` es) \<inter> dom (src G2|` es) = {}" 
      using dom_src_G[of G1] dom_tgt_G[of G1] 
        dom_src_G[of G2] es_disj_Ga_Gb[of G1 G2]
      by auto
    from assms have h5: "dom (tgt G1|` es) \<inter> dom (tgt G2|` es) = {}" 
      using dom_tgt_G[of G1] dom_tgt_G[of G2] es_disj_Ga_Gb[of G1 G2]
      by auto
    from h4 h5 show ?thesis
      by (auto simp add: cupG_def rst_Ns_def map_add_restrict_dist)
  qed

lemma rst_Ns_disj: 
  assumes "wf_g G1" and "wf_g G2" and "disjGs G1 G2"
  shows "rst_Ns G1 es1 \<inter> rst_Ns G2 es2 = {}"
  proof
    show "rst_Ns G1 es1 \<inter> rst_Ns G2 es2 \<subseteq> {}"
    proof
      fix x
      assume ha: "x \<in> rst_Ns G1 es1 \<inter> rst_Ns G2 es2"
      hence hb: "x \<in> Ns G1" 
         using assms(1) ran_src_G[of G1] ran_tgt_G[of G1] 
            ran_restrict_sub[of "src G1" "es1"] 
            ran_restrict_sub[of "tgt G1" "es1"]
          by (auto simp add: rst_Ns_def)
      from ha have hc: "x \<in> Ns G2" 
         using assms(2) ran_src_G[of G2] ran_tgt_G[of G2] 
         ran_restrict_sub[of "src G2" "es2"] 
         ran_restrict_sub[of "tgt G2" "es2"]
      by (auto simp add: rst_Ns_def)
      from hb hc assms(3) show "x \<in> {}" 
      by (auto simp add: disjGs_def)
      qed
  next
     show "{} \<subseteq> rst_Ns G1 es1 \<inter> rst_Ns G2 es2" by auto
  qed

lemma rst_Ns_sub: 
  assumes "wf_g G" 
  shows "rst_Ns G es \<subseteq> Ns G"
  using assms ran_src_G[of G] ran_tgt_G[of G] 
        ran_restrict_sub[of "src G" "es"] 
        ran_restrict_sub[of "tgt G" "es"]
  by (auto simp add: rst_Ns_def)


lemma rst_Ns_Un_neutral: 
  assumes h1: "wf_g G" and h2: "es2 \<inter> Es G = {}"  and h3: "es1 \<subseteq> Es G"
  shows "rst_Ns G (es1 \<union> es2) = rst_Ns G es1"
  proof -
    have ha: "src G |` (es1 \<union> es2) = src G |` es1"
      using assms dom_src_G[of G] by (simp add: disj_fun_vimage_Un)
    have hb: "tgt G |` (es1 \<union> es2) = tgt G |` es1"
      using assms dom_tgt_G[of G] 
      by (simp add: disj_fun_vimage_Un)
    show ?thesis
      using ha hb by (simp add: rst_Ns_def)
  qed

(*Restricts a graph to a set of given edges*)
definition restrict :: "'a Gr_scheme \<Rightarrow> E set \<Rightarrow> Gr" (infixl "\<bowtie>" 100)
where
    "G \<bowtie> es \<equiv> \<lparr>Ns = rst_Ns G es, 
      Es = (Es G) \<inter> es, src = rst_fun es (src G), 
      tgt = rst_fun es (tgt G) \<rparr>"

lemma Ns_restrict[simp]: "Ns (G \<bowtie> es) = rst_Ns G es"
  by (simp add: restrict_def)

lemma Es_restrict[simp]:"Es (G \<bowtie> es) = (Es G) \<inter> es"
  by (simp add: restrict_def)

lemma src_restrict[simp]:"src (G \<bowtie> es) = rst_fun es (src G)"
  by (simp add: restrict_def)

lemma tgt_restrict[simp]:"tgt (G \<bowtie> es) = rst_fun es (tgt G)"
  by (simp add: restrict_def)

lemma restrict_dist_cup: 
  assumes "wf_g G1" and "wf_g G2" and "disjEsGs G1 G2"
  shows "(G1 UG G2) \<bowtie> es = (G1 \<bowtie> es) UG (G2 \<bowtie> es)"
  using assms 
  by (simp add: restrict_def rst_Ns_dist_UG rst_fun_dist_map_add)
    (auto simp add: cupG_def)

lemma src_es_simp[simp]: 
  assumes "wf_g G"
  shows "src G |` (es \<inter> Es G) = src G |` es"
  proof
      fix x
      show "(src G |` (es \<inter> Es G)) x = (src G |` es) x"
      proof (case_tac "x \<in> Es G")
        assume "x \<in> Es G"
        then show "(src G |` (es \<inter> Es G)) x = (src G |` es) x"
        by (auto simp add: restrict_map_def split: if_splits)
      next
        assume "x \<notin> Es G"
        hence "x \<notin> dom (src G)" 
          using assms dom_src_G[of G] by auto
        then show "(src G |` (es \<inter> Es G)) x = (src G |` es) x"
          by (auto simp add: restrict_map_def split: if_splits)
      qed
  qed

lemma tgt_es_simp[simp]: 
  assumes "wf_g G"
  shows "tgt G |` (es \<inter> Es G) = tgt G |` es"
proof
      fix x
      show "(tgt G |` (es \<inter> Es G)) x = (tgt G |` es) x"
      proof (case_tac "x \<in> Es G")
        assume "x \<in> Es G"
        then show "(tgt G |` (es \<inter> Es G)) x = (tgt G |` es) x"
        by (auto simp add: restrict_map_def split: if_splits)
      next
        assume "x \<notin> Es G"
        hence "x \<notin> dom (tgt G)" 
          using assms dom_tgt_G[of G] by auto
        then show "(tgt G |` (es \<inter> Es G)) x = (tgt G |` es) x"
          by (auto simp add: restrict_map_def split: if_splits)
      qed
qed

lemma wf_restrict: 
  assumes "wf_g G"
  shows "wf_g (G \<bowtie> es)"
    using ran_restrict_sub[of "src G" "es"] 
    ran_restrict_sub[of "tgt G" "es"] assms
    by (auto simp add: wf_g_def ftotal_on_def rst_fun_def rst_Ns_def)
  
lemma disj_restrict: 
  assumes "wf_g G1" and "wf_g G2" and "disjGs G1 G2"
  shows "disjGs (G1 \<bowtie> es1) (G2 \<bowtie> es2)"
  proof -
    show ?thesis
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
              using assms disjGs_imp_disjEsGs[of G1 G2] 
                ns_disj_Ga_Gb[of G1 G2] 
                es_disj_Ga_Gb[of G1 G2] 
                ran_src_G[of G1] ran_tgt_G[of G1] 
                ran_src_G[of G2] ran_tgt_G[of G2]
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
            using assms ran_src_G[of G1] ran_tgt_G[of G1] 
              ran_src_G[of G2] 
            by auto
          then show "x \<in> {}" 
            using assms(1) assms(2) disj_V_E
            by (auto simp add: wf_g_def ftotal_on_def)
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
            using assms(1) assms(2) 
              dom_src_G[of G1] dom_tgt_G[of G1] 
              ran_src_G[of G1] ran_tgt_G[of G1]
            by auto
          then show "x \<in> {}"
            using assms(1) assms(2) disj_V_E ns_disj_Ga_Gb[of G1 G2] 
            by (auto simp add: wf_g_def ftotal_on_def)
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
            using assms(2) ran_src_G[of G2] ran_tgt_G[of G2] 
            by auto
          then show "x \<in> {}"
            using ns_disj_Ga_Gb[of G1 G2] assms disj_V_E
            by (auto simp add: wf_g_def ftotal_on_def)
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
            using assms(2) ran_src_G[of G2] ran_tgt_G[of G2] 
            by auto
          then show "x \<in> {}"
            using ns_disj_Ga_Gb[of G1 G2] assms disj_V_E
            by (auto simp add: wf_g_def ftotal_on_def)
        qed
      next
        show "{} \<subseteq> (ran (src G2 |` es2) \<union> ran (tgt G2 |` es2)) \<inter> (Es G2 \<inter> es2)"
          by auto
      qed
    next
      show "Es G1 \<inter> es1 \<inter> (Es G2 \<inter> es2) = {}"
        using assms disjGs_imp_disjEsGs[of G1 G2] 
            es_disj_Ga_Gb[of G1 G2]
        by auto
    qed
  qed 

lemma emptyG_restrict:
  shows "emptyG \<bowtie> es = emptyG"
  by (simp add: restrict_def emptyG_def rst_Ns_def rst_fun_def)

lemma G_restrict_empty:
  shows "G \<bowtie> {} = emptyG"
  by (simp add: restrict_def rst_Ns_def rst_fun_def emptyG_def)

(*Subsumption*)
definition subsumeG::"Gr \<Rightarrow>(V \<rightharpoonup> V) \<Rightarrow> Gr" (infixl "\<odot>" 100)
  where
  "G \<odot> s \<equiv> if fpartial_on s (Ns G) (Ns G) then 
    \<lparr>Ns = (Ns G) - (dom s) \<union> (ran s), Es = Es G, 
    src =  (mtotalise_in s (Ns G))\<circ>\<^sub>m (src G), 
    tgt =  (mtotalise_in s (Ns G))\<circ>\<^sub>m (tgt G)\<rparr> else G"

lemma subsumeG_empty: 
  assumes "wf_g G"
  shows "G \<odot> Map.empty = G"
using assms ran_src_G[of G] ran_tgt_G[of G] 
  by (auto simp add: subsumeG_def mid_on_comp_A_in_ran)

lemma subsumeG_same: 
  assumes "wf_g G"
  shows "G \<odot> mid_on (Ns G) = G"
using assms ran_src_G[of G] ran_tgt_G[of G] 
  by (simp add: subsumeG_def mid_on_comp_A_in_ran 
      mtotalise_in_def map_add_subsumed2)

(*lemma subsumeG_union:
  assumes "wf_g G1" and "wf_g G1" and "disjGs G1 G2"
    and "fpartial_on s1 (Ns G1) (Ns G1)"
    and "fpartial_on s2 (Ns G2) (Ns G2)"
  shows "(G1 UG G2)\<odot> (s1++s2) = (G1 \<odot> s1) UG (G2 \<odot> s2)"
  using assms by (simp add: subsumeG_def fpartial_on_map_add)*)

(****
Function to be used in graph replacement function.
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
  assumes h1: "wf_g G" and h2: "dom sub \<subseteq> V_A" and h3: "ran sub \<subseteq> V_A" 
    and h4: "dom sub \<inter> ran sub = {}"
  shows "wf_g (replaceGr G sub)"
  proof (simp add: wf_g_def, rule conjI)
      from h1 h2 show "Ns G - dom sub \<subseteq> V_A" 
        by (auto simp add: wf_g_def)
    next
      apply_end(rule conjI)
      from h1 h3 show "ran (sub |` Ns G) \<subseteq> V_A" 
        by (auto simp add: wf_g_def restrict_map_def ran_def split: if_splits)
    next
      apply_end(rule conjI)
      from h1 h3 show "Es G \<subseteq> E_A" by (auto simp add: wf_g_def)
    next
      apply_end(rule conjI)
      from h1 h4 show "ftotal_on (replace_emap (src G) sub) (Es G) (Ns G - dom sub \<union> ran (sub |` Ns G))"
        using ran_src_G[of G] dom_src_G[of G] ran_replace_emap[where f="src G" and sub="sub"] h2 h3 
        by (auto simp add: ftotal_on_def ran_def restrict_map_def split: if_splits)   
    next
      from h1 h4 show "ftotal_on (replace_emap (tgt G) sub) (Es G) (Ns G - dom sub \<union> ran (sub |` Ns G))"
        using ran_tgt_G[of G] dom_tgt_G[of G] ran_replace_emap[where f="tgt G" and sub="sub"] h2
         by (auto simp add: ftotal_on_def ran_def restrict_map_def split: if_splits) 
 qed


lemma disjEs_replace:
  assumes "disjEsGs G1 G2"
  shows "disjEsGs (replaceGr G1 sub) (replaceGr G2 sub)"
  using assms by (simp add: disjEsGs_def)

lemma replace_neutral:
  assumes "wf_g G" and "dom sub \<inter> Ns G = {}" 
  shows "replaceGr G sub = G"
  proof -
    from assms(2) have h2a: "Ns G - dom sub \<union> ran (sub |` Ns G) = Ns G"
      by (auto simp add: restrict_map_def ran_def split: if_splits)
    from assms have h2b: "dom sub \<inter> ran (src G) = {}" 
      using ran_src_G[of G] by auto
    from assms have h2c: "dom sub \<inter> ran (tgt G) = {}" 
      using ran_tgt_G[of G] by auto
    show ?thesis
    using assms(2) h2a h2b h2c 
    by (auto simp add: replaceGr_def replace_emap_neutral split: if_splits)
  qed

lemma relOfGr_replace:
  shows "relOfGr(replaceGr G sub) = {(x, y). \<exists> e. e \<in> Es G 
    \<and> replace_emap (src G) sub e = Some x 
    \<and> replace_emap (tgt G) sub e = Some y}"
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

lemma wf_g_Un: 
  assumes "wf_g G1" and "wf_g G2" 
  shows "wf_g (G1 UG G2)"
  proof (simp add: wf_g_def cupG_def, rule conjI)
    from assms(1) show "Ns G1 \<subseteq> V_A" 
      by (simp add: wf_g_def)
    next
      apply_end(rule conjI)
      from assms(2) show "Ns G2 \<subseteq> V_A" 
        by (simp add: wf_g_def)
    next 
      apply_end(rule conjI)
      from assms(1) show "Es G1 \<subseteq> E_A" by (simp add: wf_g_def)
    next
      apply_end(rule conjI)
      from assms(2) show "Es G2 \<subseteq> E_A" by (simp add: wf_g_def)
    next
      apply_end(rule conjI)
      show "ftotal_on (src G1 ++ src G2) (Es G1 \<union> Es G2) (Ns G1 \<union> Ns G2)"
      using assms dom_src_G[of G1] dom_src_G[of G2]
        ran_map_add_sub[where f="src G1" and g="src G2"]
        by (auto simp add: wf_g_def ftotal_on_def)
    next
      show "ftotal_on (tgt G1 ++ tgt G2) (Es G1 \<union> Es G2) (Ns G1 \<union> Ns G2)"
      using assms
        ran_map_add_sub[where f="tgt G1" and g="tgt G2"]
        by (auto simp add: ftotal_on_def wf_g_def)
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
      \<and> ftotal_on (fE r) (Es G1) (Es G2) 
      \<and> (fV r) \<circ>\<^sub>m (src G1) = (src G2) \<circ>\<^sub>m (fE r) 
      \<and> (fV r) \<circ>\<^sub>m (tgt G1) = (tgt G2) \<circ>\<^sub>m (fE r)}"

definition morphGrComp :: "Morph \<Rightarrow> Morph \<Rightarrow> Morph"
where
  "morphGrComp MG1 MG2 \<equiv> \<lparr>fV = (fV MG2) \<circ>\<^sub>m (fV MG1), fE = (fE MG2) \<circ>\<^sub>m (fE MG1) \<rparr>"

(*The empty graph morphism*)
definition emptyGM :: "Morph"
where
  "emptyGM \<equiv> \<lparr>fV = Map.empty, fE = Map.empty \<rparr>"

definition UGrM :: "'a Morph_scheme  \<Rightarrow> 'a Morph_scheme \<Rightarrow> Morph" (infixl "UGM" 100)
where
  "MG1 UGM MG2 \<equiv> \<lparr>fV= (fV MG1)++(fV MG2), fE = (fE MG1)++(fE MG2)\<rparr>"

lemma fVL_UGM[simp]: "fV (ML1 UGM ML2) = (fV ML1)++(fV ML2)"
  by (simp add: UGrM_def)

lemma fEL_UGM[simp]: "fE (ML1 UGM ML2) = (fE ML1)++(fE ML2)"
  by (simp add: UGrM_def)

end
