
(********  
  Title:      Theory of Base Graphs, base of Fragmenta's Graphs
  Author:     Nuno Amálio
***********)

theory Base_Graphs
imports Main "../Extra/Map_Extra" "../Extra/Set_Extra"
begin

type_synonym V = string
type_synonym E = string

(*Defines universe of nodes and eges; these sets are mutually disjoint*) 
axiomatization
  V_A:: "V set"     (* set of vertice atoms*)
  and E_A:: "E set" (*set of edge atoms*)
where
  disj_V_E: "V_A \<inter> E_A = {}"

record Gr =
  Ns  :: "V set"
  Es  :: "E set"
  src :: "E \<rightharpoonup> V" (*\<rightharpoonup> is partial function; eq to: "E\<Rightarrow>V option"*)
  tgt :: "E \<rightharpoonup> V"

lemma Gr_eq: 
  shows "(G1 = G2) \<longleftrightarrow> Ns G1 = Ns G2 \<and> Es G1 = Es G2 \<and> src G1 = src G2 \<and> tgt G1 = tgt G2
    \<and> Gr.more G1 = Gr.more G2"
  by (auto)

(* Graph construction*)
definition consG :: "V set\<Rightarrow>E set\<Rightarrow>(E \<rightharpoonup> V)\<Rightarrow>(E \<rightharpoonup> V)\<Rightarrow>Gr"
  where
  "consG ns es s t \<equiv> \<lparr>Ns = ns, Es = es, src = s, tgt =t\<rparr>"

(*Conditions for a graph to be well-formed*)
definition wf_g :: "'a Gr_scheme \<Rightarrow> bool"
where
  "wf_g G \<equiv> (Ns G) \<subseteq> V_A \<and> (Es G) \<subseteq> E_A \<and>ftotal_on (src G) (Es G) (Ns G) 
    \<and> ftotal_on (tgt G) (Es G) (Ns G)"

lemma disjoint_WF_G: "wf_g G \<Longrightarrow> disjoint[Ns G, Es G]"
  using disj_V_E
  by (auto simp add: wf_g_def)

lemma ftotal_on_src_G:
  assumes "wf_g G"
  shows "ftotal_on (src G)(Es G)(Ns G)"
  using assms by (simp add: wf_g_def)

lemma dom_src_G:
  assumes "wf_g G"
  shows "dom (src G) = Es G"
  using assms ftotal_on_src_G [of G] 
  by (simp add: ftotal_on_def)

lemma ran_src_G:
  assumes "wf_g G"
  shows "ran (src G) \<subseteq> Ns G"
  using assms ftotal_on_src_G [of G] 
  by (simp add: ftotal_on_def)

lemma ftotal_on_tgt_G:
  assumes "wf_g G"
  shows "ftotal_on (tgt G)(Es G)(Ns G)"
  using assms by (simp add: wf_g_def)

lemma dom_tgt_G:
  assumes "wf_g G"
  shows "dom (tgt G) = Es G"
  using assms ftotal_on_tgt_G[of G] 
  by (simp add: ftotal_on_def)

lemma ran_tgt_G:
  assumes "wf_g G"
  shows "ran (tgt G) \<subseteq> Ns G"
  using assms ftotal_on_tgt_G[of G] 
  by (simp add: ftotal_on_def)

(*Self edges*)
definition EsId ::"'a Gr_scheme \<Rightarrow> E set"
where
  "EsId G \<equiv> {e. e \<in> Es G \<and> (src G e) = (tgt G e)}"

definition adjacent :: "'a Gr_scheme => V \<Rightarrow> V \<Rightarrow> bool"
where
    "adjacent G v1 v2  \<equiv>  \<exists>e. e \<in> (Es G) \<and> src G e = Some v1 \<and> tgt G e = Some v2"

definition successors :: "V \<Rightarrow> Gr \<Rightarrow> V set"
where
    "successors v G = {v' \<in> (Ns G). (adjacent G v v')}"

(*Adjacency relation induced by a graph*)
definition relG :: "'a Gr_scheme \<Rightarrow> V rel" ("(_\<^sup>\<Leftrightarrow>)" [1000] 999)
where
   "G\<^sup>\<Leftrightarrow> = {(v1, v2). adjacent G v1 v2}"

lemma Domain_relG: "Domain (G\<^sup>\<Leftrightarrow>) \<subseteq> ran (src G)"
  by (auto simp add: relG_def adjacent_def ran_def)

lemma Range_relG: "Range (G\<^sup>\<Leftrightarrow>) \<subseteq> ran (tgt G)"
  by (auto simp add: relG_def adjacent_def ran_def)

definition acyclicGr :: "'a Gr_scheme \<Rightarrow> bool"
where
   "acyclicGr G \<equiv> acyclic (G\<^sup>\<Leftrightarrow>)"

lemma Domain_RelGr_Sub_NsG: 
  assumes "wf_g G"
  shows "Domain (G\<^sup>\<Leftrightarrow>) \<subseteq> Ns G"
  using assms by (auto simp add: relG_def 
      adjacent_def wf_g_def ftotal_on_def intro: ranI)

lemma acyclicIffForAll: 
  assumes h1: "wf_g G"
  shows "acyclicGr G \<longleftrightarrow> (\<forall>x. x \<in> Ns G \<longrightarrow> (x, x) \<notin> (G\<^sup>\<Leftrightarrow>)\<^sup>+)"
  proof
    assume h2: "acyclicGr G"
    show "\<forall>x. x \<in> Ns G \<longrightarrow> (x, x) \<notin> (G\<^sup>\<Leftrightarrow>)\<^sup>+"
    proof (rule allI, rule impI)
      fix x
      assume h3: "x \<in> Ns G"
      then show "(x, x) \<notin> (G\<^sup>\<Leftrightarrow>)\<^sup>+"
        using h2 by (auto simp add: acyclicGr_def acyclic_def)
    qed
  next
    assume "\<forall>x. x \<in> Ns G \<longrightarrow> (x, x) \<notin> (G\<^sup>\<Leftrightarrow>)\<^sup>+"
      then have "\<forall>x. (x, x) \<notin> (G\<^sup>\<Leftrightarrow>)\<^sup>+" 
      proof (clarify)
        fix x
        assume "\<forall>x. x \<in> Ns G \<longrightarrow> (x, x) \<notin> (G\<^sup>\<Leftrightarrow>)\<^sup>+"
        then have h2: "x \<in> Ns G \<longrightarrow> (x, x) \<notin> (G\<^sup>\<Leftrightarrow>)\<^sup>+"
          by (drule_tac x = "x" in spec)
        assume h3: "(x, x) \<in> (G\<^sup>\<Leftrightarrow> )\<^sup>+"
        then have "x \<in> Domain ((G\<^sup>\<Leftrightarrow>)\<^sup>+)"
          by (auto simp add: Domain_def)
        then have "x \<in> Domain (G\<^sup>\<Leftrightarrow>)"
          by (simp)
        then have h4: "x \<in> Ns G"  
          using h1 Domain_RelGr_Sub_NsG by auto
        show "False"
          using h2 h3 h4 by auto
      qed
    then show "acyclicGr G"
      by (simp add: acyclicGr_def acyclic_def relG_def adjacent_def)
  qed

(*
definition incidentEsSrc :: "Gr \<Rightarrow> V \<Rightarrow> E set"
where
  "incidentEsSrc G v \<equiv> {e \<in> (Es G). src G e = Some v}"*)

(* Inverts a graph*)
definition invertG::"Gr \<Rightarrow> Gr" ("(_\<^sup>\<rightleftharpoons>)" [1000] 999)
  where
  "G\<^sup>\<rightleftharpoons> = \<lparr>Ns = Ns G, Es = Es G, src = tgt G, tgt = src G\<rparr>"

(* Obtains the incident edges of a set of nodes*)
definition esIncident::"'a Gr_scheme \<Rightarrow> V set \<Rightarrow> E set" (infixl "\<circ>\<rightarrow>\<circ>" 100)
  where
  "G \<circ>\<rightarrow>\<circ> vs \<equiv>  (src G) -` (Some ` vs) \<union> (tgt G) -` (Some ` vs)"

(* Obtains edges connecting a set of nodes*)
definition esConnect::"'a Gr_scheme \<Rightarrow> V set \<Rightarrow> E set" (infixl "\<bullet>\<leftrightarrow>\<bullet>" 100)
  where
  "G \<bullet>\<leftrightarrow>\<bullet> vs \<equiv>  (src G) -` (Some ` vs) \<inter> (tgt G) -` (Some ` vs)"


(* Empty graph*)
definition emptyG :: "Gr"  ("\<emptyset>\<^sub>G")
where
  "\<emptyset>\<^sub>G \<equiv> consG {} {}  Map.empty Map.empty"

lemma emptyG_eq:
  "\<emptyset>\<^sub>G = \<lparr>Ns = {}, Es = {}, src = Map.empty, tgt =Map.empty\<rparr>"
  by (simp add: emptyG_def consG_def)

lemma wf_emptyG:
  shows "wf_g \<emptyset>\<^sub>G"
  by (simp add: emptyG_eq wf_g_def)

lemma NotEmptyG_imp_non_empty_Ns:
  assumes "wf_g G" and "G \<noteq> \<emptyset>\<^sub>G"
  shows "Ns G  \<noteq> {}"
  proof (rule ccontr)
    assume "\<not>Ns G \<noteq> {}"
    hence "Ns G = {}" by auto
    hence "src G = Map.empty"
      using assms(1) ran_src_G[of G] 
      by (simp add: map_empty_if_ran_empty)
    have "tgt G = Map.empty"
      using \<open>Ns G = {}\<close> ran_tgt_G[of G] assms(1)
      by (simp add: map_empty_if_ran_empty)
    hence "Es G = {}"
      using dom_tgt_G[of G] assms(1) 
      by auto
    then show "False"
      using \<open>G \<noteq> \<emptyset>\<^sub>G\<close> \<open>Ns G = {}\<close> \<open>src G = Map.empty\<close>
      \<open>tgt G = Map.empty\<close>
     by (simp add: Gr_eq emptyG_def consG_def)
 qed  

(*lemma NotEmptyG_imp_non_empty_Es:
  assumes "wf_g G" and "G \<noteq> \<emptyset>\<^sub>G"
  shows "Es G  \<noteq> {}"
proof (rule ccontr)
  assume "\<not> Es G \<noteq> {}"
  hence "Es G = {}" by auto
  hence "src G = Map.empty"
    using assms(1) dom_src_G[of G] 
    by (simp) 
  have "tgt G = Map.empty"
    using assms(1) dom_tgt_G[of G] \<open>Es G = {}\<close>
    by (simp)
  then show "False"
    using 
    \<open>src G = Map.empty\<close> \<open>Es G = {}\<close>
      \<open>tgt G = Map.empty\<close>
    by (simp add: Gr_eq emptyG_def consG_def)*)

end