
(********  
  Title:      Theory of Base Graphs constituting the base of Fragmenta's Graphs
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

(*Conditions for a graph to be well-formed*)
definition is_wf_g :: "'a Gr_scheme \<Rightarrow> bool"
where
  "is_wf_g G \<equiv> (Ns G) \<subseteq> V_A \<and> (Es G) \<subseteq> E_A \<and>ftotal_on (src G) (Es G) (Ns G) 
    \<and> ftotal_on (tgt G) (Es G) (Ns G)"

lemma disjoint_WF_G: "is_wf_g G \<Longrightarrow> disjoint[Ns G, Es G]"
  using disj_V_E
  by (auto simp add: is_wf_g_def)

lemma src_gr_edge: "is_wf_g G \<Longrightarrow> e \<in> Es(G) \<Longrightarrow> \<exists> v. src G e = Some v"
  by (auto simp add: is_wf_g_def ftotal_on_def)

lemma tgt_gr_edge: "is_wf_g G \<Longrightarrow> e \<in> Es(G) \<Longrightarrow> \<exists> v. tgt G e = Some v"
  by (auto simp add: is_wf_g_def ftotal_on_def)

(*Self edges*)
definition EsId ::"'a Gr_scheme \<Rightarrow> E set"
where
  "EsId G \<equiv> {e. e \<in> Es G \<and> (src G e) = (tgt G e)}"

definition adjacent :: "V \<Rightarrow> V \<Rightarrow> 'a Gr_scheme => bool"
where
    "adjacent v1 v2 G \<equiv>  \<exists>e. e \<in> (Es G) \<and> src G e = Some v1 \<and> tgt G e = Some v2"

definition successors :: "V \<Rightarrow> Gr \<Rightarrow> V set"
where
    "successors v G = {v1 \<in> (Ns G). (adjacent v v1 G)}"

(* Obtains the incident source edges of a node*)
definition incidentEsSrc :: "Gr \<Rightarrow> V \<Rightarrow> E set"
where
  "incidentEsSrc G v \<equiv> {e \<in> (Es G). src G e = Some v}"

(*The adjacency relation induced by a graph*)
definition relOfGr :: "'a Gr_scheme \<Rightarrow> (V\<times>V) set"
where
   "relOfGr G = {(v1, v2). (adjacent v1 v2 G)}"

lemma Domain_relOfGr: "Domain (relOfGr G) \<subseteq> ran (src G)"
  by (auto simp add: relOfGr_def adjacent_def ran_def)

lemma Range_relOfGr: "Range (relOfGr G) \<subseteq> ran (tgt G)"
  by (auto simp add: relOfGr_def adjacent_def ran_def)

definition acyclicGr :: "'a Gr_scheme \<Rightarrow> bool"
where
   "acyclicGr G \<equiv> acyclic (relOfGr G)"

lemma Domain_RelGr_Sub_NsG: 
  assumes h1: "is_wf_g G"
  shows "Domain (relOfGr G) \<subseteq> Ns G"
    using h1 by (auto simp add: relOfGr_def adjacent_def is_wf_g_def ftotal_on_def intro: ranI)

lemma acyclicIffForAll: 
  assumes h1: "is_wf_g G"
  shows "acyclicGr G \<longleftrightarrow> (\<forall>x. x \<in> Ns G \<longrightarrow> (x, x) \<notin> (relOfGr G)\<^sup>+)"
  proof
    assume h2: "acyclicGr G"
    show "\<forall>x. x \<in> Ns G \<longrightarrow> (x, x) \<notin> (relOfGr G)\<^sup>+"
    proof (rule allI, rule impI)
      fix x
      assume h3: "x \<in> Ns G"
      then show "(x, x) \<notin> (relOfGr G)\<^sup>+"
        using h2 by (auto simp add: acyclicGr_def acyclic_def)
    qed
  next
    assume "\<forall>x. x \<in> Ns G \<longrightarrow> (x, x) \<notin> (relOfGr G)\<^sup>+"
      then have "\<forall>x. (x, x) \<notin> (relOfGr G)\<^sup>+" 
      proof (clarify)
        fix x
        assume "\<forall>x. x \<in> Ns G \<longrightarrow> (x, x) \<notin> (relOfGr G)\<^sup>+"
        then have h2: "x \<in> Ns G \<longrightarrow> (x, x) \<notin> (relOfGr G)\<^sup>+"
          by (drule_tac x = "x" in spec)
        assume h3: "(x, x) \<in> (relOfGr G)\<^sup>+"
        then have "x \<in> Domain ((relOfGr G)\<^sup>+)"
          by (auto simp add: Domain_def)
        then have "x \<in> Domain (relOfGr G)"
          by (simp)
        then have h4: "x \<in> Ns G"  
          using h1 Domain_RelGr_Sub_NsG by auto
        show "False"
          using h2 h3 h4 by auto
      qed
    then show "acyclicGr G"
      by (simp add: acyclicGr_def acyclic_def relOfGr_def adjacent_def)
  qed

(* Defines the empty graph*)
definition emptyG :: "Gr"
where
  "emptyG \<equiv> \<lparr>Ns = {}, Es = {}, src = empty, tgt = empty\<rparr>"

end