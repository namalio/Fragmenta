(********  
  Title:      Theory of Base Graphs that constitutes the base of Fragmenta's Graphs
  Author:     Nuno Amálio
***********)

theory Base_GraphsL
imports Base_Graphs
begin

(* An alternative representation of Graphs based on a list of nodes and edges. 
 Better for computational purposes as it is easier to go from lists to sets 
than the other way round.*)
record Gr_ls =
  NsG  :: "V list"
  EsG  :: "E list"
  srcG :: "(E \<times> V) list" (*A list of (edge, vertice) pairs*)
  tgtG :: "(E \<times> V) list"

(* Defines the empty graph in listed version*)
definition emptyGL :: "Gr_ls"
where
  "emptyGL \<equiv> \<lparr>NsG = [], EsG = [], srcG = [], tgtG = []\<rparr>"

(*A function that converts the list-based representation to the set-based one*)
definition toGr :: "'a Gr_ls_scheme \<Rightarrow> Gr"
where
  "toGr GL \<equiv> \<lparr>Ns = set (NsG GL), Es = set (EsG GL), 
    src = map_of (srcG GL), tgt = map_of (tgtG GL)\<rparr>"

lemma in_set_EsG: "e \<in> set (EsG GL) \<longleftrightarrow> e \<in> Es (toGr GL)"
  by (simp add: toGr_def)

(* The list version of the incident source edges of a node*)
primrec incidentEsSrc_ls_0 :: "E list \<Rightarrow> Gr \<Rightarrow> V \<Rightarrow> E list"
where
  "incidentEsSrc_ls_0 [] GL v = []" 
  | "incidentEsSrc_ls_0 (e#el) GL v = 
    (let el2 = (incidentEsSrc_ls_0 el GL v) in
      (if src GL e = Some v then e#el2 else el2))"

definition incidentEsSrc_ls :: "Gr_ls \<Rightarrow> V \<Rightarrow> E list"
where
  "incidentEsSrc_ls G v \<equiv> (incidentEsSrc_ls_0 (EsG G) (toGr G) v)" 

(* Obtains the incident target edges of a node*)
definition incidentEsTgt :: "Gr \<Rightarrow> V => E set"
where
  "incidentEsTgt G v \<equiv> {e \<in> (Es G). tgt G e = Some v}" 

(* Obtains nodes without successors*)
primrec nonOutNodes0 :: "Gr_ls \<Rightarrow> V list \<Rightarrow>V list"
where
  "nonOutNodes0 G [] = []"
  | "nonOutNodes0 G (v#vs) = (if (incidentEsSrc_ls G v) = [] 
    then nonOutNodes0 G vs
    else v#nonOutNodes0 G vs)"

definition nonOutNodes :: "Gr_ls \<Rightarrow> V list"
where
  "nonOutNodes G \<equiv> nonOutNodes0 G (NsG G)" 

definition consRelE:: "'a Gr_scheme \<Rightarrow> E \<Rightarrow> (V\<times>V) list"
where
  "consRelE G e  \<equiv> (if e \<in> Es G then [(the (src G e),  the (tgt G e))] 
      else [])"

primrec consRel0:: "'a Gr_scheme \<Rightarrow> E list \<Rightarrow> (V\<times>V) list"
where
  "consRel0 G [] = []"
  | "consRel0 G (e#es) = (consRelE G e)@(consRel0 G es)"

lemma in_consRel0_insertls: 
  "(x, y) \<in> set(consRel0 G (e # es)) \<longleftrightarrow> (x, y) \<in> set(consRelE G e) \<union> set(consRel0 G es)"
  by simp

lemma in_consRel0:
  fixes x y es 
  assumes ha: "set es \<subseteq> Es G" and hb: "is_wf_g G"
  shows "(x, y) \<in> set(consRel0 G es) \<longleftrightarrow> 
    (\<exists> e. e \<in> (set es) \<and> (src G) e  = Some x \<and> (tgt G) e = Some y)"
  proof
    assume hd: "(x, y) \<in> set(consRel0 G es)"
    then show "\<exists>e. e \<in> set es \<and> src G e = Some x \<and> tgt G e = Some y"
    proof (induct es, simp)
      fix a es'
      assume he: "(x, y) \<in> set(consRel0 G es') \<Longrightarrow>
        \<exists>e. e \<in> set es' \<and> src G e = Some x \<and> tgt G e = Some y"
      assume hf: "(x, y) \<in> set(consRel0 G (a # es'))"
      show "\<exists>e. e \<in> set (a # es') \<and> src G e = Some x \<and> tgt G e = Some y"
      proof (case_tac "a \<in> Es G")
        assume hg: "a \<in> Es G"
        from hf hg have hh: "(x, y) \<in> {(the (src G a), the (tgt G a))} \<union> set(consRel0 G es')"
          by (auto simp add: consRelE_def)
        then show "\<exists>e. e \<in> set (a # es') \<and> src G e = Some x \<and> tgt G e = Some y"
        proof (case_tac "(x, y) \<in> set(consRel0 G es')")
          assume "(x, y) \<in> set(consRel0 G es')"
          then show "\<exists>e. e \<in> set (a # es') \<and> src G e = Some x \<and> tgt G e = Some y"
            using hh he by (auto)
        next
          from ha hg hb have hi: "a \<in> dom (src G)"
            by (auto simp add: is_wf_g_def ftotal_on_def)
          from hg hb have hj: "a \<in> dom (tgt G)"
            by (auto simp add: is_wf_g_def ftotal_on_def)
          assume "(x, y) \<notin> set(consRel0 G es')"
          then have "(x, y) \<in> {(the (src G a), the (tgt G a))}"
            using hh by simp
          then have "src G a = Some x \<and> tgt G a = Some y"
            using hi hj by (simp add: domD)
          then show "\<exists>e. e \<in> set (a # es') \<and> src G e = Some x \<and> tgt G e = Some y"
            using hg by (auto)
        qed
      next
        assume hg: "\<not>(a \<in> Es G)"
        from hf hg have hh: "(x, y) \<in> set(consRel0 G es')" 
          by (auto simp add: consRelE_def)
        then have "\<exists>e. e \<in> set es' \<and> src G e = Some x \<and> tgt G e = Some y"
          using he by simp
        then show "\<exists>e. e \<in> set (a # es') \<and> src G e = Some x \<and> tgt G e = Some y"
          by (auto)
      qed
    qed
  next
    assume hd: "\<exists>e. e \<in> set es  \<and> src G e = Some x \<and> tgt G e = Some y"
    then show "(x, y) \<in> set(consRel0 G es)"
    proof (clarify)
      fix a
      assume he: "a \<in> set es"
      assume hg: "src G a = Some x"
      assume hh: "tgt G a = Some y"
      from he show "(x, y) \<in> set(consRel0 G es)"
      proof (induct es, simp)
        fix a' es'
        assume hi: "(a \<in> set es' \<Longrightarrow> (x, y) \<in> set(consRel0 G es'))"
        assume hj: "a \<in> set (a' # es')"
        show "(x, y) \<in> set(consRel0 G (a' # es'))"
        proof (simp add: in_consRel0_insertls, case_tac "a=a'")
          assume "a = a'"
          then show "(x, y) \<in> set(consRelE G a') \<or> (x, y) \<in> set(consRel0 G es')"
            using ha he hg hh hi by (auto simp add: consRelE_def)
        next
          assume hk: "a \<noteq> a'"
          show "(x, y) \<in> set(consRelE G a') \<or> (x, y) \<in> set(consRel0 G es')"
          proof (rule disjI2)
            from hj hk have "a \<in> set es'"
              by simp
            then have "(x, y) \<in> set(consRel0 G es')"
              using hi by simp
            then show "(x, y) \<in> set(consRel0 G es')"
              by simp
          qed
        qed
      qed
    qed
  qed

definition consRel:: "Gr_ls \<Rightarrow> (V\<times>V) list"
where
  "consRel GL \<equiv> consRel0 (toGr GL) (EsG GL)"

lemma in_consRel: 
  fixes x y
  assumes ha: "is_wf_g (toGr GL)"
  shows "(x, y) \<in> set(consRel GL)  \<longleftrightarrow> 
    (\<exists> e. e \<in> set (EsG GL) \<and> src (toGr GL) e  = Some x \<and> tgt (toGr GL) e = Some y)"
    proof -
      have hb: "set (EsG GL) \<subseteq> Es (toGr GL)" 
        by (auto simp add: toGr_def)
      show ?thesis
      proof
        assume "(x, y) \<in> set(consRel GL)"
        then have "(x, y) \<in> set(consRel0 (toGr GL) (EsG GL))"
          by (simp add: consRel_def)
        then have "(\<exists> e. e \<in> set (EsG GL) 
          \<and> src (toGr GL) e  = Some x 
          \<and> tgt (toGr GL) e = Some y)"
          using ha hb  
          by (simp add: in_consRel0)
        then 
        show "\<exists>e. e \<in> set (EsG GL) \<and> src (toGr GL) e = Some x \<and> tgt (toGr GL) e = Some y"
          by simp
      next
        assume "\<exists>e. e \<in> set (EsG GL) \<and> src (toGr GL) e = Some x \<and> tgt (toGr GL) e = Some y"
        then have "(x, y) \<in> set(consRel0 (toGr GL) (EsG GL))"
          using ha hb  
          by (simp add: in_consRel0)
        then show "(x, y) \<in> set(consRel GL)"
          by (simp add: consRel_def)
      qed
    qed

lemma relOfGr_eq_consRel:
  assumes ha: "is_wf_g (toGr GL)" 
  shows "relOfGr (toGr GL) = set(consRel GL)"
  proof
    show "set(consRel GL) \<subseteq> relOfGr (toGr GL)"
    proof (rule subrelI)
      fix x y
      have hc: "is_wf_g (toGr GL)"
        using ha by (simp add: toGr_def)
      assume "(x, y) \<in> set(consRel GL)"
      then have "\<exists> e. e \<in> Es (toGr GL) \<and> (src (toGr GL))e  = Some x \<and> (tgt (toGr GL)) e = Some y" 
        using hc by (simp add: in_consRel in_set_EsG)
      then show "(x, y) \<in> relOfGr (toGr GL)"
      proof (clarify)
        fix e 
        assume "e \<in> Es (toGr GL)"
        then have hb: "e \<in> Es (toGr GL)"
          by (simp add: in_set_EsG)
        assume hc: "src (toGr GL) e = Some x"
        assume hd: "tgt (toGr GL) e = Some y"
        show "(x, y) \<in> relOfGr (toGr GL)"
        using hb hc hd  ha
        by (simp add: relOfGr_def adjacent_def restrict_map_def EsId_def
           in_set_EsG)(rule exI[where x="e"], 
        auto simp add: is_wf_g_def ftotal_on_def)
      qed
    qed
  next
    show "relOfGr (toGr GL) \<subseteq> set(consRel GL)"
    proof (rule subrelI)
      fix x y
      assume "(x, y) \<in> relOfGr (toGr GL)"
      then have "\<exists>e. e \<in> Es (toGr GL) \<and> src (toGr GL) e = Some x \<and> tgt (toGr GL) e = Some y"
        using ha by (auto simp add: relOfGr_def adjacent_def 
          restrict_map_def EsId_def
          is_wf_g_def ftotal_on_def)
      then show "(x, y) \<in> set(consRel GL)"
        using ha by (simp add: in_consRel in_set_EsG)
    qed
  qed

end