(*  Title:      Fragmenta theory of structural graphs (SGs)
    Description: 'Fragmenta' theory of SGs presented in the Models 2015 paper.
    Author:     Nuno Amálio
*)
theory Fragmenta_SGs
imports Fragmenta_Graphs "../Extra/Trcl_Extra"

begin

(*Multiplicity values: a natural number or 0*)
datatype MultUVal = val nat | many ("*")

(*Multiplicities: either a range multiplicity or a single multiplicity value*)
datatype MultVal = rm nat MultUVal | sm MultUVal

definition ok_multVal :: "MultVal \<Rightarrow> bool"
where
  "ok_multVal mv \<equiv> (case mv of (rm n *) \<Rightarrow> True
      | (rm lb (val ub)) \<Rightarrow> lb \<le> ub 
      | (sm mv) \<Rightarrow> True)"

lemma ok_multVal_sm_many[simp]: "ok_multVal (sm *)"
  by (simp add: ok_multVal_def)

lemma ok_multVal_sm_one[simp]: "ok_multVal (sm (val (Suc 0)))"
  by (simp add: ok_multVal_def)

definition multOk :: "V set \<Rightarrow> MultVal \<Rightarrow> bool"
where
  "multOk vs mv \<equiv> ok_multVal mv 
      \<and> (case mv of (rm lb *) \<Rightarrow> card vs \<ge> lb 
        | (rm lb (val ub)) \<Rightarrow>card vs \<ge> lb \<and> card vs \<le> ub  
        | (sm *) \<Rightarrow> True 
        | (sm (val b)) \<Rightarrow> card vs = b)"

(* The node types of a SG: normal, abstract, proxy and enumeration*)
datatype SGNTy = nnrml | nabst | nprxy | nenum
datatype SGETy = einh | ecompbi | ecompuni | erelbi | ereluni | elnk | eref

definition SGNTy_set :: "SGNTy set"
where 
   "SGNTy_set = {nnrml, nabst, nprxy, nenum}"

definition SGETy_set :: "SGETy set"
where 
   "SGETy_set = {einh, ecompbi, ecompuni, erelbi, ereluni, elnk, eref}"

(*Type of SGs*)
record SGr = Gr +
   nty :: "V \<rightharpoonup> SGNTy"
   ety :: "E \<rightharpoonup> SGETy" 
   srcm  :: "E \<rightharpoonup> MultVal"
   tgtm  :: "E \<rightharpoonup> MultVal"

(* Defines the empty SG*)
definition emptySG :: "SGr"
where
  "emptySG \<equiv> \<lparr>Ns = {}, Es = {}, src = Map.empty, tgt = Map.empty, 
    nty = Map.empty, ety = Map.empty,
    srcm = Map.empty, tgtm = Map.empty\<rparr>"

lemma SGr_eq: 
  shows "(SG1 = SG2) \<longleftrightarrow> Ns SG1 = Ns SG2 \<and> Es SG1 = Es SG2 \<and> src SG1 = src SG2 
    \<and> tgt SG1 = tgt SG2 \<and> nty SG1 = nty SG2 \<and> ety SG1 = ety SG2 
    \<and> srcm SG1 = srcm SG2 \<and> tgtm SG1 = tgtm SG2 \<and> SGr.more SG1 = SGr.more SG2"
    by (auto)

definition gr_sg :: "SGr \<Rightarrow> Gr"
where
  "gr_sg SG = \<lparr>Ns = Ns SG, Es = Es SG, src = src SG, tgt = tgt SG\<rparr>"

(*Nodes of some type*)
definition NsTy ::"SGr \<Rightarrow> SGNTy option set \<Rightarrow> E set"
where
  "NsTy SG nts = (nty SG)-` nts"

(*Edges of some type*)
definition EsTy ::"SGr \<Rightarrow> SGETy option set \<Rightarrow> E set"
where
  "EsTy SG ets = (ety SG)-` ets"

(*Association edges*)
definition EsA ::"SGr \<Rightarrow> E set"
where
  "EsA SG \<equiv> EsTy SG {Some ecompbi, Some ecompuni, Some erelbi, Some ereluni, Some elnk}"

(*Inheritance edges*)
definition EsI ::"SGr \<Rightarrow> E set"
where
  "EsI SG \<equiv> EsTy SG {Some einh}"

(*Reference edges*)
definition EsR ::"SGr \<Rightarrow> E set"
where
  "EsR SG \<equiv> EsTy SG {Some eref}"

(*Proxy nodes*)
definition NsP ::"SGr \<Rightarrow> V set"
where
  "NsP SG \<equiv> NsTy SG {Some nprxy}"

(*Reference edges attached to proxies*)
definition EsRP ::"SGr \<Rightarrow> E set"
where
  "EsRP SG \<equiv> {e. e \<in> EsR SG \<and> (\<exists> v. (src SG e) = Some v \<and> v \<in> (NsP SG))}"

definition inhG ::"SGr \<Rightarrow> Gr"
where
  "inhG SG \<equiv> restrict SG ((EsI SG) - (EsId SG))"

lemma Ns_inhG[simp]: "Ns (inhG SG) = rst_Ns SG ((EsI SG) - (EsId SG))"
  by (simp add: inhG_def)

lemma Es_inhG[simp]: "Es (inhG SG) = Es SG \<inter> ((EsI SG) - (EsId SG))"
  by (simp add: inhG_def)

lemma src_inhG[simp]: "src (inhG SG) = rst_fun ((EsI SG) - (EsId SG)) (src SG)"
  by (simp add: inhG_def)

lemma tgt_inhG[simp]: "tgt (inhG SG) = rst_fun ((EsI SG) - (EsId SG)) (tgt SG)"
  by (simp add: inhG_def)

definition inh ::"SGr \<Rightarrow> (V\<times>V) set"
where
  "inh SG \<equiv> relOfGr (inhG SG)"

(*Above, Inheritance relation is inheritance edges minus dummy self inheritance edges*)
lemma inh_noedgesI: "EsI SG = {} \<Longrightarrow> inh SG = {}"
  by (simp add: EsI_def inh_def relOfGr_def adjacent_def restrict_def inhG_def)

lemma inh_eq: "relOfGr (inhG SG) = inh SG"
  by (simp add: inh_def)

lemma acyclic_sg_noEI:"EsI SG = {} \<Longrightarrow> acyclicGr (inhG SG)"
  by (simp add: acyclicGr_def inh_eq inh_noedgesI wf_acyclic)

      
(*definition acyclicI :: "SGr \<Rightarrow> bool"
where
  "acyclicI SG \<equiv> acyclic (inh SG)"

lemma acyclic_sg_noEI:"EsI SG = {} \<Longrightarrow> acyclicI SG"
  by (auto simp add: acyclicI inh_noedgesI acyclicI_def)*)

definition is_wf_sg :: "SGr \<Rightarrow> bool"
where
  "is_wf_sg SG \<equiv> wf_g SG 
      \<and> ftotal_on (nty SG) (Ns SG) SGNTy_set 
      \<and> ftotal_on (ety SG) (Es SG) SGETy_set 
      \<and> dom (srcm SG) = EsTy SG {Some erelbi, Some ecompbi} 
      \<and> dom (tgtm SG) = EsTy SG {Some erelbi, Some ereluni, Some ecompbi, Some ecompuni}
      \<and> EsR SG \<subseteq> EsId SG 
      \<and> (srcm SG `(EsTy SG {Some ecompbi})) \<subseteq> {Some (rm 0 (val 1)), Some (sm (val 1))}
      \<and> acyclicGr (inhG SG)"

lemma NsP_sub_Ns: 
  assumes h1: "is_wf_sg SG"
  shows "NsP SG \<subseteq> Ns SG"
  proof -
    from h1 have h1a: "ftotal_on (nty SG) (Ns SG) SGNTy_set"
      by (simp add: is_wf_sg_def) 
    show ?thesis
    proof
      fix x
      assume "x \<in> NsP SG "
      then show "x \<in> Ns SG" 
        using h1a by (auto simp add: NsP_def NsTy_def ftotal_on_def)
    qed
  qed

lemma is_wf_g_inhG:
  assumes h1: "is_wf_g SG"
  shows "is_wf_g (inhG SG)"
proof -
  from h1 show ?thesis
    by (simp add: inhG_def is_wf_restrict)
qed

lemma in_NsP_Ns: 
  assumes h1: "is_wf_sg SG" and h2: "n \<in> NsP SG"
  shows "n \<in> Ns SG"
  proof -
    from assms show ?thesis
      using NsP_sub_Ns[where SG="SG"]
      by (auto)
  qed

lemma EsI_sub_Es: 
  assumes h1: "is_wf_sg SG"
  shows "EsI SG \<subseteq> Es SG"
  proof -
    from h1 have h1a: "ftotal_on (ety SG) (Es SG) SGETy_set"
      by (simp add: is_wf_sg_def)
    from h1a show ?thesis
      by (auto simp add: EsI_def EsTy_def ftotal_on_def)
  qed

lemma in_EsI_in_Es:
  assumes h1: "is_wf_sg SG" and h2: "x \<in> EsI SG"
  shows "x \<in> (Es SG)"
  proof -
    from assms show ?thesis
    using EsI_sub_Es [of "SG"]
    by (auto) 
  qed

(*All edges that are attached to proxies*)
definition EsP:: "SGr \<Rightarrow> E set"
where
  "EsP SG \<equiv> {e. e \<in> Es SG \<and> (src SG e \<in> Some ` NsP SG \<or> tgt SG e \<in> Some ` NsP SG)}"

definition inhGWithoutNsP:: "SGr\<Rightarrow>Gr"
where
  "inhGWithoutNsP SG \<equiv> restrict (inhG SG) (Es (inhG SG) - EsP (SG))" 

lemma No_NsP_in_inhGWithoutNsP: "Ns(inhGWithoutNsP SG) \<inter> NsP SG = {}"
  by (auto simp add: inhGWithoutNsP_def rst_Ns_def rst_fun_def restrict_map_def
    ran_def EsP_def)

definition inhGRestrictedToNsP:: "SGr\<Rightarrow>Gr"
where
  "inhGRestrictedToNsP SG \<equiv> restrict (inhG SG) (EsP SG)" 

lemma inhG_partition_NsP:
  assumes h:"is_wf_sg SG"
  shows "inhG SG = inhGWithoutNsP SG UG inhGRestrictedToNsP SG"
  proof -
    from h have h1a: "dom (src SG) = Es SG"
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h have h1b: "dom (tgt SG) = Es SG"
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    show ?thesis
    proof (simp add: inhGWithoutNsP_def inhGRestrictedToNsP_def Gr_eq, rule conjI)
      show "rst_Ns SG (EsI SG - EsId SG) =
        rst_Ns (inhG SG) (Es SG \<inter> (EsI SG - EsId SG) - EsP SG) \<union> rst_Ns (inhG SG) (EsP SG)"
        using h h1a h1b 
        by (auto simp add: rst_Ns_def rst_fun_def ran_def restrict_map_def intro!: in_EsI_in_Es)
    next
      apply_end(rule conjI)
      show "Es SG \<inter> (EsI SG - EsId SG) =
        Es SG \<inter> (EsI SG - EsId SG) \<inter> (Es SG \<inter> (EsI SG - EsId SG) - EsP SG) \<union>
          Es SG \<inter> (EsI SG - EsId SG) \<inter> EsP SG"
        by (auto)
    next
      apply_end(rule conjI)
      show "rst_fun (EsI SG - EsId SG) (src SG) =
          rst_fun (Es SG \<inter> (EsI SG - EsId SG) - EsP SG) (rst_fun (EsI SG - EsId SG) (src SG)) ++
          rst_fun (EsP SG) (rst_fun (EsI SG - EsId SG) (src SG))"
        using h1a by (auto simp add: fun_eq_iff rst_fun_def restrict_map_def map_add_def 
          split: option.splits)
    next
      show "rst_fun (EsI SG - EsId SG) (tgt SG) =
        rst_fun (Es SG \<inter> (EsI SG - EsId SG) - EsP SG) (rst_fun (EsI SG - EsId SG) (tgt SG)) ++
        rst_fun (EsP SG) (rst_fun (EsI SG - EsId SG) (tgt SG))"
        using h1b by (auto simp add: fun_eq_iff rst_fun_def restrict_map_def  
          map_add_def split: option.splits)
    qed
  qed

(*lemma in_Es_removeNsP_inhG:
  assumes h1: "is_wf_sg SG" and h2: "e \<in> Es (removeNs (inhG SG) (NsP SG))" and h3: "p \<in> NsP SG"
  shows "src SG e \<noteq> Some p \<and> tgt SG e \<noteq> Some p"
  proof -
    from h1 have h1a: "dom (src SG) = Es SG" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1b: "dom (tgt SG) = Es SG" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from assms h1a h1b show ?thesis
      by (auto simp add: rst_fun_def restrict_map_def)
  qed

lemma All_Prxys_in_removeNsNotAdjP_inhG:
  assumes h1: "is_wf_sg SG" 
  shows "\<forall> p. p \<in> NsP SG \<longrightarrow> p \<in> Ns (removeNs (inhG SG) (NsNotAdjP SG))"
  using h1 by (simp add: NsNotAdjP_def NsAdjP_def in_NsP_Ns)

lemma in_Es_implies_hasP_inhG:
  assumes h1: "is_wf_sg SG" and h2: "e \<in> Es (removeNs (inhG SG) (NsNotAdjP SG))" 
  shows "\<exists> p. p \<in> NsP SG"
  proof -
    from h1 have h1a: "dom (src SG) = Es SG" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1b: "dom (tgt SG) = Es SG" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1c: "ran (src SG) \<subseteq> Ns SG" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1d: "ran (tgt SG) \<subseteq> Ns SG" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1a h1b h2 show ?thesis
    proof (simp add: rst_fun_def restrict_map_def split: if_splits)
      apply_end(erule conjE, erule conjE, erule conjE, erule conjE)
      assume h3a: "e \<in> Es SG"
      assume h3b: "e \<in> EsI SG"
      assume h3c: "e \<notin> EsId SG" 
      assume h3d: "src SG e \<notin> Some ` NsNotAdjP SG"
      assume h3e: "tgt SG e \<notin> Some ` NsNotAdjP SG"
      from h3a h1a have h3f: "e \<in> dom (src SG)" by simp
      from h3a h1b have h3g: "e \<in> dom (tgt SG)" by simp
      from h3d h3f h1c have h3h: "src SG e \<in> Some ` NsAdjP SG"
        by (simp add: image_def dom_def NsNotAdjP_def)(erule exE, auto intro: ranI)
      from h3e h3g h1d have h3i: "tgt SG e \<in> Some ` NsAdjP SG"
        by (simp add: image_def dom_def NsNotAdjP_def)(erule exE, auto intro: ranI)
      from h3h h3i show ?thesis by (auto simp add: NsAdjP_def)
     next
    qed
  qed

lemma in_Es_removeNsNotAdjP_inhG:
  assumes h1: "is_wf_sg SG" and h2: "e \<in> Es (removeNs (inhG SG) (NsNotAdjP SG))" 
  shows "\<exists> p. p \<in> NsP SG \<and> (src SG e = Some p \<or> tgt SG e = Some p)"
  proof -
    from h1 have h1a: "is_wf_g SG"
      by (simp add: is_wf_sg_def)
    from h1a have h1b: "dom (src SG) = Es SG" 
      by (simp add: is_wf_g_def ftotal_on_def)
    from h1a have h1c: "dom (tgt SG) = Es SG" 
      by (simp add: is_wf_g_def ftotal_on_def)
    from h1a have h1d: "ran (src SG) \<subseteq> Ns SG" 
      by (simp add: is_wf_g_def ftotal_on_def)
    from h1a have h1e: "ran (tgt SG) \<subseteq> Ns SG" 
      by (simp add: is_wf_g_def ftotal_on_def)
    from h1 have h1f: "is_wf_g (inhG SG)"
      by (simp add: is_wf_g_inhG)
    from h1f have h1g: "is_wf_g (removeNs (inhG SG) (NsNotAdjP SG))"
      using is_wf_remove[where G="inhG SG" and ns="NsNotAdjP SG"]
      by (simp)
    from h2 h1g have h2a: "e \<in> dom (src (removeNs (inhG SG) (NsNotAdjP SG)))"
      by (simp add: is_wf_g_def ftotal_on_def)
    from h2 h1g have h2b: "e \<in> dom (tgt (removeNs (inhG SG) (NsNotAdjP SG)))"
      by (simp add: is_wf_g_def ftotal_on_def)
    from h1b h1c h2 show ?thesis
    proof (simp add: rst_fun_def restrict_map_def split: if_splits)
      apply_end(erule conjE, erule conjE, erule conjE, erule conjE)
      assume h3a: "e \<in> Es SG"
      from h3a h1b have h3b: "e \<in> dom (src SG)" by simp
      from h3a h1c have h3c: "e \<in> dom (tgt SG)" by simp
      assume h3d: "e \<in> EsI SG"
      assume h3e: "e \<notin> EsId SG" 
      assume h3f: "src SG e \<notin> Some ` NsNotAdjP SG"
      hence h3g: "src SG e \<notin> Some ` NsNotAdjP SG \<longrightarrow> src SG e \<in> Some ` NsAdjP SG"
        using h3b h1d
        by (simp add: image_def dom_def NsNotAdjP_def)(erule exE, auto intro: ranI)
      assume h3h: "tgt SG e \<notin> Some ` NsNotAdjP SG"
      hence h3i: "tgt SG e \<in> Some ` NsAdjP SG"
        using h3c h1e
        by (simp add: image_def dom_def NsNotAdjP_def)(erule exE, auto intro: ranI)
      have h2c: "\<exists>v1 v2. src (removeNs (inhG SG) (NsNotAdjP SG)) e = Some v1
        \<and> tgt (removeNs (inhG SG) (NsNotAdjP SG)) e = Some v2 \<and> (v1 \<in> NsP SG \<or> v2 \<in> NsP SG)"
      proof (simp)
      qed
        by (auto simp add: rst_fun_def rmv_EsOfNs_def restrict_map_def image_def NsNotAdjP_def 
          NsAdjP_def dom_def split: if_splits intro!: ranI)
      from h2a h2b h3a h3d h1d h1e 
        by (simp add: image_def dom_def NsNotAdjP_def)(erule exE, auto intro: ranI)
      have h3j: "\<exists> v1 v2 . src SG e \<in> Some ` NsP SG \<or> tgt SG e \<in> Some ` NsP SG"
        using h3b h3c  
        proof (simp add: image_def dom_def NsAdjP_def)
          apply_end(erule exE, erule exE)
          fix v1 v2
          assume ha: "src SG e = Some v1"
          assume hb: "tgt SG e = Some v2"
          show "(\<exists>x\<in>NsP SG. src SG e = Some x) \<or> (\<exists>x\<in>NsP SG. tgt SG e = Some x)"
          proof (case_tac "v1 \<in> NsP SG")
            assume hc: "v1 \<in> NsP SG"
            from ha hc show "(\<exists>x\<in>NsP SG. src SG e = Some x) \<or> (\<exists>x\<in>NsP SG. tgt SG e = Some x)"
              by auto
          next
            assume hc: "v1 \<notin> NsP SG"
            show "(\<exists>x\<in>NsP SG. src SG e = Some x) \<or> (\<exists>x\<in>NsP SG. tgt SG e = Some x)"
            proof (case_tac "v2 \<in> NsP SG")
              assume hd: "v2 \<in> NsP SG"
              from hb hd show "(\<exists>x\<in>NsP SG. src SG e = Some x) \<or> (\<exists>x\<in>NsP SG. tgt SG e = Some x)"
                by auto
            next
              assume hd: "v2 \<notin> NsP SG"
              from hc hd ha hb h3g h3i show "(\<exists>x\<in>NsP SG. src SG e = Some x) \<or> (\<exists>x\<in>NsP SG. tgt SG e = Some x)"
                by (auto simp add: NsAdjP_def adjacent_def)
            qed
          qed
        qed
      assume h3h: "tgt SG e \<notin> Some ` NsNotAdjP SG"
      hence h3i: "\<exists> v. tgt SG e = Some v \<and> v \<in> NsAdjP SG"
         using h3c h1d by (simp add: image_def dom_def NsNotAdjP_def)
          (erule exE, auto intro: ranI)
      show "\<exists>p. p \<in> NsP SG \<and> (src SG e = Some p \<or> tgt SG e = Some p)"
      proof (rule ccontr)
        apply_end(simp)
        assume h4: "\<forall>p. p \<in> NsP SG \<longrightarrow> src SG e \<noteq> Some p \<and> tgt SG e \<noteq> Some p"
        from h3g show "False"
        proof
          apply_end(erule conjE)
          fix v1
          assume h5a: "src SG e = Some v1"
          assume h5b: "v1 \<in> NsAdjP SG"
          from h5a h5b h1c have h4c: "v1 \<in> NsP SG 
            \<or> (\<exists>p. p \<in> NsP SG \<and> (adjacent v1 p SG \<or> adjacent p v1 SG))"
            by (auto simp add: NsNotAdjP_def NsAdjP_def intro: ranI)
          show "False"
          proof (case_tac "v1 \<in> NsP SG")
            assume h6a: "v1 \<in> NsP SG"
            from h4 h6a have h6b: "src SG e \<noteq> Some v1 \<and> tgt SG e \<noteq> Some v1"
              by auto
            from h6b h5a show "False" by auto
          next
            assume h6: "v1 \<notin> NsP SG"
            from h3i show "False"
            proof
              apply_end(erule conjE)
              fix v2
              assume h7a: "tgt SG e = Some v2"
              assume h7b: "v2 \<notin> NsNotAdjP SG"
              from h7a h7b h1d have h7c: "v2 \<in> NsP SG 
                \<or> (\<exists>p. p \<in> NsP SG \<and> (adjacent v2 p SG \<or> adjacent p v2 SG))"
                by (auto simp add: NsNotAdjP_def NsAdjP_def intro: ranI)
                show "False"
                proof (case_tac "v2 \<in> NsP SG")
                  assume h8a: "v2 \<in> NsP SG"
                  from h4 h8a have h8b: "src SG e \<noteq> Some v2 \<and> tgt SG e \<noteq> Some v2"
                  by auto
                  from h8b h7a show "False" by auto
                next
                  assume h8a: "v2 \<notin> NsP SG"
                  from h6 h4c have h8b: "(\<exists>p. p \<in> NsP SG 
                    \<and> (adjacent v1 p SG \<or> adjacent p v1 SG))" by auto
                  from h8b show "False"
                  proof
                    apply_end(erule conjE)
                    fix p
                    assume h9a: "p \<in> NsP SG"
                    from h1 h9a have h9b: "p \<in> Ns SG" 
                      by (auto simp add: in_NsP_Ns)
                    assume h9c: "adjacent v1 p SG \<or> adjacent p v1 SG"
                    from h9a h4 have h9d: "src SG e \<noteq> Some p \<and> tgt SG e \<noteq> Some p"
                      by auto
                    from h1 h9b have h9e: "p \<in> NsAdjP SG \<or> p \<in> NsNotAdjP SG" 
                      by (simp add: in_NsAdjP_or_not)
                    from h9c h9d h9e show "False" 
                      by (auto simp add: NsAdjP_def NsNotAdjP_def adjacent_def)
        from h3i show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
        proof
          apply_end(erule conjE)
          fix v2
          assume h5a: "tgt SG e = Some v2"
          assume h5b: "v2 \<notin> NsNotAdjP SG"
          from h5a h5b h1d have h5c: "v2 \<in> NsP SG 
              \<or> (\<exists>p. p \<in> NsP SG \<and> (adjacent v2 p SG \<or> adjacent p v2 SG))"
            by (auto simp add: NsNotAdjP_def NsAdjP_def intro: ranI)
          from h4c show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
          proof 
            assume h6a: "v1 \<in> NsP SG"
            then show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
              using h4a by (rule_tac exI[where x="v1"])(auto)
          next
            apply_end(erule exE)
            fix p
            assume h6a: "p \<in> NsP SG \<and> (adjacent v1 p SG \<or> adjacent p v1 SG)"
            then show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
            proof (case_tac "p=v1")
              assume "p=v1"
              then show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
              using h4a h6a by (rule_tac exI[where x="p"])(auto simp add: adjacent_def)
            next
              assume h7a: "p\<noteq>v1"
              from h5c show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
              proof
                assume h8a: "v2 \<in> NsP SG"
                then show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
                using h5a by (rule_tac exI[where x="v2"])(auto)
              next
                apply_end(erule exE)
                fix p2
                assume h8a: "p2 \<in> NsP SG \<and> (adjacent v2 p2 SG \<or> adjacent p2 v2 SG)"
                from h6a h8a show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
                proof (case_tac "p=v2")
                  assume h8b: "p=v2"
                  from h6a h5a h8b show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
                    by (rule_tac exI[where x="p"])(auto simp add: adjacent_def)
                next
                  assume h8b: "p \<noteq> v2"
                  show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
                  proof (case_tac "p2=v1") 
                    assume "p2=v1"
                    then show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
                      using h8a h4a by (rule_tac exI[where x="p2"])(auto simp add: adjacent_def)
                  next
                    assume h8b: "p2\<noteq>v1"
                    show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
                    proof (case_tac "p2=v2")
                      assume h8c: "p2=v2"
                      from h6a h5a h8c show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
                        by (rule_tac exI[where x="p2"])(auto simp add: adjacent_def)
                    next
                      assume h8c: "p2\<noteq>v2" (*I AM HERE*)
                      from h6a show "\<exists>p. p \<in> NsP SG \<and> src SG e = Some p \<or> tgt SG e = Some p"
                      using h4a h6a by (rule_tac exI[where x="p"])(auto simp add: adjacent_def)
                      by (rule_tac exI[where x="p2"])(auto simp add: adjacent_def)
          
  qed*)
  

(*lemma inhG_partitions_disjEsGs:
  shows "disjEsGs (restrict (inhG SG) (Es (inhG SG) - EsP SG)) (restrict (inhG SG) (EsP SG))"
    by (auto simp add: disjEsGs_def)*)

lemma in_EsA_in_ES: "\<lbrakk>is_wf_sg SG; e \<in> EsA SG\<rbrakk> \<Longrightarrow> e \<in> Es SG"
  by (auto simp add: is_wf_sg_def EsA_def EsTy_def ftotal_on_def)

lemma src_aedge_sg: "\<lbrakk>is_wf_sg SG; e \<in> EsA SG\<rbrakk> \<Longrightarrow> \<exists> v. src SG e = Some v"
  by (frule in_EsA_in_ES, auto simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)

lemma tgt_aedge_sg: "\<lbrakk>is_wf_sg SG; e \<in> EsA SG\<rbrakk> \<Longrightarrow> \<exists> v. tgt SG e = Some v"
  by (frule in_EsA_in_ES, auto simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)

lemma Domain_inh:
  assumes h1: "is_wf_sg SG"
  shows "Domain (inh SG) \<subseteq> Ns SG"
  proof -
    from h1 have h1c: "ran (src SG) \<subseteq> Ns SG"
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    show ?thesis
      using h1c
      by (auto simp add: inh_def relOfGr_def adjacent_def rst_fun_def EsI_def EsId_def EsTy_def
        restrict_map_def inhG_def intro!: ranI)
  qed

lemma Range_inh:
  assumes h1: "is_wf_sg SG"
  shows "Range (inh SG) \<subseteq> Ns SG"
  proof -
    from h1 have h1a: "ran (tgt SG) \<subseteq> Ns SG"
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1a show ?thesis
    by (auto simp add: inh_def relOfGr_def adjacent_def rst_fun_def EsI_def EsId_def EsTy_def
      restrict_map_def inhG_def intro!: ranI)
  qed

lemma EsId_in_EsG:
  assumes h1: "is_wf_sg SG" and h2: "x \<in> EsId SG"
  shows "x \<in> Es SG"
  proof -
    from h1 have h1a: "ftotal_on (ety SG) (Es SG) SGETy_set " by (simp add: is_wf_sg_def)
    from h1a have h1b: "dom (ety SG) = Es SG" by (simp add:ftotal_on_def)
    from h1b h2 show ?thesis by (auto simp add: EsId_def EsTy_def vimage_def dom_def)
  qed

lemma SG_EsA_no_inh: 
  assumes h1: "Es SG = EsA SG" and h2: "is_wf_sg SG"
  shows "EsI SG = {}"
  proof 
    show "EsI SG \<subseteq> {}"
    proof
      fix y
      assume a1: "y \<in> EsI SG"
      show "y \<in> {}"
      proof (rule ccontr, simp)
        have a2: "ftotal_on (ety SG) (Es SG) SGETy_set" 
          using h2 by (simp add: is_wf_sg_def)
        have a3: "dom (ety SG) = (Es SG)" using a2 by (simp add: ftotal_on_dom)
        have a4: "y \<in> dom (ety SG)" using a1 a3 by (auto simp: EsI_def EsA_def EsTy_def)
        then show "False" 
        using a1 a2 a3 h1 by (auto simp: ftotal_on_def EsA_def EsI_def EsTy_def vimage_def)
     qed
  qed
  next
  show "{} \<subseteq> EsI SG" by (auto)
  qed

lemma EsR_sub_Es: 
  assumes h1: "is_wf_sg SG"
  shows "EsR SG \<subseteq> Es SG"
  proof -
    from h1 have h1a: "ftotal_on (ety SG) (Es SG) SGETy_set"
      by (simp add: is_wf_sg_def)
    from h1a show ?thesis
      by (auto simp add: EsR_def EsTy_def ftotal_on_def)
  qed

lemma in_EsR_in_Es:
  assumes h1: "is_wf_sg SG" and h2: "x \<in> EsR SG"
  shows "x \<in> (Es SG)"
  proof -
    from assms show ?thesis
    using EsR_sub_Es[where SG="SG"]
    by (auto) 
  qed

lemma EsRP_sub_Es: 
  assumes h1: "is_wf_sg SG"
  shows "EsRP SG \<subseteq> Es SG"
  proof -
    from h1 have h1a: "ftotal_on (ety SG) (Es SG) SGETy_set"
      by (simp add: is_wf_sg_def)
    from h1a show ?thesis
      by (auto simp add: EsRP_def EsR_def EsTy_def ftotal_on_def)
  qed

lemma in_EsRP_in_Es:
  assumes h1: "is_wf_sg SG" and h2: "e \<in> EsRP SG"
  shows "e \<in> Es SG"
  proof -
    from assms show ?thesis
    using EsRP_sub_Es[where SG="SG"]
    by (auto) 
  qed

lemma in_EsRP_src_proxy:
  assumes h1: "e \<in> EsRP SG"
  shows "\<exists> v. (src SG) e = Some v \<and> v \<in> (NsP SG)"
  using assms by (auto simp add: EsRP_def)

(*lemma SG_in_EsA:
  assumes "(ety SG) e = Some erelbi"
  shows "e \<in> EsA SG"
proof -
  from assms show ?thesis by (simp add: EsA_def EsTy_def)
qed*)

definition inhst ::"SGr \<Rightarrow> (V\<times>V) set"
where
  "inhst SG \<equiv> (inh SG)^*"

lemma inhst_inhid: "inh SG \<subseteq> Id \<Longrightarrow> inhst SG = Id"
  apply (simp add: inhst_def)
  by (simp add: rtrancl_subsetid)

lemma inhst_noinh: "inh SG = {} \<Longrightarrow> inhst SG = Id"
  by (simp add: inhst_def)

lemma inhst_rel: "inh SG = r \<Longrightarrow> inhst SG = r^*"
  by (simp add: inhst_def)

lemma inhst_inh_subsetid: "r \<subseteq> Id \<Longrightarrow> inhst SG = (inh SG-r)^*"
  unfolding inhst_def
  apply (insert "rtrancl_minus_subsetid"[where s = "r" and r ="inh SG"])
  apply (rule sym)
  by (simp)

lemma inhst_def_simp: "((inh SGI2)\<^sup>*)\<inverse> = ((inh SGI2)\<inverse>)\<^sup>*"
proof -
  show "((inh SGI2)\<^sup>*)\<inverse> = ((inh SGI2)\<inverse>)\<^sup>*" by (simp add: rtrancl_converse)
qed

lemma inhst_of_inh: "(v1, v2) \<in> inh SG \<Longrightarrow> (v1, v2) \<in> inhst SG"
  by (simp add: inhst_def)

lemma inhst_is_id:
  assumes ha: "Es SG = EsA SG" and hb: "is_wf_sg SG"
  shows "inhst SG = Id"
proof -
  have hc: "EsI SG = {}"  by (simp add: SG_EsA_no_inh ha hb)
  show "inhst SG = Id"
    using hc by (simp add: inh_noedgesI inhst_def)
qed

definition clan ::"V \<Rightarrow> SGr \<Rightarrow> V set"
where
  "clan v SG \<equiv> (inhst SG)\<inverse>``{v}"

lemma clan_reflex[simp]: "v \<in> clan v SG"
  by (simp add: clan_def inhst_def)

lemma clan_of_inhst: "(v1, v2) \<in> inhst SG \<Longrightarrow> v1 \<in> clan v2 SG"
  by (simp add: clan_def)

lemma clan_of_inh: "(v1, v2) \<in> inh SG \<Longrightarrow> v1 \<in> clan v2 SG"
  by (simp add: clan_def inhst_def)

definition srcst ::"SGr \<Rightarrow> (E\<times>V) set"
where
  "srcst SG \<equiv> (EsA (SG) \<lhd> pfunToRel(src SG)) O (inhst SG)\<inverse>"

(*{(e, v). e \<in> EsA (SG) \<and> (\<exists>v2. v \<in> (clan v2 SG) \<and> (src SG) e = Some v2)}"*)

lemma in_srcst_subeq_src:
  assumes ha: "Es SG = EsA SG" and hb: "is_wf_sg SG"
  shows "srcst SG \<subseteq> pfunToRel (src SG)"
proof (rule subrelI)
  fix x y 
  assume "(x, y) \<in> srcst SG"
  hence h2: "(src SG) x = Some y"
    using ha hb 
    by (simp add: srcst_def inhst_is_id)(simp add: EsA_def EsTy_def dres_def pfunToRel_def)
  thus "(x, y) \<in> pfunToRel (src SG)" by (auto simp: pfunToRel_def)
qed

lemma srcst_eq_src_EsA:
  assumes ha: "Es SG = EsA SG" and hb: "is_wf_sg SG"
  shows "srcst SG = pfunToRel (src SG)"
  proof
    show "srcst SG \<subseteq> pfunToRel (src SG)"
      using ha hb by (simp add: in_srcst_subeq_src)
  next
    show "pfunToRel (src SG) \<subseteq> srcst SG"
    proof (rule subrelI)
      fix x y 
      assume b1: "(x, y) \<in> pfunToRel (src SG)"
      hence b2: "(src SG) x = Some y"
        by (auto simp: pfunToRel_def)
      have b3: "ftotal_on (src SG) (Es SG) (Ns SG)" 
        using hb by (simp add: is_wf_sg_def is_wf_g_def)
      have b4: "x \<in> Es SG" using b2 b3 by (auto simp add: ftotal_on_def dom_def)
      have b5: "x : EsA SG" using b4 ha by (auto)
      have b6: "EsI SG = {}" using ha hb by (rule SG_EsA_no_inh)
      thus "(x, y) \<in> srcst SG"
        by (simp add: b1 b5 dres_def ha hb inhst_is_id srcst_def)

   qed
qed

lemma e_v_src_in_srcst: "e \<in> EsA SG \<Longrightarrow> src SG e = Some v \<Longrightarrow> (e, v) \<in> srcst SG"
  by (auto simp add: srcst_def dres_def pfunToRel_def inhst_def)

lemma the_src_in_srcst: 
  assumes "is_wf_sg SG" and "e \<in> EsA SG"
  shows "(e, the (src SG e)) \<in> srcst SG"
  proof -
    from assms have h1: "is_wf_g SG" by (simp add: is_wf_sg_def)
    show ?thesis
      by (simp add: assms(1) assms(2) e_v_src_in_srcst src_aedge_sg)
  qed

lemma srcpar_in_srcst: "e \<in> EsA SG \<Longrightarrow> src SG e = Some v1 \<Longrightarrow> v2 \<in> clan v1 SG  
  \<Longrightarrow> (e, v2) \<in> srcst SG"
  by (auto simp add: srcst_def dres_def pfunToRel_def inhst_def EsA_def clan_def)

definition tgtst ::"SGr \<Rightarrow> (E\<times>V) set"
where
  "tgtst SG \<equiv> (EsA (SG) \<lhd> pfunToRel(tgt SG)) O (inhst SG)\<inverse>"  
  (*"tgtst SG \<equiv> {(e, v). e \<in> EsA (SG) \<and> (\<exists>v2. v \<in> (clan v2 SG) \<and> (tgt SG) e = Some v2)}"*)

lemma tgt_in_tgtst: "\<lbrakk>e \<in> EsA SG; tgt SG e = Some v\<rbrakk> \<Longrightarrow> (e, v) \<in> tgtst SG"
  by (auto simp add: tgtst_def dres_def inhst_def pfunToRel_def)

lemma tgtpar_in_tgtst: "\<lbrakk>e \<in> EsA SG; tgt SG e = Some v1; v2 \<in> clan v1 SG\<rbrakk>  
  \<Longrightarrow> (e, v2) \<in> tgtst SG"
  by (auto simp add: tgtst_def dres_def inhst_def clan_def pfunToRel_def)

lemma the_tgt_in_tgtst: 
  assumes "is_wf_sg SG" and "e \<in> EsA SG"
  shows "(e, the (tgt SG e)) \<in> tgtst SG"
  proof -
    from assms have h1: "is_wf_g SG" by (simp add: is_wf_sg_def)
    show ?thesis
    by (simp add: assms(1) assms(2) tgt_aedge_sg tgt_in_tgtst)
  qed

(*The following lemmas shows that the source or target of an edge is also in the extended set if the edge is of type 
association. In short: 
+ If it is in src, it is in src*
+ If it is in tgt, it is in tgt*)
lemma "is_wf_sg SG \<Longrightarrow> pfunToRel(src SG |` (EsA SG)) \<subseteq> srcst SG"
  proof (rule subrelI)
    fix x y
    assume "(x, y) \<in> pfunToRel (src SG |` EsA SG) "
    then show "(x, y) \<in> srcst SG"
      by (auto simp add: srcst_def restrict_map_def pfunToRel_def inhst_def dres_def split: if_splits)
  qed

lemma "is_wf_sg SG \<Longrightarrow> pfunToRel(tgt SG |` (EsA SG)) \<subseteq> tgtst SG"
  proof (rule subrelI)
    fix x y
    assume "(x, y) \<in> pfunToRel (tgt SG |` EsA SG) "
    then show "(x, y) \<in> tgtst SG"
      by (auto simp add: tgtst_def dres_def restrict_map_def pfunToRel_def inhst_def split: if_splits)
  qed
 
(*lemma "\<lbrakk>is_wf_sg SG; e \<in> EsA(SG)\<rbrakk> \<Longrightarrow> \<exists> v. tgt SG e = Some v \<and> (e, v) \<in> tgtst SG"
  apply (frule tgt_aedge_sg, simp)
  apply (erule exE) 
  apply (rule_tac x="v" in exI)
  by (simp add: tgtst_def)*)

lemma "\<lbrakk>is_wf_sg SG; v1 \<in> Ns SG; v2 \<in> Ns SG; (v1, v2) \<in> inhst SG; e \<in> EsA(SG); src SG e = Some v2\<rbrakk> 
  \<Longrightarrow> (e, v1) \<in> srcst SG"  
    by (auto simp add: srcst_def inhst_def dres_def pfunToRel_def)  

definition cupSG :: "SGr \<Rightarrow> SGr \<Rightarrow> SGr" (infixl "USG" 100)
where
  "SG1 USG SG2 \<equiv> \<lparr>Ns = Ns SG1 \<union> Ns SG2, Es = Es SG1 \<union> Es SG2, src = src SG1 ++ src SG2, 
    tgt = tgt SG1 ++ tgt SG2, nty= nty SG1 ++ nty SG2, ety= ety SG1 ++ ety SG2, 
    srcm = srcm SG1 ++ srcm SG2, tgtm = tgtm SG1 ++ tgtm SG2\<rparr>"


lemma USG_sym: 
  assumes h1: "is_wf_sg SG1" and h2: "is_wf_sg SG2" and h3: "disjGs SG1 SG2"
  shows "SG1 USG SG2 = SG2 USG SG1"
  proof -
    from h1 have h1a: "dom (src SG1) = Es SG1" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1b: "dom (tgt SG1) = Es SG1" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1c: "dom (nty SG1) = Ns SG1" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1d: "dom (ety SG1) = Es SG1" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1e: "dom (srcm SG1) = EsTy SG1 {Some erelbi, Some ecompbi}" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1f: "dom (tgtm SG1) = EsTy SG1 {Some erelbi, Some ereluni, Some ecompuni, 
      Some ecompbi}" 
      by (auto simp add: is_wf_sg_def is_wf_g_def ftotal_on_def EsTy_def vimage_def)
    from h2 have h2a: "dom (src SG2) = Es SG2" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2b: "dom (tgt SG2) = Es SG2" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2c: "dom (nty SG2) = Ns SG2" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2d: "dom (ety SG2) = Es SG2" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2e: "dom (srcm SG2) = EsTy SG2 {Some erelbi, Some ecompbi}" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2f: "dom (tgtm SG2) = 
      EsTy SG2 {Some erelbi, Some ereluni, Some ecompbi, Some ecompuni}" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h3 have h3a: "Es SG1 \<inter> Es SG2 = {}" by (simp add:  disjGs_def disjEsGs_def)
    from h3 have h3b: "Ns SG1 \<inter> Ns SG2 = {}" by (simp add:  disjGs_def)
    from h3a h1a h2a have h3c: "dom (src SG1) \<inter> dom (src SG2) = {}"
      by auto
    from h3a h1b h2b have h3d: "dom (tgt SG1) \<inter> dom (tgt SG2) = {}"
      by auto
    from h3b h1c h2c have h3e: "dom (nty SG1) \<inter> dom (nty SG2) = {}"
      by auto
    from h3a h1d h2d have h3f: "dom (ety SG1) \<inter> dom (ety SG2) = {}"
      by auto
    from h3a h1d h2d h1e h2e have h3g: "dom (srcm SG1) \<inter> dom (srcm SG2) = {}"
      by (auto simp add: EsTy_def)
    from h3a h1d h2d h1f h2f have h3h: "dom (tgtm SG1) \<inter> dom (tgtm SG2) = {}"
      by (auto simp add: EsTy_def)
    show "SG1 USG SG2 = SG2 USG SG1"
    proof (auto simp add: cupSG_def)
      show "(src SG1) ++ (src SG2) = (src SG2) ++ (src SG1)"
        using h3c map_add_comm[of "src SG1" "src SG2"] by (simp)
    next
      show "tgt SG1 ++ tgt SG2 = tgt SG2 ++ tgt SG1"
        using h3d map_add_comm[of "tgt SG1" "tgt SG2"] by (simp)  
    next
      show "nty SG1 ++ nty SG2 = nty SG2 ++ nty SG1"
        using h3e map_add_comm[of "nty SG1" "nty SG2"] by (simp) 
    next
      show "ety SG1 ++ ety SG2 = ety SG2 ++ ety SG1"
        using h3f map_add_comm[of "ety SG1" "ety SG2"] by (simp)
    next
      show "srcm SG1 ++ srcm SG2 = srcm SG2 ++ srcm SG1"
      using h3g map_add_comm[of "srcm SG1" "srcm SG2"] by (simp)
    next
      show "tgtm SG1 ++ tgtm SG2 = tgtm SG2 ++ tgtm SG1"
      using h3h map_add_comm[of "tgtm SG1" "tgtm SG2"] by (simp)
    qed
  qed

lemma src_cupSG[simp]: "src (SG1 USG SG2) = src SG1 ++ src SG2"
  by (simp add: cupSG_def)

lemma tgt_cupSG[simp]: "tgt (SG1 USG SG2) = tgt SG1 ++ tgt SG2"
  by (simp add: cupSG_def)

lemma srcm_cupSG[simp]: "srcm (SG1 USG SG2) = srcm SG1 ++ srcm SG2"
  by (simp add: cupSG_def)

lemma restrict_dist_sgcup: 
  assumes h1: "is_wf_sg SG1" and h2: "is_wf_sg SG2" and h3: "disjEsGs SG1 SG2"
  shows "restrict (SG1 USG SG2) es = restrict SG1 es UG restrict SG2 es"
  proof -
    from h1 have h1a: "is_wf_g SG1" by (simp add: is_wf_sg_def)
    from h2 have h2a: "is_wf_g SG2" by (simp add: is_wf_sg_def)
    from h1a h2a h3 have h4: "restrict (SG1 USG SG2) es = restrict (SG1 UG SG2) es"
      by (simp add: cupSG_def restrict_def rst_Ns_dist_UG rst_Ns_def)
    from h1a h2a h3 show ?thesis by (simp add: h4 restrict_dist_cup)
  qed
  
lemma is_wf_g_Un2: "\<lbrakk>is_wf_g G1; is_wf_g G2; disjGs G1 G2\<rbrakk>\<Longrightarrow> is_wf_g (G1 USG G2)"
  proof -
    assume h1: "is_wf_g G1"
    have h1a: "ftotal_on (src G1) (Es G1) (Ns G1)"
      using h1 by (simp add: is_wf_g_def)
    have h1b: "ftotal_on (tgt G1) (Es G1) (Ns G1)"
      using h1 by (simp add: is_wf_g_def)
    have h1c: "dom (src G1) = Es G1"
      using h1a by (simp add: ftotal_on_def)
    have h1d: "dom (tgt G1) = Es G1"
      using h1b by (simp add: ftotal_on_def)
    assume h2: "is_wf_g G2"
    have h2a: "ftotal_on (src G2) (Es G2) (Ns G2)"
      using h2 by (simp add: is_wf_g_def)
    have h2b: "ftotal_on (tgt G2) (Es G2) (Ns G2)"
      using h2 by (simp add: is_wf_g_def)
    have h2c: "dom (src G2) = Es G2"
      using h2a by (simp add: ftotal_on_def)
    have h2d: "dom (tgt G2) = Es G2"
      using h2b by (simp add: ftotal_on_def)
    assume h3: "disjGs G1 G2"
    have h3a: "Es G1 \<inter> Es G2 = {}"
      using h3 by (simp add: disjGs_def disjEsGs_def)
    show "is_wf_g (G1 USG G2)"
    proof (simp add: is_wf_g_def cupSG_def, rule conjI)
      from h1 show "Ns G1 \<subseteq> V_A" 
        by (simp add: is_wf_g_def)
    next
      apply_end (rule conjI)
      from h2 show "Ns G2 \<subseteq> V_A"
        by (simp add: is_wf_g_def)
    next
      apply_end (rule conjI)
      from h1 show "Es G1 \<subseteq> E_A" by (simp add: is_wf_g_def)
    next
      apply_end (rule conjI)
      from h2 show "Es G2 \<subseteq> E_A" by (simp add: is_wf_g_def)
    next
      apply_end (rule conjI)
      show "ftotal_on (src G1 ++ src G2) (Es G1 \<union> Es G2) (Ns G1 \<union> Ns G2)"
      using h1a h2a h1c h2c h3a
        by (auto simp add: ftotal_on_def)
    next
      show "ftotal_on (tgt G1 ++ tgt G2) (Es G1 \<union> Es G2) (Ns G1 \<union> Ns G2)"
      using h1b h2b h1d h2d h3a
      by (auto simp add: ftotal_on_def)
   qed
 qed

lemma EsTy_USG: 
  assumes h1: "is_wf_sg SG1" and h2: "is_wf_sg SG2" and h3: "disjGs SG1 SG2"
    and h4: "None \<notin> ets"
  shows "EsTy (SG1 USG SG2) ets = EsTy SG1 ets \<union> EsTy SG2 ets"
  proof -
    from h3 have h3a: "Es SG1 \<inter> Es SG2 = {}"
      by (simp add: disjGs_def disjEsGs_def)
    have h5: "dom (ety SG1) \<inter> dom (ety SG2) = {}" 
      using h1 h2 h3a by (simp add: is_wf_sg_def ftotal_on_def)
    show ?thesis
      using h4 h5 by (simp add: EsTy_def cupSG_def map_add_dists_vimage)
  qed

lemma EsA_USG: 
  assumes h1: "is_wf_sg SG1" and h2: "is_wf_sg SG2" and h3: "disjGs SG1 SG2"
  shows "EsA (SG1 USG SG2) = (EsA SG1 \<union> EsA SG2)"
  using h1 h2 h3 by (simp add: EsA_def EsTy_USG)    

lemma EsR_disj_dist: 
  assumes h1: "is_wf_sg SG1" and h2: "is_wf_sg SG2" and h3: "disjGs SG1 SG2"
  shows "EsR (SG1 USG SG2) = (EsR SG1 \<union> EsR SG2)"
  using h1 h2 h3 by (simp add: EsR_def EsTy_USG) 

lemma NsP_disj_dist: "\<lbrakk>is_wf_sg SG1; is_wf_sg SG2; disjGs SG1 SG2\<rbrakk>
  \<Longrightarrow>NsP (SG1 USG SG2) = NsP SG1 \<union> NsP SG2"
  proof -
    assume h1: "disjGs SG1 SG2"
    have h1a: "Ns SG1 \<inter> Ns SG2 = {}"
      using h1 by (simp add: disjGs_def)
    assume h2: "is_wf_sg SG1"
    have h2a: "ftotal_on (nty SG1) (Ns SG1) SGNTy_set"
      using h2 by (simp add: is_wf_sg_def)
    assume h3: "is_wf_sg SG2"
    have h3a: "ftotal_on (nty SG2) (Ns SG2) SGNTy_set"
      using h3 by (simp add: is_wf_sg_def)
    have h4: "dom (nty SG1) \<inter> dom (nty SG2) = {}" 
        using h1a h2a h3a by (simp add: ftotal_on_def)
    have h5: "None \<notin>  {Some nprxy}" by simp
    show "NsP (SG1 USG SG2) = NsP SG1 \<union> NsP SG2"
      using h4 h5 by (simp add: NsP_def NsTy_def cupSG_def map_add_dists_vimage)
qed

lemma EsRP_Un_EsR_1: "\<lbrakk>disjGs SG1 SG2; is_wf_sg SG1; is_wf_sg SG2; 
  x \<in> EsR SG1; x \<in> EsRP SG1 \<or> x \<in> EsRP SG2\<rbrakk>
  \<Longrightarrow>x \<in> EsRP SG1"
  proof -
    assume h1: "disjGs SG1 SG2"
    have h1a: "Es SG1 \<inter> Es SG2 = {}"
      using h1 by (simp add: disjGs_def disjEsGs_def)
    assume h2: "is_wf_sg SG1"
    from h2 have h2a: "ftotal_on (ety SG1) (Es SG1) SGETy_set"
      by (simp add: is_wf_sg_def)
    assume h3: "is_wf_sg SG2"
    from h3 have h3a: "ftotal_on (ety SG2) (Es SG2) SGETy_set"
      by (simp add: is_wf_sg_def)
    assume h4: "x \<in> EsR SG1"
    from h4 have h4a: "x \<in> Es SG1"
      using h2a by (auto simp add: EsR_def EsTy_def ftotal_on_def)
    from h4 have h4b: "x \<notin> Es SG2" 
      using h3a h1a h2a by (auto simp add: EsR_def EsTy_def ftotal_on_def)
    from h4 have h4c: "x \<notin> EsR SG2" 
      using h3a h1a h4b by (auto simp add: EsR_def EsTy_def ftotal_on_def)
    assume h4: "x \<in> EsRP SG1 \<or> x \<in> EsRP SG2"
    show ?thesis
    using h1a h3 h3a h4 h4c by (simp add: EsRP_def)
  qed

lemma EsRP_disj_dist: "\<lbrakk>is_wf_sg SG1; is_wf_sg SG2; disjGs SG1 SG2\<rbrakk>
  \<Longrightarrow>EsRP (SG1 USG SG2) = EsRP SG1 \<union> EsRP SG2"
proof -
    assume h1: "disjGs SG1 SG2"
    have h1a: "Es SG1 \<inter> Es SG2 = {}"
      using h1 by (simp add: disjGs_def disjEsGs_def)
    have h1b: "Ns SG1 \<inter> Ns SG2 = {}"
      using h1 by (simp add: disjGs_def)
    assume h2: "is_wf_sg SG1"
    have h2a: "ftotal_on (ety SG1) (Es SG1) SGETy_set"
      using h2 by (simp add: is_wf_sg_def)
    have h2b: "ftotal_on (src SG1) (Es SG1) (Ns SG1)"
      using h2 by (simp add: is_wf_sg_def is_wf_g_def)
    from h2b have h2c: "dom (src SG1) = Es SG1"
      by (simp add: ftotal_on_def)
    from h2b have h2d: "ran (src SG1) \<subseteq> Ns SG1"
      by (simp add: ftotal_on_def)
    have "ftotal_on (nty SG1) (Ns SG1) SGNTy_set"
      using h2 by (simp add: is_wf_sg_def)
    then have h2e: "dom (nty SG1) = Ns SG1"
      by (simp add: ftotal_on_def)
    assume h3: "is_wf_sg SG2"
    have h3a: "ftotal_on (ety SG2) (Es SG2) SGETy_set"
      using h3 by (simp add: is_wf_sg_def)
    have h3b: "ftotal_on (src SG2) (Es SG2) (Ns SG2)"
      using h3 by (simp add: is_wf_sg_def is_wf_g_def)
    from h3b have h3c: "dom (src SG2) = Es SG2"
      by (simp add: ftotal_on_def)
    from h3b have h3d: "ran (src SG2) \<subseteq> Ns SG2"
      by (simp add: ftotal_on_def)
    have h4: "dom (ety SG1) \<inter> dom (ety SG2) = {}" 
      using h1a h2a h3a by (simp add: ftotal_on_dom)
    have h5: "dom (src SG1) \<inter> dom (src SG2) = {}"
      using h1a h2c h3c by simp
    from h4 have h6: "EsR SG1 \<inter> EsR SG2 = {}" 
      by (auto simp add: EsR_def EsTy_def vimage_def)
    show "EsRP (SG1 USG SG2) = EsRP SG1 \<union> EsRP SG2"
    proof
      show "EsRP (SG1 USG SG2) \<subseteq> EsRP SG1 \<union> EsRP SG2"
        proof
          fix x 
          assume h7: "x \<in> EsRP (SG1 USG SG2)"
          then have h7a: "x \<in> EsR SG1 \<or> x \<in> EsR SG2"
            using h1 h2 h3 by (simp add: EsRP_def EsR_disj_dist)
          from h7 show "x \<in> EsRP SG1 \<union> EsRP SG2"
            proof (case_tac "x \<in> EsR SG1")
              assume h8: "x \<in> EsR SG1"
              have h8a: "\<exists> v. src SG1 x = Some v \<and> v \<in> Ns SG1"
                using h8 h2 h2c h2d domD[where m="src SG1" and a ="x"]
                  ranI[where m="src SG1" and a ="x"]
                by (simp add: in_EsR_in_Es)(erule exE, auto)
              from h8 have h8c: "x \<in> EsRP SG1" 
                using h1 h2 h3 h7 h4 h5 h8a h2c h2d h1b
                by (simp add: EsRP_def EsR_disj_dist map_add_app_disj NsP_disj_dist in_EsR_in_Es)
                  (erule exE, auto simp add: in_NsP_Ns)
              from h8c show "x \<in> EsRP SG1 \<union> EsRP SG2"
                using h8 by (simp)
            next
              assume h8: "x \<notin> EsR SG1"
              show "x \<in> EsRP SG1 \<union> EsRP SG2"
              proof (case_tac "x \<in> EsR SG2")
                assume h9: "x \<in> EsR SG2"
              have h9a: "\<exists> v. src SG2 x = Some v \<and> v \<in> Ns SG2 \<and> v \<notin> Ns SG1"
                using h9 h3 h1b h3c h3d domD[where m="src SG2" and a ="x"]
                  ranI[where m="src SG2" and a ="x"]
                  EsR_sub_Es[where SG="SG2"]
                by (simp add: in_EsR_in_Es)(erule exE, auto)
              from h9 have h9c: "x \<in> EsRP SG2" 
                using h1 h2 h3 h7 h4 h5 h8 h9a h2c h3c h3d
                by (auto simp add: EsRP_def EsR_disj_dist map_add_app_disj NsP_disj_dist 
                  in_EsR_in_Es in_NsP_Ns split: if_splits)
              from h9c show "x \<in> EsRP SG1 \<union> EsRP SG2"
                by simp
            next
              assume h9: "x \<notin> EsR SG2"
              from h8 h9 show "x \<in> EsRP SG1 \<union> EsRP SG2"
                using h7a by simp
            qed
        qed
      qed
   next
      show "EsRP SG1 \<union> EsRP SG2 \<subseteq> EsRP (SG1 USG SG2)"
        proof
          fix x
          assume h7: "x \<in> EsRP SG1 \<union> EsRP SG2"
          from h7 have h7a: "x \<in> EsRP SG1 \<or> x \<in> EsRP SG2" 
            by simp
          show "x \<in> EsRP (SG1 USG SG2)"
          proof (case_tac "x \<in> EsRP SG1")
            assume h8: "x \<in> EsRP SG1"
            from h8 show "x \<in> EsRP (SG1 USG SG2)"
              using h1 h2 h3 h5 h2c
              by (auto simp add: EsRP_def EsR_disj_dist NsP_disj_dist map_add_app_disj
                in_EsR_in_Es)
          next
            assume h8: "x \<notin> EsRP SG1"
            from h8 h7a have h8a: "x \<in> EsRP SG2"
              by simp
            from h8a show "x \<in> EsRP (SG1 USG SG2)"
              using h1 h2 h3 h5 h2c
              by (auto simp add: EsRP_def EsR_disj_dist NsP_disj_dist map_add_app_disj
                in_EsR_in_Es)
          qed
        qed
   qed
qed 

lemma EsI_disj_dist: "\<lbrakk>is_wf_sg SG1; is_wf_sg SG2; disjGs SG1 SG2\<rbrakk>
  \<Longrightarrow>EsI (SG1 USG SG2) = EsI SG1 \<union> EsI SG2"
proof -
  assume h1: "disjGs SG1 SG2"
  have h1a: "Es SG1 \<inter> Es SG2 = {}"
      using h1 by (simp add: disjGs_def disjEsGs_def)
  assume h2: "is_wf_sg SG1"
  have h2a: "ftotal_on (ety SG1) (Es SG1) SGETy_set"
      using h2 by (simp add: is_wf_sg_def)
  assume h3: "is_wf_sg SG2"
  have h3a: "ftotal_on (ety SG2) (Es SG2) SGETy_set"
      using h3 by (simp add: is_wf_sg_def)
  have h4: "None \<notin>  {Some einh}"
    by simp
  have h5: "dom (ety SG1) \<inter> dom (ety SG2) = {}" 
        using h1a h2a h3a by (simp add: ftotal_on_dom)
  show "EsI (SG1 USG SG2) = EsI SG1 \<union> EsI SG2"
  using h4 h5 by (simp add: EsI_def EsTy_def cupSG_def map_add_dists_vimage)
qed

lemma EsId_disj_dist: "\<lbrakk>is_wf_sg SG1; is_wf_sg SG2; disjGs SG1 SG2\<rbrakk>
  \<Longrightarrow>EsId (SG1 USG SG2) = EsId SG1 \<union> EsId SG2"
  proof -
    assume h1: "disjGs SG1 SG2"
    have h1a: "Es SG1 \<inter> Es SG2 = {}"
      using h1 by (simp add: disjGs_def disjEsGs_def)
    assume h2: "is_wf_sg SG1"
    have h2a: "ftotal_on (src SG1) (Es SG1) (Ns SG1)"
      using h2 by (simp add: is_wf_sg_def is_wf_g_def)
    have h2b: "ftotal_on (tgt SG1) (Es SG1) (Ns SG1)"
      using h2 by (simp add: is_wf_sg_def is_wf_g_def)
    assume h3: "is_wf_sg SG2"
    have h3a: "ftotal_on (src SG2) (Es SG2) (Ns SG2)"
      using h3 by (simp add: is_wf_sg_def is_wf_g_def)
    have h3b: "ftotal_on (tgt SG2) (Es SG2) (Ns SG2)"
      using h3 by (simp add: is_wf_sg_def is_wf_g_def)
    have h4: "dom (src SG1) \<inter> dom (src SG2) = {}" 
        using h1a h2a h3a by (simp add: ftotal_on_dom)
    have h5: "dom (tgt SG1) \<inter> dom (tgt SG2) = {}" 
        using h1a h2b h3b by (simp add: ftotal_on_dom)
    show "EsId (SG1 USG SG2) = EsId SG1 \<union> EsId SG2"
    proof
      show "EsId (SG1 USG SG2) \<subseteq> EsId SG1 \<union> EsId SG2"
      proof
        fix x
        assume h6: "x \<in> EsId (SG1 USG SG2)"
        have h6b: "x \<in> Es SG1 \<union> Es SG2"
          using h6 by (simp add: cupSG_def EsId_def)
        show "x \<in> EsId SG1 \<union> EsId SG2"
        proof (case_tac "x \<in> Es SG1")
          assume h7: "x \<in> Es SG1"
          have h7a: "x \<in> dom (src SG1)"
            using h7 h4 h2a by (simp add: ftotal_on_dom)
          have h7b: "x \<in> dom (tgt SG1)"
            using h7 h4 h2b by (simp add: ftotal_on_dom)
          have h8: "(src SG1 ++ src SG2) x = (src SG1) x" 
            using h7a h4 by (simp add: map_add_disj_domf)
          have h9: "(tgt SG1 ++ tgt SG2) x = (tgt SG1) x" 
            using h7b h5 by (simp add: map_add_disj_domf)
          have h10: "x \<in> EsId (SG1)"
            using h6 h7 h4 h5 h8 h9 by (auto simp add: cupSG_def EsId_def)
          show "x \<in> EsId SG1 \<union> EsId SG2"
          using h10 by (simp)
        next
          assume h7: "x \<notin> Es SG1"
          have h7a: "x \<in> Es SG2"
            using h1a h7 h6b by (simp)
          have h7b: "x \<in> dom (src SG2)"
            using h7a h4 h3a by (simp add: ftotal_on_dom)
          have h7c: "x \<in> dom (tgt SG2)"
            using h7a h4 h3b by (simp add: ftotal_on_dom)
          have h8: "(src SG1 ++ src SG2) x = (src SG2) x" 
            using h7b h4 by (simp add: map_add_dom_app_simps)
          have h9: "(tgt SG1 ++ tgt SG2) x = (tgt SG2) x" 
            using h7c h5 by (simp add: map_add_dom_app_simps)
          have h10: "x \<in> EsId (SG2)"
            using h6 h7 h4 h5 h8 h9 by (auto simp add: cupSG_def EsId_def)
          show "x \<in> EsId SG1 \<union> EsId SG2"
          using h10 by (simp)
        qed
      qed
    next 
    show "EsId SG1 \<union> EsId SG2 \<subseteq> EsId (SG1 USG SG2)"
    proof
      fix x
      assume h6: "x \<in> EsId SG1 \<union> EsId SG2"
      have h6a: "x \<in> EsId SG1 \<or> x \<in> EsId SG2"
        using h6 by simp
      have h6b: "x \<in> Es SG1 \<or> x \<in> Es SG2"
        using h6 by (auto simp add: EsId_def)
      show "x \<in> EsId (SG1 USG SG2)"
      proof (case_tac "x \<in> Es SG1")
        assume h7: "x \<in> Es SG1"
        have h7a: "x \<in> dom (src SG1)"
          using h7 h4 h2a by (simp add: ftotal_on_dom)
        have h7b: "(src SG1 ++ src SG2) x = (src SG1) x"
          using h7a h4 by (simp add: map_add_disj_domf)
        have h7c: "x \<in> dom (tgt SG1)"
          using h7 h5 h2b by (simp add: ftotal_on_dom)
        have h7d: "(tgt SG1 ++ tgt SG2) x = (tgt SG1) x"
          using h7c h5 by (simp add: map_add_disj_domf)
        show "x \<in> EsId (SG1 USG SG2)"
        using h1a h7 h7b h7d h6 by (auto simp add: cupSG_def EsId_def)
      next
        assume h7: "x \<notin> Es SG1"
        have h8: "x \<in> Es SG2"
          using h1a h7 h6b by (simp)
        have h8a: "x \<in> dom (src SG2)"
          using h8 h4 h3a by (simp add: ftotal_on_dom)
        have h8b: "(src SG1 ++ src SG2) x = (src SG2) x"
          using h8a h4 by (simp add: map_add_dom_app_simps)
        have h8c: "x \<in> dom (tgt SG2)"
          using h8 h5 h3b by (simp add: ftotal_on_dom)
        have h8d: "(tgt SG1 ++ tgt SG2) x = (tgt SG2) x"
          using h8c h5 by (simp add: map_add_dom_app_simps)
        show "x \<in> EsId (SG1 USG SG2)"
        using h1a h8 h8b h8d h6 by (auto simp add: cupSG_def EsId_def)
      qed
    qed
  qed
qed

lemma restrict_cup_wf_1: 
  assumes h1: "is_wf_sg SG1" and h2: "is_wf_sg SG2" and h3: "disjGs SG1 SG2"
  shows "restrict SG1 (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2)) = restrict SG1 (EsI SG1 - EsId SG1)"
  proof -
    from h1 have h1a : "dom (src SG1) = Es SG1" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1b : "dom (tgt SG1) = Es SG1"
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2a : "dom (src SG2) = Es SG2" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2b : "dom (tgt SG2) = Es SG2" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h3 have h3a: "Es SG1 \<inter> Es SG2 = {}" by (simp add: disjGs_def disjEsGs_def)
    have h4: "src SG1 |` (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2)) 
      = src SG1 |` (EsI SG1 - EsId SG1)"
    proof
      fix x
      show "(src SG1 |` (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2))) x =
        (src SG1 |` (EsI SG1 - EsId SG1)) x"
      proof (case_tac "x \<in> Es SG1")
        assume "x \<in> Es SG1"
        then show "(src SG1 |` (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2))) x =
          (src SG1 |` (EsI SG1 - EsId SG1)) x"
          using h1a h1b h2a h2b h3a h1 h2 
          by (auto simp add: restrict_map_def EsId_def split: if_splits 
            intro: in_EsI_in_Es domI)
      next
        assume "x \<notin> Es SG1"
        then show "(src SG1 |` (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2))) x =
          (src SG1 |` (EsI SG1 - EsId SG1)) x"
          using h1a h1b h2a h2b h3a h1 h2 
          by (auto simp add: restrict_map_def EsId_def split: if_splits intro: in_EsI_in_Es domI)
      qed
    qed
    have h5: "tgt SG1 |` (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2)) = tgt SG1 |` (EsI SG1 - EsId SG1)"
    proof
      fix x
      show "(tgt SG1 |` (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2))) x = (tgt SG1 |` (EsI SG1 - EsId SG1)) x"
      proof (case_tac "x \<in> Es SG1")
        assume "x \<in> Es SG1"
        then show "(tgt SG1 |` (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2))) x =
          (tgt SG1 |` (EsI SG1 - EsId SG1)) x"
          using h1a h1b h2a h2b h3a h1 h2 
          by (auto simp add: restrict_map_def EsId_def split: if_splits 
            intro: in_EsI_in_Es domI)
        next
          assume "x \<notin> Es SG1"
          then show "(tgt SG1 |` (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2))) x =
            (tgt SG1 |` (EsI SG1 - EsId SG1)) x"
          using h1a h1b h2a h2b h3a h1 h2 
            by (auto simp add: restrict_map_def EsId_def split: if_splits 
              intro: in_EsI_in_Es domI)
        qed
      qed
    show ?thesis
    proof (simp add: restrict_def, rule conjI)
      show "rst_Ns SG1 (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2)) = rst_Ns SG1 (EsI SG1 - EsId SG1)"
      using h4 h5 by (simp add: rst_Ns_def)
    next
      apply_end(rule conjI)
      show "Es SG1 \<inter> (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2)) = Es SG1 \<inter> (EsI SG1 - EsId SG1)"
      proof (rule ccontr)
        assume h5: "\<not>(Es SG1 \<inter> (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2)) = Es SG1 \<inter> (EsI SG1 - EsId SG1))"
        from h1a h5 show "False"
          using h2 h3a by (auto simp add: in_EsI_in_Es EsId_in_EsG)
      qed
      next
      apply_end (rule conjI)
       from h1a h2b h2 h3a 
       show "rst_fun (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2)) (src SG1) = rst_fun (EsI SG1 - EsId SG1) (src SG1)"
        by (auto simp add: rst_fun_eq in_EsI_in_Es EsId_in_EsG)
      next
      from h1a h1b h2 h3a 
      show "rst_fun (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2)) (tgt SG1) = rst_fun (EsI SG1 - EsId SG1) (tgt SG1)"
        by (auto simp add: rst_fun_eq in_EsI_in_Es EsId_in_EsG)
    qed
  qed

lemma restrict_cup_wf_2: 
  assumes h1: "is_wf_sg SG1" and h2: "is_wf_sg SG2" and h3: "disjGs SG1 SG2"
  shows "restrict SG2 (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2)) = restrict SG2 (EsI SG2 - EsId SG2)"
  proof -
    from h1 have h1a: "dom (src SG1) = Es SG1" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h1 have h1b: "dom (tgt SG1) = Es SG1" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2a: "dom (src SG2) = Es SG2" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h2 have h2b: "dom (tgt SG2) = Es SG2" 
      by (simp add: is_wf_sg_def is_wf_g_def ftotal_on_def)
    from h3 have h3a: "Es SG1 \<inter> Es SG2 = {}" 
      by (simp add: disjGs_def disjEsGs_def)
    have h4: "src SG2 |` (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2)) 
      = src SG2 |` (EsI SG2 - EsId SG2)"
    proof
      fix x
      show "(src SG2 |` (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2))) x =
        (src SG2 |` (EsI SG2 - EsId SG2)) x"
      proof (case_tac "x \<in> Es SG2")
        assume "x \<in> Es SG2"
        then show "(src SG2 |` (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2))) x =
          (src SG2 |` (EsI SG2 - EsId SG2)) x"
          using h1a h1b h2a h2b h3a h1 h2 
          by (auto simp add: restrict_map_def split: if_splits 
            intro: in_EsI_in_Es domI EsId_in_EsG)
      next
        assume "x \<notin> Es SG2"
        then show "(src SG2 |` (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2))) x =
          (src SG2 |` (EsI SG2 - EsId SG2)) x"
          using h1a h1b h2a h2b h3a h1 h2 
          by (auto simp add: restrict_map_def split: if_splits intro: in_EsI_in_Es domI)
      qed
    qed
    have h5: "tgt SG2 |` (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2)) = tgt SG2 |` (EsI SG2 - EsId SG2)"
    proof
      fix x
      show "(tgt SG2 |` (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2))) x = (tgt SG2 |` (EsI SG2 - EsId SG2)) x"
      proof (case_tac "x \<in> Es SG2")
        assume "x \<in> Es SG2"
        then show "(tgt SG2 |` (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2))) x =
          (tgt SG2 |` (EsI SG2 - EsId SG2)) x"
          using h1a h1b h2a h2b h3a h1 h2 
          by (auto simp add: restrict_map_def EsId_def split: if_splits 
            intro: in_EsI_in_Es domI)
        next
          assume "x \<notin> Es SG2"
          then show "(tgt SG2 |` (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2))) x =
            (tgt SG2 |` (EsI SG2 - EsId SG2)) x"
          using h1a h1b h2a h2b h3a h1 h2 
            by (auto simp add: restrict_map_def EsId_def split: if_splits 
              intro: in_EsI_in_Es domI)
        qed
      qed
    show ?thesis
    proof (simp add: restrict_def, rule conjI)
      show "rst_Ns SG2 (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2)) = rst_Ns SG2 (EsI SG2 - EsId SG2)"
        using h4 h5 by (simp add: rst_Ns_def)
    next
      apply_end(rule conjI)
      show "Es SG2 \<inter> (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2)) = Es SG2 \<inter> (EsI SG2 - EsId SG2)"
      proof (rule ccontr)
        assume h6: "\<not>Es SG2 \<inter> (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2)) = Es SG2 \<inter> (EsI SG2 - EsId SG2)"
        from h2a h6 show "False"
          using h1 h2 h3a by (auto intro: in_EsI_in_Es EsId_in_EsG)
      qed
    next
    apply_end (rule conjI)
    from h3a h2a h1 h2
    show "rst_fun (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2)) (src SG2) = rst_fun (EsI SG2 - EsId SG2) (src SG2)"
      by (auto simp add: rst_fun_eq intro: in_EsI_in_Es EsId_in_EsG)    
    next
      from h3a h2b h1 h2
      show "rst_fun (EsI SG1 \<union> EsI SG2 - (EsId SG1 \<union> EsId SG2)) (tgt SG2) = rst_fun (EsI SG2 - EsId SG2) (tgt SG2)"
        by (auto simp add: rst_fun_eq intro: in_EsI_in_Es EsId_in_EsG)      
    qed
  qed

lemma disjGs_inhG:
  assumes h1: "is_wf_sg SG1" and h2: "is_wf_sg SG2" and h3: "disjGs SG1 SG2"
  shows "disjGs (inhG SG1) (inhG SG2)"
  proof -
    from h1 have h1a: "is_wf_g SG1" 
      by (simp add: is_wf_sg_def)
    from h2 have h2a: "is_wf_g SG2" 
      by (simp add: is_wf_sg_def)
    from h3 have h3b: "Es SG1 \<inter> Es SG2 = {}"
      by (simp add: disjGs_def)
    show ?thesis
    proof (simp add: disjGs_def, rule conjI)
      show "rst_Ns SG1 (EsI SG1 - EsId SG1) \<inter> rst_Ns SG2 (EsI SG2 - EsId SG2) = {}"
        using h1a h2a h3 by (simp add: rst_Ns_disj)
    next
      apply_end(rule conjI)
      have h: "Ns SG1 \<inter> (Es SG1 \<inter> (EsI SG1 - EsId SG1)) = {}"
        using disj_V_E h1a
        by (auto simp add: is_wf_g_def)
      show "rst_Ns SG1 (EsI SG1 - EsId SG1) \<inter> (Es SG1 \<inter> (EsI SG1 - EsId SG1)) = {}"
        using h h1a rst_Ns_sub[of SG1 "(EsI SG1 - EsId SG1)"] 
        by (auto)
    next
      apply_end(rule conjI)
      have h: "Ns SG1 \<inter> (EsI SG1 - EsId SG1) \<inter> (Es SG2 \<inter> (EsI SG2 - EsId SG2)) = {}"
        using disj_V_E h1a h2a h3b
        by (auto simp add: is_wf_g_def intro: in_EsI_in_Es)
      show "rst_Ns SG1 (EsI SG1 - EsId SG1) \<inter> (Es SG2 \<inter> (EsI SG2 - EsId SG2)) = {}"
        using h h1a h3 rst_Ns_sub[of SG1 "(EsI SG1 - EsId SG1)"] 
        by (auto simp add: disjGs_def)
    next
      apply_end(rule conjI)
      have h: "Ns SG2 \<inter> (EsI SG2 - EsId SG2) \<inter> (Es SG1 \<inter> (EsI SG1 - EsId SG1)) = {}"
        using disj_V_E h1a h2a h3b
        by (auto simp add: is_wf_g_def intro: in_EsI_in_Es)
      show "rst_Ns SG2 (EsI SG2 - EsId SG2) \<inter> (Es SG1 \<inter> (EsI SG1 - EsId SG1)) = {}"
        using h h2a h3 rst_Ns_sub[of SG2 "(EsI SG2 - EsId SG2)"] 
        by (auto simp add: disjGs_def)
    next
      apply_end(rule conjI)
      have h: "Ns SG2 \<inter> (Es SG2 \<inter> (EsI SG2 - EsId SG2)) = {}"
        using disj_V_E h1a h2a h3b
        by (auto simp add: is_wf_g_def intro: in_EsI_in_Es)
      show "rst_Ns SG2 (EsI SG2 - EsId SG2) \<inter> (Es SG2 \<inter> (EsI SG2 - EsId SG2)) = {}"
        using h h2a h3 rst_Ns_sub[of SG2 "(EsI SG2 - EsId SG2)"] 
        by (auto simp add: disjGs_def)
    next
      from h3b show "Es SG1 \<inter> (EsI SG1 - EsId SG1) \<inter> (Es SG2 \<inter> (EsI SG2 - EsId SG2)) = {}"
        by auto
    qed
  qed

lemma inh_disj_SGs_disj_fields: 
  assumes h1: "is_wf_sg SG1" and h2: "is_wf_sg SG2" and h3: "disjGs SG1 SG2"
  shows "Field (inh SG1) \<inter> Field (inh SG2) = {}"
  proof -
    from h1 have h1a: "is_wf_g SG1" 
      by (simp add: is_wf_sg_def)
    from h1a have h1b: "is_wf_g (inhG SG1)" 
      by (simp add: is_wf_g_inhG)
    from h2 have h2a: "is_wf_g SG2" 
      by (simp add: is_wf_sg_def)
    from h2a have h2b: "is_wf_g (inhG SG2)" 
      by (simp add: is_wf_g_inhG)
      from h1 h2 h3 h1b h2b show ?thesis
        using disjGs_inhG[of SG1 SG2]
        by (simp add: inh_def relOfGr_disj_Gs)
  qed

lemma inhG_Un_dist:
  assumes h1: "is_wf_sg SG1" and h2: "is_wf_sg SG2" and h3: "disjGs SG1 SG2"
  shows "inhG (SG1 USG SG2) = inhG (SG1) UG  inhG (SG2)"
  proof -
    from h3 have h3a: "disjEsGs SG1 SG2"
      by (simp add: disjGs_def disjEsGs_def)
    have h4: "restrict SG1 (EsI SG1 - EsId SG1) = inhG SG1"
      by (auto simp add: inhG_def)
    have h5: "restrict SG2 (EsI SG2 - EsId SG2) = inhG SG2"
      by (auto simp add: inhG_def)
    from assms h3a show ?thesis 
      by (simp add: inhG_def restrict_dist_sgcup EsI_disj_dist EsId_disj_dist
        restrict_cup_wf_1 restrict_cup_wf_2)
  qed

lemma inhsg_Un_dist:
  assumes h1: "is_wf_sg SG1" and h2: "is_wf_sg SG2" and h3: "disjGs SG1 SG2"
  shows "inh (SG1 USG SG2) = inh (SG1) \<union>  inh (SG2)"
  proof -
    from h1 have h1a: "is_wf_g (inhG SG1)" 
      by (simp add: is_wf_g_inhG is_wf_sg_def)
    from h2 have h2a: "is_wf_g (inhG SG2)" 
      by (simp add: is_wf_g_inhG is_wf_sg_def)
    from h3 have h3a: "disjEsGs SG1 SG2" by (simp add: disjGs_def disjEsGs_def)
    have h4: "restrict SG1 (EsI SG1 - EsId SG1) = inhG SG1"
      by (auto simp add: inhG_def)
    have h5: "restrict SG2 (EsI SG2 - EsId SG2) = inhG SG2"
      by (auto simp add: inhG_def)
    have h6: "disjEsGs (inhG SG1)(inhG SG2)"
      using assms disjGs_inhG[of SG1 SG2] by (simp add: disjGs_def disjEsGs_def)
    from assms h3a h1a h2a h6 show ?thesis
      by (simp add: inh_def restrict_dist_sgcup inhG_def EsI_disj_dist EsId_disj_dist 
        restrict_cup_wf_1 restrict_cup_wf_2, (subst h4)+, (subst h5)+)
        (simp add: relOfGr_UG)
  qed

lemma acyclic_SGr_Un_dist: 
  assumes h1: "is_wf_sg SG1" and h2: "is_wf_sg SG2" and h3: "disjGs SG1 SG2"
  shows "acyclicGr (inhG (SG1 USG SG2)) = (acyclicGr (inhG SG1) \<and> acyclicGr (inhG SG2))"
  proof -
    from h1 have h1a: "is_wf_g (inhG SG1)" 
      by (simp add: is_wf_g_inhG is_wf_sg_def)
    from h2 have h2a: "is_wf_g (inhG SG2)" 
      by (simp add: is_wf_g_inhG is_wf_sg_def)
    from h3 have h3a: "disjEsGs SG1 SG2" by (simp add: disjGs_def disjEsGs_def)
    have h4: "disjGs (inhG SG1)(inhG SG2)"
      using assms disjGs_inhG[of SG1 SG2] by (simp add: disjGs_def)
    from assms h1a h2a h3a h4 show ?thesis
      by (simp add: inhG_Un_dist acyclic_Gr_dist_disj)
  qed
  
(*lemma acyclic_sg_dist:
  assumes h1: "is_wf_sg SG1" and h2: "is_wf_sg SG2" and h3: "disjGs SG1 SG2"
  shows "acyclicGr (SG1 USG SG2) \<longleftrightarrow> acyclicGr SG1 \<and> acyclicGr SG2"
  proof -
    from h1 h2 h3 have h3a: "Field (inh SG1) \<inter> Field (inh SG2) = {}"
      by (simp add: inh_disj_SGs_disj_fields)
    from assms h3a show ?thesis
      by (simp add: acyclic_Gr_dist_disj inhsg_Un_dist acyclic_disj_dist)
  qed*)

lemma is_wf_sg_Un: 
  assumes h1: "is_wf_sg SG1" and h2: "is_wf_sg SG2" and h3: "disjGs SG1 SG2"
  shows "is_wf_sg (SG1 USG SG2)"
  proof -
    from h1 have h1a: "is_wf_g SG1" by (simp add: is_wf_sg_def)
    have h1d: "dom (srcm SG1) = EsTy SG1 {Some erelbi, Some ecompbi}"
      using h1 by (simp add: is_wf_sg_def)
    have h1e: "dom (tgtm SG1) = EsTy (SG1) {Some erelbi, Some ereluni, Some ecompbi, 
    Some ecompuni}"
      using h1 by (simp add: is_wf_sg_def)
    from h1 have h1f: "EsR (SG1) \<subseteq> EsId (SG1)" by (simp add: is_wf_sg_def)
    from h1 have h1g: "acyclicGr (inhG SG1)" by (simp add: is_wf_sg_def)
    from h2 have h2a: "is_wf_g SG2" by (simp add: is_wf_sg_def)
    from h2 have h2d: "dom (srcm SG2) = EsTy SG2 {Some erelbi, Some ecompbi}" 
      by (simp add: is_wf_sg_def)
    from h2 have h2e: "dom (tgtm SG2) = 
      EsTy (SG2) {Some erelbi, Some ereluni, Some ecompbi, Some ecompuni}" 
      by (simp add: is_wf_sg_def)
    from h2 have h2f: "EsR (SG2) \<subseteq> EsId (SG2)" by (simp add: is_wf_sg_def)
    from h2 have h2g: "acyclicGr (inhG SG2)" by (simp add: is_wf_sg_def)
    from h3 have h3a: "Es SG1 \<inter> Es SG2 = {}" by (simp add: disjGs_def disjEsGs_def)
    from h3 have h3b: "Ns SG1 \<inter> Ns SG2 = {}" by (simp add: disjGs_def)
    have h4: "dom (ety SG1) \<inter> dom (ety SG2) = {}" 
        using h1 h2 h3a by (simp add: is_wf_sg_def ftotal_on_def)
    show ?thesis
    proof (simp add: is_wf_sg_def, rule conjI)
      show "is_wf_g (SG1 USG SG2)"
        using h1a h2a h3 by (simp add: is_wf_g_Un2)
    next
      apply_end(rule conjI)
      show "ftotal_on (nty (SG1 USG SG2)) (Ns (SG1 USG SG2)) SGNTy_set"
        using h1 h2 h3b by (auto simp add: cupSG_def is_wf_sg_def ftotal_on_def)
    next
      apply_end(rule conjI)
      show "ftotal_on (ety (SG1 USG SG2)) (Es (SG1 USG SG2)) SGETy_set"
        using h1 h2 h3a by (auto simp add: cupSG_def ftotal_on_def is_wf_sg_def)
    next
      apply_end(rule conjI)
      have ha: "None \<notin> {Some erelbi, Some ecompbi}" by (simp)
      show "dom (srcm SG2) \<union> dom (srcm SG1) = EsTy (SG1 USG SG2) {Some erelbi, Some ecompbi}"
        using h1d h2d h3a ha h4 by (auto simp add: cupSG_def EsTy_def map_add_dists_vimage)
    next
      apply_end(rule conjI)
      have ha: "None \<notin> {Some erelbi, Some ereluni, Some ecompbi, Some ecompuni}" by (simp)
      from h1e h2e h3a ha h4
      show "dom (tgtm (SG1 USG SG2)) = 
        EsTy (SG1 USG SG2) {Some erelbi, Some ereluni, Some ecompbi, Some ecompuni}"
        by (auto simp add: cupSG_def EsTy_def map_add_dists_vimage)
    next
      apply_end(rule conjI)
       have h6: "None \<notin> {Some eref}" by (simp)
       show "EsR (SG1 USG SG2) \<subseteq> EsId (SG1 USG SG2)"
        using h1 h2 h3 h1f h2f by (auto simp add: EsR_disj_dist EsId_disj_dist)
    next 
      apply_end(rule conjI)
      from h3a have ha: "dom (srcm SG1) \<inter> dom (srcm SG2) = {}"
        using h1 h2 by (auto simp add: is_wf_sg_def EsTy_def vimage_def 
          ftotal_on_def intro!: domI)
      have hb: "EsTy SG1 {Some ecompbi} \<subseteq> dom (srcm SG1)"
        using h1 by (auto simp add: EsTy_def vimage_def is_wf_sg_def)
      have hc: "EsTy SG2 {Some ecompbi} \<subseteq> dom (srcm SG2)"
        using h2 by (auto simp add: EsTy_def vimage_def is_wf_sg_def)
      show "srcm SG1 ++ srcm SG2 ` EsTy (SG1 USG SG2) {Some ecompbi}
          \<subseteq> {Some (rm 0 (val (Suc 0))), Some (sm (val (Suc 0)))}"
          using h1 h2 h3 ha hb hc 
          by (simp add: EsTy_USG image_Un map_add_image_dist map_add_image_dist2 is_wf_sg_def)
    next
        from h1 h2 h3 h1g h2g show "acyclicGr (inhG (SG1 USG SG2))"
          by (simp add: acyclic_SGr_Un_dist)
    qed
  qed
        
definition morphSGr :: "SGr \<Rightarrow> SGr \<Rightarrow> Morph set"
where
  "morphSGr SG1 SG2 \<equiv> {r. is_wf_sg SG1 \<and> is_wf_sg SG2
      \<and> ftotal_on (fV r) (Ns SG1) (Ns SG2) 
      \<and> ftotal_on (fE r) (Es SG1) (Es SG2)  
      \<and> srcst SG1 O pfunToRel(fV r)  \<subseteq> pfunToRel(fE r) O srcst SG2  
      \<and> tgtst SG1 O pfunToRel(fV r) \<subseteq> pfunToRel(fE r) O tgtst SG2  
      \<and> inhst SG1 O pfunToRel (fV r) \<subseteq> pfunToRel (fV r) O inhst SG2}"

definition morphGr2SGr :: "Gr \<Rightarrow> SGr \<Rightarrow> Morph set"
where
  "morphGr2SGr G1 SG2 \<equiv> {r. is_wf_g G1 \<and> is_wf_sg SG2
      \<and> ftotal_on (fV r) (Ns G1) (Ns SG2) 
      \<and> ftotal_on (fE r) (Es G1) (Es SG2)  
      \<and> pfunToRel((fV r) \<circ>\<^sub>m (src G1)) \<subseteq> pfunToRel(fE r) O srcst SG2  
      \<and> pfunToRel((fV r) \<circ>\<^sub>m (tgt G1)) \<subseteq> pfunToRel(fE r) O tgtst SG2}"

end
