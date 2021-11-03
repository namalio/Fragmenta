(*  Title:       Fragmenta theory of Models (Mdls)
    Description: The 'Fragmenta' theory presented in the Models 2015 paper.
    Author:      Nuno Amálio
*)
theory Fragmenta_MdlsL
imports Fragmenta_FrsL Fragmenta_Mdls

begin

(*List version of Models*)      
record Mdl_ls = 
  gfgL :: "GFGr_ls"
  frdL :: "(V \<times> Fr_ls) list"

definition toMdl:: "Mdl_ls \<Rightarrow> Mdl"
where
  "toMdl ML \<equiv> \<lparr>gfg = gfgL ML, 
    frd = map_of (zip (map fst (frdL ML)) (map (toFr o snd) (frdL ML))) \<rparr>"

definition is_wf_mdl_ls :: "Mdl_ls \<Rightarrow> bool"
where
  "is_wf_mdl_ls ML \<equiv> NsG (gfgL ML) = (map fst (frdL ML))
    \<and> distinct (map fst (frdL ML))
    \<and> is_wf_mdl (toMdl ML)"

fun getSelfEf :: "V \<Rightarrow> Mdl \<Rightarrow> E"
where
  "getSelfEf vf M = hd (filter 
    (\<lambda> e. src (toGFGr (gfg M)) e = Some vf \<and> tgt (toGFGr (gfg M)) e = Some vf)
    (EsG (gfg M)))"

fun getFrLOfV :: "V \<Rightarrow> Mdl_ls \<Rightarrow> Fr_ls"
where
  "getFrLOfV vf ML = (snd \<circ> the) ((List.find (\<lambda>p. fst p = vf)(frdL ML)))" 

(*Builds a morphism from a fragment to the GFG, given a GFG node*)
definition calcF2GFGL :: "V \<Rightarrow> Mdl_ls \<Rightarrow> MorphL"
where
  "calcF2GFGL vf ML \<equiv> (let FL = getFrLOfV vf ML in
    (if frd (toMdl ML) vf \<noteq> None then 
      \<lparr>fVL = (List.product (NsG (sg_ls FL)) [vf]), 
        fEL = 
        (List.product (filter (\<lambda> e. ety (sg (toFr FL)) e \<noteq> Some eref) 
          (EsG (sg_ls FL))) [getSelfEf vf (toMdl ML)])\<rparr>
      else \<lparr>fVL = [], fEL = []\<rparr>))"

(* Calculates all required morphisms for a given list of nodes*)
primrec calcMFs2GFG:: "Mdl_ls \<Rightarrow> V list \<Rightarrow> MorphL"
where
  "calcMFs2GFG ML [] = emptyGML " |
  "calcMFs2GFG ML (vf#vs) = consUGM (calcF2GFGL vf ML) (calcMFs2GFG ML vs)"

lemma "consF2GFG vf (toMdl ML) = toMorph (calcF2GFGL vf ML)"
  proof -
    have "\<exists> m . vf \<in> Ns (toGFGr (gfg (toMdl ML))) \<and>
        (\<exists>F. frd (toMdl ML) vf = Some F \<and>
             (\<exists>ef. src (toGFGr (gfg (toMdl ML))) ef = Some vf \<and>
                   tgt (toGFGr (gfg (toMdl ML))) ef = Some vf \<and>
                   fE m =
                   (\<lambda>e. if e \<in> Es (sg F) \<and> e \<notin> EsR (sg F) then Some ef
                        else None) \<and>
                   fV m = (\<lambda>v. if v \<in> Ns (sg F) then Some vf else None) \<and>
                   m \<in> morphF2GFGr F (toGFGr (gfg (toMdl ML)))))"
      by (simp)
    then show ?thesis
    by (simp add: consF2GFG_def)
  qed


lemma consMFs2GFG_eq_calc: "consMFs2GFG (toMdl ML) vfs = toMorph(calcMFs2GFG ML vfs)"
  proof (induct vfs)
    show "consMFs2GFG (toMdl ML) [] = toMorph (calcMFs2GFG ML [])"
      by (simp add: toMdl_def toMorph_def emptyGML_def emptyGM_def)
  next
    fix a vfs
    assume h1: "consMFs2GFG (toMdl ML) vfs = toMorph (calcMFs2GFG ML vfs)"
    have h2: "consMFs2GFG (toMdl ML) (a # vfs) = consF2GFG a (toMdl ML) UGM consMFs2GFG (toMdl ML) vfs"
      by (simp)
    have h3: "toMorph (calcMFs2GFG ML (a # vfs)) = toMorph(consUGM (calcF2GFGL a ML) (calcMFs2GFG ML vfs))"
      by (simp)
    from h1 show "consMFs2GFG (toMdl ML) (a # vfs) = toMorph (calcMFs2GFG ML (a # vfs))"
      by (simp only: h2 h3 UGM_eq_ConsUGM[THEN sym])
  qed

(*Calculates the union of a model's fragments*)
definition consUMdlFs:: "Mdl_ls \<Rightarrow>Fr_ls"
where
  "consUMdlFs ML \<equiv> consUFs (map snd (frdL ML))"

lemma Ns_ToFr_eq_NsG: "Ns (sg (toFr FL)) = set (NsG (sg_ls FL))"
  by (auto simp add: toFr_def toSGr_def)

lemma map_the_fdr_toMdl:
  assumes h1: "ML = \<lparr>gfgL = GL, frdL = IFL\<rparr>" 
    and h2: "NsG (gfgL ML) = (map fst (frdL ML))" and h3: "distinct (map fst (frdL ML))"
  shows "map (the \<circ> frd (toMdl ML)) (NsG (gfg (toMdl ML))) = map (toFr \<circ> snd) (frdL ML)"
  proof -
    from h1 have h4: "frdL ML = IFL" by simp
    from h1 h2 have h5: "NsG (gfg (toMdl ML)) = (map fst IFL)" 
      by (simp add: toMdl_def is_wf_mdl_ls_def)
    from h1 h3 have h6: "distinct (map fst IFL)" by (simp)
    show ?thesis
    proof (simp only: h4 h5, cases IFL)
      assume "IFL = []"
      then show "map (the \<circ> frd (toMdl ML)) (map fst IFL) = map (toFr \<circ> snd) IFL"
        by (simp)
    next
      fix a list
      assume h7: "IFL = a # list"
      then have h8: "fst a \<notin> fst ` set list" using h4 h6 by simp
      have "(\<And>x. x \<in> set (a # list) \<Longrightarrow> (the \<circ> frd (toMdl ML) \<circ> fst) x = (toFr \<circ> snd) x)"
      proof (simp, case_tac "x = a", simp)
        fix x
        assume "x = a"
        then show "the (frd (toMdl ML) (fst a)) = toFr (snd a)"
          using h7 h5 by (simp add: h1 h6 toMdl_def image_def)
      next
        apply_end(simp)
        fix x 
        assume h8a: "x \<noteq> a"
          and h8b: "x \<in> set list"
        then show "the (frd (toMdl ML) (fst x)) = toFr (snd x)"
        using h8
        proof (auto simp add: h1 h7 toMdl_def image_def map_of_zip_eq the_pos_map)
          from h8a h6 h7 have h9: "distinct (map fst list)"
            by simp
          from h8b have "fst x \<in> set (map fst list)"
            by auto
          then have "pos0 (map fst list) (fst x) < length (map fst list)"
            by (simp only: pos0_of_in_lt_length)
          then show "the (nth_opt (map (toFr \<circ> snd) list) (pos0 (map fst list) (fst x))) = toFr (snd x)"
            using the_nth_opt_in[where n="pos0 (map fst list) (fst x)"
              and l = "map (toFr \<circ> snd) list"]
            using h9 h8b by (simp add: nth_pos_map_fst)
        qed
      qed
      then show "map (the \<circ> frd (toMdl ML)) (map fst IFL) = map (toFr \<circ> snd) IFL"
        using h7 by simp
    qed
  qed

lemma UMdlFs_eq_UFs:
  assumes h1: "ML = \<lparr>gfgL = GL, frdL = IFL\<rparr>" 
    and h2: "NsG (gfgL ML) = (map fst (frdL ML))" 
    and h3: "distinct (map fst (frdL ML))"
  shows "UMdlFs (toMdl ML) = UFs (map (toFr \<circ> snd) (frdL ML))"
  proof -
    from assms show ?thesis
    by (simp only: UMdlFs_def map_the_fdr_toMdl)
  qed
          
lemma UMdlFs_Eq_consUMdlFs:
  assumes h1: "ML = \<lparr>gfgL = GL, frdL = IFL\<rparr>" 
    and h2: "NsG (gfgL ML) = (map fst (frdL ML))" 
    and h3: "distinct (map fst (frdL ML))"
  shows "UMdlFs (toMdl ML) = toFr (consUMdlFs ML)"
  proof -
    have "UMdlFs (toMdl ML) = UFs (map toFr (map snd (frdL ML)))"
      using assms by (auto simp add: UMdlFs_eq_UFs)
    then show ?thesis
    by (simp only: consUMdlFs_def UFsEqConsUFs)
  qed

end