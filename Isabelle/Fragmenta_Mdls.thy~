(*  Title:       Fragmenta theory of Models (Mdls)
    Description: The 'Fragmenta' theory presented in the Models 2015 paper.
    Author:      Nuno Amálio
*)
theory Fragmenta_Mdls
imports Fragmenta_GFGs Fragmenta_Frs Fragmenta_GraphsL

begin

(*Models with GFGs as lists*)      
record Mdl = 
  gfg :: "GFGr_ls"
  frd :: "V \<rightharpoonup> Fr"

(*Predicate to check that all fragments of a Model are disjoint*)
definition disjMdlFrs:: "Mdl \<Rightarrow> bool"
where
  "disjMdlFrs M \<equiv> disjFs (map (the o frd M) (NsG (gfg M)))"

(*Predicate that gets the union of fragments of a model*)
definition UMdlFs:: "Mdl \<Rightarrow> Fr"
where
  "UMdlFs M \<equiv> UFs (map (the o frd M) (NsG (gfg M)))"

(*Builds a morphism from a fragment to the GFG, given a GFG node*)
definition consF2GFG:: "V \<Rightarrow> Mdl \<Rightarrow> Morph"
where
  "consF2GFG vf M \<equiv> 
    SOME m.  
      vf \<in> Ns (toGFGr (gfg M)) 
      \<and> (\<exists> F ef. frd M vf = Some F 
        \<and> src (toGFGr (gfg M)) ef = Some vf 
        \<and> tgt (toGFGr (gfg M)) ef = Some vf
        \<and> fE m = (\<lambda> e. if e \<in> Es (sg F)- EsR(sg F) then Some ef else None)
        \<and> fV m = (\<lambda> v. if v \<in> Ns (sg F) then Some vf else None)
        \<and> m \<in> (morphF2GFGr F (toGFGr (gfg M))))"

(*Builds the morphism given a list of nodes*)
primrec consMFs2GFG:: "Mdl \<Rightarrow> V list \<Rightarrow> Morph"
where
  "consMFs2GFG M [] = emptyGM"
  | "consMFs2GFG M (vf#vfs) = consF2GFG vf M UGM consMFs2GFG M vfs"

(*Constructs morphism from the model fragments to the GFG*)
definition mUM2GFG:: "Mdl \<Rightarrow> Morph"
where
  "mUM2GFG M \<equiv> consMFs2GFG M (NsG (gfg M))"

(*Well-formedness for models*)
definition is_wf_mdl :: "Mdl \<Rightarrow> bool"
where
  "is_wf_mdl M \<equiv> (\<forall> F. F \<in> ran (frd M) \<longrightarrow> is_wf_fr F) 
    \<and> is_wf_gfg_ls (gfg M)
    \<and> ftotal_on (frd M) (set (NsG (gfg M))) fr_set
    \<and> disjMdlFrs M \<and> mUM2GFG M \<in> (morphF2GFGr (UMdlFs M) (toGFGr (gfg M)))" 

(*Can't I show that it is always the case that : mUM2GFG is a morphism?*)


(*lemma 
  assumes h1: "ML = \<lparr>gfgL = GL, frdL = IFL\<rparr>" and h2: "M' = toMdl (ML)" and h3: "L = NsG GL"
    and h4: "is_wf_mdl (toMdl ML)"
  shows "map (the o frd M') L = map toFr (map snd (frdL ML))"
  proof (cases L)
    assume h5: "L = []"
    then have "IFL = []"
      using h1 h2 h3 h4
      by (simp add: is_wf_mdl_def ftotal_on_def toMdl_def)
    then show "map (the \<circ> frd M') L = map toFr (map snd (frdL ML))"
      using h1 h3 h5 by (simp add: toFr_def toMdl_def)
  next
    fix a list
    assume h6: "L = a # list"
    then have "IFL \<noteq> []"
      using h1 h2 h3 h4
      by (auto simp add: is_wf_mdl_def ftotal_on_def toMdl_def)
    then show "map (the \<circ> frd M') L = map toFr (map snd (frdL ML))"
    proof (simp add: h1, cases IFL, simp)
      fix a' list'
      assume h7: "IFL = a' # list'"
      then show "map (the \<circ> frd M') L = map (toFr \<circ> snd) IFL"
      by (simp add: h2)
        apply_end(rule conjI)
        show "the (frd (toMdl ML) a) = toFr (snd a')"
          using h1 by (auto simp add: toFr_def toMdl_def Fr_eq)*)

  
end