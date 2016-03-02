(*  Title:       Fragmenta theory of Typed Models (Mdls)
    Description: The 'Fragmenta' theory presented in the Models 2015 paper.
    Author:      Nuno Amálio
*)
theory Fragmenta_TyMdls
imports Fragmenta_Mdls Fragmenta_TFrs Fragmenta_GraphsL

begin

(*Typed Models*)      
record TyMdl = 
  gfgt :: "GFGr_ls"
  frdt :: "V \<rightharpoonup> TFr"

(*Predicate to check that all fragments of a Model are disjoint*)
definition disjTyMdlFrs:: "TyMdl \<Rightarrow> bool"
where
  "disjTyMdlFrs TM \<equiv> disjFs (map (fr o the o frdt TM) (NsG (gfgt TM)))"

(*Gets the union of typed fragments of a model*)
definition UTyMdlFs:: "TyMdl \<Rightarrow> TFr"
where
  "UTyMdlFs TM \<equiv> UTFs (map (the o frdt TM) (NsG (gfgt TM)))"

(*Builds a morphism from a fragment to the GFG, given a GFG node*)
definition consTF2GFG:: "V \<Rightarrow> TyMdl \<Rightarrow> Morph"
where
  "consTF2GFG vf TM \<equiv> SOME m.  
    vf \<in> Ns (toGFGr (gfgt TM)) \<and> (\<exists> TF ef. frdt TM vf = Some TF \<and> 
      src (toGFGr (gfgt TM)) ef = Some vf \<and> tgt (toGFGr (gfgt TM)) ef = Some vf
      \<and> fE m = (\<lambda> e. if e \<in> Es (sg (fr TF))- EsR(sg (fr TF)) then Some ef else None)
      \<and> fV m = (\<lambda> v. if v \<in> Ns (sg (fr TF)) then Some vf else None)
      \<and> m \<in> (morphF2GFGr (fr TF) (toGFGr (gfgt TM))))"

(*Builds the morphism given a list of nodes*)
primrec consTMFs2GFG:: "TyMdl \<Rightarrow> V list \<Rightarrow> Morph"
where
  "consTMFs2GFG TM [] = emptyGM"
  | "consTMFs2GFG TM (vf#vfs) = consTF2GFG vf TM UGM consTMFs2GFG TM vfs"

(*Construct the morphism from the model fragments to the GFG*)
definition mUTM2GFG:: "TyMdl \<Rightarrow> Morph"
where
  "mUTM2GFG TM \<equiv> consTMFs2GFG TM (NsG (gfgt TM))"

(*Well-formedness for models*)
definition is_wf_tmdl :: "TyMdl \<Rightarrow> bool"
where
  "is_wf_tmdl TM \<equiv> (\<forall> TF. TF \<in> ran (frdt TM) \<longrightarrow> is_wf_tfr TF) 
    \<and> ftotal_on (frdt TM) (set (NsG (gfgt TM))) tfr_set
    \<and> disjTyMdlFrs TM \<and> mUTM2GFG TM \<in> (morphF2GFGr (fr (UTyMdlFs TM)) (toGFGr (gfgt TM)))" 

record MdlTy = 
  tmdl :: "TyMdl"
  mdl :: "Mdl"
  mty :: "Morph"

(*Well-formedness for typed models*)
definition is_wf_mdlty :: "MdlTy \<Rightarrow> bool"
where
  "is_wf_mdlty M \<equiv> is_wf_tmdl (tmdl M) \<and> is_wf_mdl (mdl M)
    \<and> mty M \<in> morphFr (UMdlFs (mdl M)) (fr (UTyMdlFs (tmdl M)))"

end