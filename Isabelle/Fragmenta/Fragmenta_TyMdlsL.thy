(*  Title:       Fragmenta theory of Typed Models (Mdls)
    Description: The 'Fragmenta' theory presented in the Models 2015 paper.
    Author:      Nuno Amálio
*)
theory Fragmenta_TyMdlsL
imports Fragmenta_TyMdls Fragmenta_MdlsL 

begin

(*Typed Models as lists*)      
record TyMdl_ls = 
  gfgt_ls :: "GFGr_ls"
  frdt_ls :: "(V \<times> TFr_ls) list"

definition toTyMdl:: "TyMdl_ls \<Rightarrow> TyMdl"
where
  "toTyMdl TML \<equiv> \<lparr>gfgt = gfgt_ls TML, 
    frdt = map_of (zip (map fst (frdt_ls TML)) (map (toTFr o snd) (frdt_ls TML))) \<rparr>"

definition is_wf_tmdlL :: "TyMdl_ls \<Rightarrow> bool"
where
  "is_wf_tmdlL TML \<equiv> distinct (map fst (frdt_ls TML)) \<and> is_wf_tmdl (toTyMdl TML)" 

record MdlTy_ls = 
  tmdlL :: "TyMdl_ls"
  mdlL :: "Mdl_ls"
  mtyL :: "MorphL"

definition toMdlTy:: "MdlTy_ls \<Rightarrow> MdlTy"
where
  "toMdlTy MTL \<equiv> \<lparr>tmdl = toTyMdl(tmdlL MTL), mdl = toMdl(mdlL MTL),
      mty = toMorph (mtyL MTL) \<rparr>"

definition is_wf_mdltyL :: "MdlTy_ls \<Rightarrow> bool"
where
  "is_wf_mdltyL MTL \<equiv> is_wf_MorphL (mtyL MTL) \<and> is_wf_mdlty (toMdlTy MTL)"

end