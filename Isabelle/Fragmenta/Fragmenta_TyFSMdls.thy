(*  Title:       Fragmenta theory of Typed Models with a fragmentation strategy 
    Description: The 'Fragmenta' theory presented in the Models 2015 paper.
    Author:      Nuno Amálio
*)
theory Fragmenta_TyFSMdls
imports Fragmenta_TyMdls 

begin

(*Typed Models with a fragmentation strategy*)
record TyFSMdl = 
  tmdl :: "TyMdl"
  gfg_fs :: "GFGr_ls"
  mfs :: "MorphTuple"

(*Typed Models with a fragmentation strategy*)
record TyFSMdl_ls = 
  tymdl_ls   :: "TyMdl_ls"
  gfg_fs_ls :: "GFGr_ls"
  mfs_ls    :: "MorphTuple"

definition toTyFSMdl :: "TyFSMdl_ls \<Rightarrow> TyFSMdl"
where
  "toTyFSMdl TM = \<lparr>tmdl = toTyMdl(tymdl_ls TM), 
    gfg_fs = gfg_fs_ls TM, 
    mfs = mfs_ls TM\<rparr>"

(*Well-formedness for type models with a fragmentation strategy*)
definition is_wf_tfsmdl :: "TyFSMdl \<Rightarrow> bool"
where
  "is_wf_tfsmdl TM \<equiv> is_wf_tmdl (tmdl TM)
    \<and> is_wf_gfg (toGFGr (gfg_fs TM)) 
    \<and> mfs TM \<in> (morphF2GFGr (fr (UTyMdlFs (tmdl TM))) (toGFGr (gfg_fs TM)))"

record MdlTyFS = 
  tfsmdl :: "TyFSMdl"
  mdl :: "Mdl"
  mty :: "MorphTuple"
  mfs :: "MorphTuple"

record MdlTyFS_ls = 
  tfsmdl_ls :: "TyFSMdl_ls"
  mdl_ls :: "Mdl_ls"
  mty_ls :: "MorphTuple"
  mfs_ls :: "MorphTuple"

definition toMdlTyFS :: "MdlTyFS_ls \<Rightarrow> MdlTyFS"
where
  "toMdlTyFS TM = \<lparr>tfsmdl = toTyFSMdl(tfsmdl_ls TM), 
    mdl = toMdl (mdl_ls TM), 
    mty = mty_ls TM,
    mfs = mfs_ls TM\<rparr>"

(*Well-formedness for typed models*)
definition is_wf_mdltyfs :: "MdlTyFS \<Rightarrow> bool"
where
  "is_wf_mdltyfs MT \<equiv> is_wf_tfsmdl (tfsmdl MT) \<and> is_wf_mdl (mdl MT)
    \<and> mfs MT \<in> (morphGFGr (toGFGr (gfg (mdl MT))) (toGFGr (gfg_fs (tfsmdl MT))))"
(* I need to add more predicates the definition above.*)

definition M_Fr_To_FSGFG:: "Fr \<Rightarrow> V \<Rightarrow> E \<Rightarrow> MorphTuple"
where
  "M_Fr_To_FSGFG F v_GFG e_GFG \<equiv> 
    \<lparr>fV = (\<lambda> v. if v \<in> Ns (withRsG F) then Some v_GFG else None),
     fE = (\<lambda> e. if e \<in> Es (withRsG F) then Some e_GFG else None) \<rparr>"

end