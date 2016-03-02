(*  Title:       Fragmenta theory of Typed Fragments (TFrs and FrTys)
    Description: The 'Fragmenta' theory presented in the Models 2015 paper.
    Author:      Nuno Amálio
*)
theory Fragmenta_TFrs
imports Fragmenta_FrsL Fragmenta_SGs

begin

(*Type Fragments*)      
record TFr = 
  fr :: "Fr"
  iet :: "E \<rightharpoonup> SGETy"

(*Type Fragments with underlying list version*)      
record TFr_ls = 
  fr_ls :: "Fr_ls"
  iet_ls :: "(E \<times> SGETy) list"

(*Set of all fragments*)
definition is_tfr :: "TFr \<Rightarrow> bool"
where
  "is_tfr TF \<equiv> True"

definition tfr_set :: "TFr set"
where
  "tfr_set \<equiv> {TF. is_tfr TF}"

(*Conversion function from list to plain fragment form*)
definition toTFr :: "TFr_ls \<Rightarrow> TFr"
where
  "toTFr TFL \<equiv> \<lparr>fr = toFr (fr_ls TFL), iet = map_of(iet_ls TFL)\<rparr>"

(* Defines the empty Fr*)
definition emptyTFr :: "TFr"
where
  "emptyTFr \<equiv> \<lparr>fr = emptyFr, iet = empty\<rparr>"

(* Defines the instance edge types as overriding. The instance edge type is type of 
meta-edge, unless otherwise stated (Not defined in the Z)*)
definition iety :: "TFr \<Rightarrow> E \<rightharpoonup> SGETy"
where
  "iety TF \<equiv> ety(sg (fr TF)) |` EsA(sg (fr TF)) ++ iet TF"

definition is_wf_tfr :: "TFr \<Rightarrow> bool"
where
  "is_wf_tfr TF \<equiv> is_wf_fr (fr TF) 
    \<and> dom (iet TF) \<subseteq> EsA (sg  (fr TF))
    \<and> ftotal_on (iety TF) (EsA (sg  (fr TF))) (SGETy_set)" 

(*Fragments union*)
definition UTFr :: "TFr \<Rightarrow> TFr \<Rightarrow> TFr" (infixl "UTF" 100)
where
  "TF1 UTF TF2 \<equiv> \<lparr>fr = (fr TF1) UF (fr TF2), iet = iet TF1 ++ iet TF2\<rparr>"

lemma fr_UTF[simp]: "fr (TF1 UTF TF2) = (fr TF1) UF (fr TF2)"
  by (simp add: UTFr_def)

lemma iet_UTF[simp]: "iet (TF1 UTF TF2) = (iet TF1) ++ (iet TF2)"
  by (simp add: UTFr_def)

(* Fragment distributed union*)
primrec UTFs :: "TFr list \<Rightarrow> TFr"
where
  "UTFs [] = emptyTFr"
  | "UTFs (TF#TFs) = TF UTF (UTFs TFs)"


end

