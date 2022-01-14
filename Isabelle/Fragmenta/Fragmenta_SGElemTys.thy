(*  Theory:      SGElemTys
    Description: Definitions related to the different types of SG elements (nodes or edges).
    Author:     Nuno Amálio
*)

theory Fragmenta_SGElemTys
  imports Main
begin

(* Node types of a SG: normal, abstract, proxy, enumeration, 
  value, virtual and optional*)
datatype SGNT = nnrml | nabst | nprxy | nenum | nval | nvirt | nopt
datatype SGED = dbi | duni
datatype SGET = einh | ecomp SGED | erel SGED | ewander | eder

definition SGNT_set :: "SGNT set"
where 
   "SGNT_set = {nnrml, nabst, nprxy, nenum,  nval, nvirt, nopt}"

definition erels::"SGET set"
  where 
  "erels = erel ` {dbi, duni}"

definition ecomps::"SGET set"
  where 
  "ecomps = ecomp ` {dbi, duni}"

definition SGET_set :: "SGET set"
where 
   "SGET_set = {einh, erel dbi, erel duni, 
  ewander, eder} \<union> ecomps \<union> erels"

(*Dictates allowed inheritance relations between node types*)
definition ilt_NT::"SGNT \<Rightarrow> SGNT  \<Rightarrow> bool" (infixl "<\<^sub>N\<^sub>T" 100)
  where
  "nt\<^sub>1 <\<^sub>N\<^sub>T nt\<^sub>2 \<equiv> (nt\<^sub>2 = nenum \<and> nt\<^sub>1 = nval
    \<or> nt\<^sub>1 = nvirt \<and> nt\<^sub>2 = nvirt
    \<or> nt\<^sub>1 = nabst \<and> nt\<^sub>2 \<in> {nabst, nprxy, nvirt})
    \<and> nt\<^sub>1 \<notin> {nprxy, nenum, nopt} \<and> nt\<^sub>2 \<noteq> nopt"

(*Dictates allowed refinement relations between node types*)
definition rleq_NT::"SGNT \<Rightarrow> SGNT  \<Rightarrow> bool" (infixl "\<le>\<^sub>N\<^sub>T" 100)
  where
  "nt\<^sub>1\<le>\<^sub>N\<^sub>T nt\<^sub>2 \<equiv> nt\<^sub>1 = nt\<^sub>2 \<or> nt\<^sub>1 = nprxy 
      \<or> nt\<^sub>2 = nabst \<and> nt\<^sub>1 \<in> {nnrml, nvirt} 
      \<or> nt\<^sub>2 \<in> {nnrml, nopt}"


definition eq_ET:: "SGET \<Rightarrow> SGET \<Rightarrow> bool" (infixl "=\<^sub>E\<^sub>T" 100)
where
  "et\<^sub>1 =\<^sub>E\<^sub>T et\<^sub>2 \<equiv> et\<^sub>1 = et\<^sub>2 \<or> ({et\<^sub>1, et\<^sub>2} \<subseteq> erels)
    \<or> ({et\<^sub>1, et\<^sub>2} \<subseteq> ecomps)"

(*Dictates allowed refinement relations between edge types*)
definition leq_ET:: "SGET \<Rightarrow> SGET \<Rightarrow> bool" (infixl "\<le>\<^sub>E\<^sub>T" 100)
  where
  "et\<^sub>1 \<le>\<^sub>E\<^sub>T et\<^sub>2 \<equiv> einh \<notin>  {et\<^sub>1, et\<^sub>2}  
    \<and> (et\<^sub>1 =\<^sub>E\<^sub>T et\<^sub>2 \<or> et\<^sub>2 = ewander 
      \<or> (et\<^sub>1 = eder \<and> et\<^sub>2 \<in> erels \<union> ecomps))"
end