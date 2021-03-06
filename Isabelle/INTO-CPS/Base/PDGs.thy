
(********  
  Title:      Theory that defines Port dependency graphs
  Author:     Nuno Amálio
***********)

theory PDGs
imports "../../Fragmenta/Base_GraphsL"

begin

(*PDGs use the list based representation of Graphs*)
type_synonym PDGr = Gr_ls

(*A PDG is well-formed if the graph is well-formed and there are no 
  self edges (not reflexive). We require that the sets of edges and nodes is finite.*)
definition is_wf_PDG :: "PDGr \<Rightarrow> bool"
where
  "is_wf_PDG G \<equiv> 
    (let G' = toGr G in
      is_wf_g G' \<and> EsId G' = {} \<and> finite (Es G') \<and> finite (Ns G'))"

definition acyclicPDGr :: "PDGr \<Rightarrow> bool"
where
  "acyclicPDGr G \<equiv> acyclicGr(toGr G)"

end