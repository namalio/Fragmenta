(********  
  Theory: 'PDG_To_Alloy'
  Description:  Theory that converts PDGs to Alloy
  Author:     Nuno Amálio
***********)

theory PDG_To_Alloy
imports Alloy_ast PDGs

begin

(*Defines the 'Ports' signature in Alloy*)
abbreviation sigPorts :: "SigDecl"
where
  "sigPorts \<equiv> sig sabstract None [''Port''] None
    [dc [''tgt''] (dset None (\<aa>set (AExpid ''Port'')))]
    [(AExpid ''tgt'') \<aa>!= \<aa>this]"

(*Defines acyclic assertion on 'tgt' in Alloy*)
abbreviation assertAcyclic :: "AssertDecl"
where
  "assertAcyclic \<equiv> assert ''AcyclicTgt'' 
    [\<aa>no (\<aa>^(AExpid ''tgt'') \<aa>& \<aa>iden)]"

primrec wrConstraintOfEgdes::"PDGr \<Rightarrow> E list \<Rightarrow> AExp"
where
  "wrConstraintOfEgdes PDG [] = \<aa>none" |
  "wrConstraintOfEgdes PDG (e#es) = 
    (if es = []
      then AExpid (the (tgt (toGr PDG) e))
      else AExpid (the (tgt (toGr PDG) e)) \<aa>+ (wrConstraintOfEgdes PDG es))"

fun wrConstraintOfNode::"PDGr \<Rightarrow> V \<Rightarrow> AExp"
where
  "wrConstraintOfNode PDG v = 
    (let es_fr_v = incidentEsSrc_ls PDG v in
      (if es_fr_v = [] then (\<aa>no ((AExpid v)\<aa>.(AExpid ''tgt'')))
        else (((AExpid v)\<aa>.(AExpid ''tgt'')) 
          \<aa>= (wrConstraintOfEgdes PDG es_fr_v))))"

fun wrConstraintsOfNodes::"PDGr \<Rightarrow> V list \<Rightarrow> AExp list"
where
  "wrConstraintsOfNodes PDG vs = map (wrConstraintOfNode PDG) vs"

definition toAlloyFactOfPDGPorts:: "PDGr \<Rightarrow> FactDecl"
where
  "toAlloyFactOfPDGPorts PDG \<equiv> fact '''' (wrConstraintsOfNodes PDG (NsG PDG))"

definition toAlloySigOfPDGPorts:: "PDGr \<Rightarrow> SigDecl"
where
  "toAlloySigOfPDGPorts PDG \<equiv> sig snormal (Some mone) (NsG PDG) (Some ''Port'')[][]"

definition toAlloyCheck:: "PDGr \<Rightarrow> CheckDecl"
where
  "toAlloyCheck PDG \<equiv> check ''AcyclicTgt'' (length (NsG PDG))"

definition toAlloy :: "PDGr \<Rightarrow> AlloyModule"
where
  "toAlloy PDG \<equiv> amodule ''algebraicLoopCheck'' 
    [psig sigPorts, psig (toAlloySigOfPDGPorts PDG), 
      pfact (toAlloyFactOfPDGPorts PDG), passert assertAcyclic,
      pcheck (toAlloyCheck PDG)]"

end