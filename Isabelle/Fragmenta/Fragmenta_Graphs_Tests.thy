theory Fragmenta_Graphs_Tests
imports Fragmenta_Graphs
begin

lemma "[1\<mapsto>1, 1\<mapsto> 3, 2\<mapsto>4, 3\<mapsto>6] |` {1::nat, 2} = [1\<mapsto>1, 1\<mapsto>3, 2\<mapsto>4] "
    by (auto simp add: restrict_map_def)

definition GI1 :: "Gr"
where
   "GI1 = \<lparr>Ns={''1'', ''2'', ''3''}, Es = {''1'', ''2''}, 
   src = [''1''\<mapsto>''1'', ''2''\<mapsto>''2''], tgt=[''1''\<mapsto>''2'', ''2''\<mapsto>''3'']\<rparr>"

lemma "(src GI1) ''1'' = Some ''1''"
   by (simp add: GI1_def)

lemma "(adjacent ''1'' ''2'' GI1)"
  by (simp add: GI1_def adjacent_def)

lemma "(''1'',''2'') \<in> (relOfGr GI1)"
  by (simp add: GI1_def relOfGr_def adjacent_def)

lemma "restrict GI1 {''1''} = \<lparr>Ns={''1'', ''2''}, Es = {''1''}, 
    src = [''1''\<mapsto>''1''], tgt=[''1''\<mapsto>''2'']\<rparr>"
    by (auto simp add: GI1_def restrict_def rst_Ns_def rst_fun_def)

lemma "replaceGr GI1 [''1''\<mapsto>''4''] = \<lparr>Ns={''4'', ''2'', ''3''}, Es = {''1'', ''2''}, 
   src = [''1''\<mapsto>''4'', ''2''\<mapsto>''2''], tgt=[''1''\<mapsto>''2'', ''2''\<mapsto>''3'']\<rparr>"
    by (auto simp add: GI1_def replaceGr_def replace_emap_def split: if_splits)

axiomatization
where
  Es_GI1_in_V_E: "Es GI1 \<subseteq> V_E"
  and Ns_GI1_in_V_V: "Ns GI1 \<subseteq> V_V"

(* This a mandatory well-formedness proof obligation!"*)
lemma "is_wf_g (GI1)"
  using Es_GI1_in_V_E Ns_GI1_in_V_V
  by (auto simp add: GI1_def is_wf_g_def ftotal_on_def)

end
