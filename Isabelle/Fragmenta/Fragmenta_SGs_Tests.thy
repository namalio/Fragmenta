(*  Description: Theory of tests to validate Fragmenta's theory of 
        structural graphs (SGs)
    Author:      Nuno Amálio
*)
theory Fragmenta_SGs_Tests
imports Fragmenta_SGs 
  "../Extra/Map_Extra" 
  "../Extra/Finite_Transitive_Closure_Simprocs"

begin

lemma "multOk {''1'', ''2'', ''3'', ''4'', ''5''} (rm 1 *) = True"
  unfolding multOk_def ok_multVal_def
  by auto

definition SGI1 :: "SGr"
where
   "SGI1 = \<lparr>Ns={''Employee'', ''Car''}, 
      Es = {''Owns'', ''IEmployeeSelf'', ''ICarSelf''}, 
      src = [''Owns''\<mapsto>''Employee'', ''IEmployeeSelf''\<mapsto>''Employee'', ''ICarSelf''\<mapsto>''Car''], 
      tgt=[''Owns''\<mapsto>''Car'', ''IEmployeeSelf''\<mapsto>''Employee'', ''ICarSelf''\<mapsto>''Car''],
      nty =[''Employee''\<mapsto>nnrml, ''Car''\<mapsto>nnrml],
      ety =[''Owns''\<mapsto>erelbi, ''IEmployeeSelf''\<mapsto>einh, ''ICarSelf''\<mapsto>einh],
      srcm = [''Owns''\<mapsto> sm (val 1)], tgtm = [''Owns''\<mapsto> sm *]\<rparr>"

axiomatization
where
  Es_SGI1_in_V_E: "Es SGI1 \<subseteq> E_A"
  and Ns_SGI1_in_V_V: "Ns SGI1 \<subseteq> V_A"

(* This a mandatory well-formedness proof obligation!"*)
lemma wf_SGI1: "is_wf_sg SGI1"
  proof (simp add: is_wf_sg_def, rule conjI)
     show "is_wf_g SGI1"
     using Es_SGI1_in_V_E Ns_SGI1_in_V_V
      by (auto simp add: is_wf_g_def SGI1_def ftotal_on_def)
  next
    apply_end(rule conjI)
    show "ftotal_on (nty SGI1) (Ns SGI1) SGNTy_set"
      by (auto simp add: SGI1_def ftotal_on_def SGNTy_set_def)
  next
    apply_end(rule conjI)
    show "ftotal_on (ety SGI1) (Es SGI1) SGETy_set"
      by (auto simp add: SGI1_def ftotal_on_def SGETy_set_def)
   next
    apply_end(rule conjI)
    show "dom (srcm SGI1) = dom (tgtm SGI1)"
      by (simp add: SGI1_def)
  next
    apply_end(rule conjI)
    show "dom (tgtm SGI1) = EsTy SGI1 {Some erel, Some ecomp}"
      by (simp add: SGI1_def EsTy_def vimage_def)
  next
    apply_end(rule conjI)
    show "EsR SGI1 \<subseteq> EsId SGI1"
      by (simp add: SGI1_def EsR_def EsId_def EsTy_def vimage_def)
  next
    apply_end(rule conjI)
    show "srcm SGI1 ` EsTy SGI1 {Some ecomp} \<subseteq> {Some (rm 0 (val (Suc 0))), Some (sm (val (Suc 0)))}"
      by (simp add: image_def EsTy_def SGI1_def vimage_def)
  next
    show "acyclicI SGI1"
      by (auto simp add: acyclicI_def inh_def relOfGr_def restrict_def adjacent_def
        rst_fun_def EsI_def EsTy_def vimage_def restrict_map_def SGI1_def EsId_def
        acyclic_def inhG_def elim: tranclE)
  qed

definition SGI2 :: "SGr"
where
   "SGI2 = \<lparr>Ns={''Person'', ''Vehicle'', ''Employee'', ''Car''}, 
      Es = {''IEmployeePerson'', ''ICarVehicle'', ''Owns'', ''IEmployeeSelf'', ''ICarSelf''}, 
      src = [''IEmployeePerson''\<mapsto>''Employee'', ''ICarVehicle''\<mapsto>''Car'', ''Owns''\<mapsto>''Person'',
        ''IEmployeeSelf''\<mapsto>''Employee'', ''ICarSelf''\<mapsto>''Car''], 
      tgt=[''IEmployeePerson''\<mapsto>''Person'', ''ICarVehicle''\<mapsto>''Vehicle'', ''Owns''\<mapsto>''Vehicle'',
        ''IEmployeeSelf''\<mapsto>''Employee'', ''ICarSelf''\<mapsto>''Car''],
      nty =[''Person''\<mapsto>nnrml, ''Vehicle''\<mapsto>nnrml, ''Employee''\<mapsto>nnrml, ''Car''\<mapsto>nnrml],
      ety =[''IEmployeePerson''\<mapsto>einh, ''ICarVehicle''\<mapsto>einh, ''Owns''\<mapsto>erel, 
        ''IEmployeeSelf''\<mapsto>einh, ''ICarSelf''\<mapsto>einh],
      srcm = [''Owns''\<mapsto> sm (val 1)], tgtm = [''Owns''\<mapsto> sm *]\<rparr>"

axiomatization
where
  Es_SGI2_in_E_A: "Es SGI2 \<subseteq> E_A"
  and Ns_SGI2_in_V_A: "Ns SGI2 \<subseteq> V_A"

(* This a mandatory well-formedness proof obligation!"*)
lemma wf_SGI2: "is_wf_sg SGI2"
  proof (simp add: is_wf_sg_def, rule conjI)
    show "is_wf_g SGI2"
      using Es_SGI2_in_E_A Ns_SGI2_in_V_A
      by (auto simp add: SGI2_def is_wf_g_def ftotal_on_def)
  next
    apply_end (rule conjI)
    show "ftotal_on (nty SGI2) (Ns SGI2) SGNTy_set"
      by (auto simp add: SGI2_def is_wf_g_def ftotal_on_def SGNTy_set_def)
  next
    apply_end (rule conjI)
    show "ftotal_on (ety SGI2) (Es SGI2) SGETy_set"
      by (auto simp add: SGI2_def is_wf_g_def ftotal_on_def SGETy_set_def)
  next
    apply_end (rule conjI)
    show "dom (srcm SGI2) = dom (tgtm SGI2)"
      by (auto simp add: SGI2_def EsR_def EsTy_def)
  next
    apply_end (rule conjI)
    show "dom (tgtm SGI2) = EsTy SGI2 {Some erel, Some ecomp}"
      by (auto simp add: SGI2_def EsTy_def split: if_splits)
  next
    apply_end (rule conjI)
    show "EsR SGI2 \<subseteq> EsId SGI2"
      by (auto simp add: SGI2_def EsTy_def EsR_def split: if_splits)
  next
    apply_end (rule conjI)
    show "srcm SGI2 ` EsTy SGI2 {Some ecomp} \<subseteq> {Some (rm 0 (val (Suc 0))), Some (sm (val (Suc 0)))}"
      by (simp add: EsTy_def image_def vimage_def SGI2_def)
  next
    show "acyclicI SGI2"
      by (auto simp add: acyclicI_def restrict_def EsI_def EsR_def EsTy_def EsId_def
        acyclicGr_def relOfGr_def adjacent_def acyclic_def rst_fun_def vimage_def SGI2_def
        inh_def inhG_def elim: tranclE)
  qed

lemma inh_SGI2: "inh SGI2 = {(''Employee'', ''Person''), (''Car'', ''Vehicle'')}"
  proof
    show "inh SGI2 \<subseteq> {(''Employee'', ''Person''), (''Car'', ''Vehicle'')}"
      by (auto simp add: inh_def relOfGr_def adjacent_def restrict_def EsI_def EsTy_def SGI2_def 
            EsId_def rst_fun_def inhG_def) 
  next
    show "{(''Employee'', ''Person''), (''Car'', ''Vehicle'')} \<subseteq> inh SGI2"
       by (simp add: inh_def relOfGr_def adjacent_def restrict_def EsI_def EsTy_def 
          SGI2_def EsId_def rst_fun_def inhG_def) (rule exI[where x="''ICarVehicle''"], simp)
  qed

lemma "clan ''Person'' SGI2 = {''Person'', ''Employee''}"
proof (simp add: clan_def inhst_def inhst_def_simp)
  have h1: "(inh SGI2)\<inverse> = {(''Person'', ''Employee''), (''Vehicle'', ''Car'')}"
      by (auto simp add: inh_SGI2 converse_unfold)
  show "((inh SGI2)\<inverse>)\<^sup>* `` {''Person''} = {''Person'', ''Employee''}" 
    using h1 by (auto simp: rtrancl_Image_eq)
qed

lemma "src SGI2 ''Owns'' \<noteq> Some ''Employee''"
  unfolding SGI2_def
  by auto

lemma "(''Owns'', ''Employee'') \<in> srcst SGI2"
  unfolding srcst_def EsA_def clan_def inhst_def 
  by (simp add: inh_SGI2 EsTy_def)(auto simp add: SGI2_def elim: rtranclE)
  
lemma "(''Owns'', ''Person'') \<in> srcst SGI2"
  unfolding srcst_def EsA_def clan_def inhst_def 
  by (simp add: inh_SGI2 EsTy_def)(auto simp add: SGI2_def elim: rtranclE)

lemma "(''Owns'', ''Car'') \<in> tgtst SGI2"
  unfolding tgtst_def EsA_def clan_def inhst_def 
      restrict_def EsI_def EsTy_def
  by (simp add: inh_SGI2 EsTy_def)(auto simp add: SGI2_def elim: rtranclE)

lemma "(''Owns'', ''Vehicle'') \<in> tgtst SGI2"
   unfolding tgtst_def EsA_def clan_def inhst_def 
   by (simp add: inh_SGI2 EsTy_def)(auto simp add: SGI2_def elim: rtranclE)

definition SGMorph1 :: "MorphTuple"
where
   "SGMorph1 \<equiv> \<lparr>fV=[''Employee''\<mapsto>''Employee'', ''Car''\<mapsto>''Car''],
              fE=[''Owns''\<mapsto>''Owns'', ''IEmployeeSelf''\<mapsto>''IEmployeeSelf'', 
                ''ICarSelf''\<mapsto>''ICarSelf'']\<rparr>"

lemma pfunToRel_fV_SGMorph1: 
  "pfunToRel (fV SGMorph1) = {(''Employee'', ''Employee''), (''Car'', ''Car'')}"
  proof
    show "pfunToRel (fV SGMorph1) \<subseteq> {(''Employee'', ''Employee''), (''Car'', ''Car'')}"
      by (auto simp add: pfunToRel_def SGMorph1_def split : if_splits)
  next
    show "{(''Employee'', ''Employee''), (''Car'', ''Car'')} \<subseteq> pfunToRel (fV SGMorph1)"
     by (auto simp add: pfunToRel_def SGMorph1_def split : if_splits)
  qed

lemma pfunToRel_fE_SGMorph1: 
  "pfunToRel (fE SGMorph1) = {(''Owns'', ''Owns''), (''IEmployeeSelf'', ''IEmployeeSelf''), 
                (''ICarSelf'', ''ICarSelf'')}"
  proof
    show "pfunToRel (fE SGMorph1) \<subseteq> 
      {(''Owns'', ''Owns''), (''IEmployeeSelf'', ''IEmployeeSelf''), 
        (''ICarSelf'', ''ICarSelf'')}"
      by (auto simp add: pfunToRel_def SGMorph1_def split : if_splits)
  next
    show "{(''Owns'', ''Owns''), (''IEmployeeSelf'', ''IEmployeeSelf''), (''ICarSelf'', ''ICarSelf'')}
    \<subseteq> pfunToRel (fE SGMorph1)"
      by (auto simp add: pfunToRel_def SGMorph1_def split : if_splits)
  qed

lemma "SGMorph1 \<in> morphSGr SGI1 SGI2"
  proof (simp add: morphSGr_def wf_SGI1 wf_SGI2, rule conjI)
    show "ftotal_on (fV SGMorph1) (Ns SGI1) (Ns SGI2)"
      by (auto simp add: SGMorph1_def ftotal_on_def SGI1_def SGI2_def)
  next  
    apply_end(rule conjI)
    show "ftotal_on (fE SGMorph1) (Es SGI1) (Es SGI2)"
      by (auto simp add: SGMorph1_def ftotal_on_def SGI1_def SGI2_def)
  next 
    apply_end(rule conjI)
    show "srcst SGI1 O pfunToRel (fV SGMorph1) \<subseteq> pfunToRel (fE SGMorph1) O srcst SGI2"
    proof (rule subrelI)
      fix x y 
      assume "(x, y) \<in> srcst SGI1 O pfunToRel (fV SGMorph1)"
      then show "(x, y) \<in> pfunToRel (fE SGMorph1) O srcst SGI2"
        by (simp add: relcomp_unfold pfunToRel_fV_SGMorph1 pfunToRel_fE_SGMorph1
          srcst_def clan_def inhst_def inh_SGI2) (auto simp add: EsA_def 
          EsTy_def clan_def inhst_def inh_def inhG_def relOfGr_def restrict_def adjacent_def
          EsId_def EsI_def rst_fun_def vimage_def restrict_map_def SGMorph1_def
          SGI1_def SGI2_def split: if_splits elim: rtranclE)
    qed
  next 
    apply_end(rule conjI)
    show "tgtst SGI1 O pfunToRel (fV SGMorph1) \<subseteq> pfunToRel (fE SGMorph1) O tgtst SGI2"
    proof (rule subrelI)
      fix x y 
      assume "(x, y) \<in> tgtst SGI1 O pfunToRel (fV SGMorph1)"
      then show "(x, y) \<in> pfunToRel (fE SGMorph1) O tgtst SGI2"
       by (simp add: relcomp_unfold pfunToRel_fV_SGMorph1 pfunToRel_fE_SGMorph1
          tgtst_def clan_def inhst_def inh_SGI2)(auto simp add: EsA_def 
          EsTy_def clan_def inhst_def inh_def inhG_def relOfGr_def restrict_def adjacent_def
          EsId_def EsI_def rst_fun_def vimage_def restrict_map_def SGMorph1_def
          SGI1_def SGI2_def split: if_splits elim: rtranclE)
    qed
  next 
    show "inhst SGI1 O pfunToRel (fV SGMorph1) \<subseteq> pfunToRel (fV SGMorph1) O inhst SGI2"
    proof (rule subrelI)
      fix x y
      assume "(x, y) \<in> inhst SGI1 O pfunToRel (fV SGMorph1)"
      then show "(x, y) \<in> pfunToRel (fV SGMorph1) O inhst SGI2"
      by (simp add: relcomp_unfold pfunToRel_fV_SGMorph1 pfunToRel_fE_SGMorph1
          clan_def inhst_def inh_SGI2)(auto simp add: EsTy_def 
          inh_def inhG_def relOfGr_def restrict_def adjacent_def
          EsId_def EsI_def rst_fun_def vimage_def restrict_map_def SGMorph1_def
          SGI1_def SGI2_def split: if_splits elim: rtranclE)
    qed
  qed

definition SGMorph2 :: "MorphTuple"
where
   "SGMorph2 \<equiv> \<lparr>fV=[''Employee''\<mapsto>''Employee'', 
                ''Person''\<mapsto>''Employee'', 
                ''Car''\<mapsto>''Car'', 
                ''Vehicle''\<mapsto>''Car''],
              fE=[''Owns''\<mapsto>''Owns'', 
                ''IEmployeePerson''\<mapsto>''IEmployeeSelf'', 
                ''IEmployeeSelf''\<mapsto>''IEmployeeSelf'',
                ''ICarVehicle''\<mapsto>''ICarSelf'', 
                ''ICarSelf''\<mapsto>''ICarSelf'']\<rparr>"

lemma pfunToRel_fV_SGMorph2: 
  "pfunToRel (fV SGMorph2) = {(''Employee'', ''Employee''), (''Person'', ''Employee''), 
      (''Car'', ''Car''), (''Vehicle'',''Car'')}"
  proof
    show "pfunToRel (fV SGMorph2)
    \<subseteq> {(''Employee'', ''Employee''), (''Person'', ''Employee''), (''Car'', ''Car''),
        (''Vehicle'', ''Car'')}"
      by (auto simp add: pfunToRel_def SGMorph2_def split : if_splits)
  next
    show "{(''Employee'', ''Employee''), (''Person'', ''Employee''), (''Car'', ''Car''),
     (''Vehicle'', ''Car'')} \<subseteq> pfunToRel (fV SGMorph2)"
     by (auto simp add: pfunToRel_def SGMorph2_def split : if_splits)
  qed

lemma pfunToRel_fE_SGMorph2: 
  "pfunToRel (fE SGMorph2) = {(''Owns'', ''Owns''), (''IEmployeePerson'', ''IEmployeeSelf''), 
                (''IEmployeeSelf'', ''IEmployeeSelf''),
                (''ICarVehicle'', ''ICarSelf''), 
                (''ICarSelf'', ''ICarSelf'')}"
  proof
    show "pfunToRel (fE SGMorph2) \<subseteq> 
      {(''Owns'', ''Owns''), (''IEmployeePerson'', ''IEmployeeSelf''), 
                (''IEmployeeSelf'', ''IEmployeeSelf''),
                (''ICarVehicle'', ''ICarSelf''), 
                (''ICarSelf'', ''ICarSelf'')}"
      by (auto simp add: pfunToRel_def SGMorph2_def split : if_splits)
  next
    show "{(''Owns'', ''Owns''), (''IEmployeePerson'', ''IEmployeeSelf''),
     (''IEmployeeSelf'', ''IEmployeeSelf''), (''ICarVehicle'', ''ICarSelf''),
     (''ICarSelf'', ''ICarSelf'')} \<subseteq> pfunToRel (fE SGMorph2)"
      by (auto simp add: pfunToRel_def SGMorph2_def split : if_splits)
  qed

lemma "SGMorph2 \<in> morphSGr SGI2 SGI1"
  proof -
    have "inh SGI1 \<subseteq> Id" 
      by (auto simp: inh_def inhG_def relOfGr_def adjacent_def restrict_def EsI_def EsTy_def 
        SGI1_def EsId_def) 
    hence h1: "inhst SGI1 = Id" by (simp add: inhst_inhid)
    show ?thesis
    proof (simp add: morphSGr_def wf_SGI1 wf_SGI2, rule conjI)
      show "ftotal_on (fV SGMorph2) (Ns SGI2) (Ns SGI1)"
      by (auto simp add: SGMorph2_def ftotal_on_def SGI1_def SGI2_def)
    next  
      apply_end(rule conjI)
      show " ftotal_on (fE SGMorph2) (Es SGI2) (Es SGI1)"
        by (auto simp add: SGMorph2_def ftotal_on_def SGI1_def SGI2_def)
    next  
      apply_end(rule conjI)
      show "srcst SGI2 O pfunToRel (fV SGMorph2) \<subseteq> pfunToRel (fE SGMorph2) O srcst SGI1"
        proof (rule subrelI)
          fix x y
          assume "(x, y) \<in> srcst SGI2 O pfunToRel (fV SGMorph2)"
          then show "(x, y) \<in> pfunToRel (fE SGMorph2) O srcst SGI1"
          by (simp add: relcomp_unfold pfunToRel_fV_SGMorph2 pfunToRel_fE_SGMorph2
          srcst_def clan_def h1) (simp add: inhst_def inh_SGI2 EsA_def EsTy_def, 
          auto simp add: SGI2_def SGI1_def split: if_splits elim: rtranclE)
        qed
    next  
      apply_end(rule conjI)
      show "tgtst SGI2 O pfunToRel (fV SGMorph2) \<subseteq> pfunToRel (fE SGMorph2) O tgtst SGI1"
      proof (rule subrelI)
        fix x y
        assume "(x, y) \<in> tgtst SGI2 O pfunToRel (fV SGMorph2)"
        then show "(x, y) \<in> pfunToRel (fE SGMorph2) O tgtst SGI1"
          by (simp add: relcomp_unfold pfunToRel_fV_SGMorph2 pfunToRel_fE_SGMorph2
            tgtst_def clan_def h1)(simp add: inhst_def inh_SGI2 EsA_def EsTy_def, 
            auto simp add: SGI2_def SGI1_def split: if_splits elim: rtranclE)
      qed
    next
      show "inhst SGI2 O pfunToRel (fV SGMorph2) \<subseteq> pfunToRel (fV SGMorph2) O inhst SGI1"
      proof (rule subrelI)
        fix x y
        assume "(x, y) \<in> inhst SGI2 O pfunToRel (fV SGMorph2)"
        then show "(x, y) \<in> pfunToRel (fV SGMorph2) O inhst SGI1"
          by (simp add: relcomp_unfold pfunToRel_fV_SGMorph2 pfunToRel_fE_SGMorph2 h1)
            (auto simp add: inhst_def inh_SGI2 elim: rtranclE)
      qed
   qed
 qed

end
