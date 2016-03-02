(**************************  
    Title:      'Exmp_PDGs_Grs'
    Description: Encodings and proofs of port dependency graphs (PDGs) 
      taken from the Broman papers
    Author:     Nuno Amálio
****************)
theory Exmp_PDGs_Grs

imports PDGs "../Extra/Finite_Transitive_Closure_Simprocs" 
  "../Extra/Trcl_Extra"
begin

(* The Graph of Figure 4, Broman 13*)
definition G1 :: "PDGr"
where
   "G1 = \<lparr>NsG=[''a'', ''b1'', ''b3'', ''b2'', ''b4'', ''c1'',
    ''c3'', ''c2'', ''d1'', ''d2''], 
   EsG = [''e1'', ''e2'', ''e3'', ''e4'', ''e5'', ''e6'', ''e7'', ''e8'', ''e9''], 
   srcG = [(''e1'', ''a''), (''e2'', ''b1''), (''e3'', ''b3''), 
    (''e4'', ''b2''), (''e5'', ''b4''), (''e6'', ''c3''), (''e7'', ''c2''), (''e8'', ''d1''), 
    (''e9'', ''d2'')], 
   tgtG=[(''e1'', ''b1''), (''e2'', ''b4''), (''e3'', ''b2''), 
    (''e4'', ''c1''), (''e5'', ''c3''), (''e6'', ''c2''), (''e7'', ''d1''), (''e8'', ''d2''), 
    (''e9'', ''b3'')]\<rparr>"

axiomatization
where
  Es_G1_in_V_E: "set(EsG G1) \<subseteq> V_E"
  and Ns_G1_in_V_V: "set(NsG G1) \<subseteq> V_V"

(* Checks that the PDG is well-formed"*)
lemma is_wf_G1: "is_wf_PDG G1"
  using Es_G1_in_V_E Ns_G1_in_V_V
  by (auto simp add: is_wf_PDG_def G1_def toGr_def is_wf_g_def ftotal_on_def 
    ran_def EsId_def)

(* Checks that the graph is acyclic*)
lemma "acyclicPDGr G1"
  proof -
    let ?rel_G1 = "{(''a'', ''b1''), (''b1'', ''b4''), (''b3'', ''b2''), 
      (''b3'', ''b2''), (''b2'', ''c1''), (''b4'', ''c3''), (''c3'', ''c2''),
      (''c2'', ''d1''), (''d1'', ''d2''), (''d2'', ''b3'')}"
    have "is_wf_g (toGr G1)"
      using is_wf_G1 by (simp add: is_wf_PDG_def Let_def)
    then have h1: "relOfGr (toGr G1) = ?rel_G1"
      by (simp add: relOfGr_eq_consRel)(eval)
    show "?thesis"
    proof (simp add: acyclicPDGr_def acyclicGr_def acyclic_def, clarify)
      fix x
      assume h2: "(x, x) \<in> (relOfGr (toGr G1))\<^sup>+"
      then have h3 : "x \<in> Domain (relOfGr (toGr G1))"
        by (rule in_trancl_in_Domain)
      show "False"
      proof (case_tac "x = ''a''")
        assume h4: "x = ''a''"
        have "(''a'', ''a'') \<notin> (relOfGr (toGr G1))\<^sup>+"
          by (simp add: h1 trancl_in)
        then show "False"
          using h2 h4 by auto
      next
        assume h4: "x \<noteq> ''a''"
        then show "False"
        proof (case_tac "x = ''b1''")
          assume h5: "x = ''b1''"
          have "(''b1'', ''b1'') \<notin> (relOfGr (toGr G1))\<^sup>+"
            by (simp add: h1 trancl_in)
          then show "False"
            using h2 h5 by auto 
        next
          assume h5: "x \<noteq> ''b1''"
          then show "False"
          proof (case_tac "x = ''b2''")
            assume h6: "x = ''b2''"
            have "(''b2'', ''b2'') \<notin> (relOfGr (toGr G1))\<^sup>+"
              by (simp add: h1 trancl_in)
            then show "False"
              using h2 h6 by auto
          next
            assume h6: "x \<noteq> ''b2''"
            then show "False"
            proof (case_tac "x = ''b3''")
              assume h7: "x = ''b3''"
              have "(''b3'', ''b3'') \<notin> (relOfGr (toGr G1))\<^sup>+"
                by (simp add: h1 trancl_in)
              then show "False"
                using h2 h7 by auto
            next
              assume h7: "x \<noteq> ''b3''"
              then show "False"
              proof (case_tac "x = ''b4''")
                assume h8: "x = ''b4''"
                have "(''b4'', ''b4'') \<notin> (relOfGr (toGr G1))\<^sup>+"
                  by (simp add: h1 trancl_in)
                then show "False"
                  using h2 h8 by auto
              next
                assume h8: "x \<noteq> ''b4''"
                then show "False"
                proof (case_tac "x = ''c1''")
                  assume h9: "x = ''c1''"
                  have "(''c1'', ''c1'') \<notin> (relOfGr (toGr G1))\<^sup>+"
                    by (simp add: h1 trancl_in)
                  then show "False"
                    using h2 h9 by auto
                next
                  assume h9: "x \<noteq> ''c1''"
                  then show "False" 
                  proof (case_tac "x = ''c2''")
                    assume h10: "x = ''c2''"
                    have "(''c2'', ''c2'') \<notin> (relOfGr (toGr G1))\<^sup>+"
                      by (simp add: h1 trancl_in)
                    then show "False"
                      using h2 h10 by auto
                  next
                    assume h10: "x \<noteq> ''c2''"
                    then show "False"
                    proof (case_tac "x = ''c3''")
                      assume h11: "x = ''c3''"
                      have "(''c3'', ''c3'') \<notin> (relOfGr (toGr G1))\<^sup>+"
                        by (simp add: h1 trancl_in)
                      then show "False"
                        using h2 h11 by auto
                    next
                      assume h11: "x \<noteq> ''c3''"
                      then show "False"
                      proof (case_tac "x = ''d1''")
                        assume h12: "x = ''d1''"
                        have "(''d1'', ''d1'') \<notin> (relOfGr (toGr G1))\<^sup>+"
                          by (simp add: h1 trancl_in)
                        then show "False"
                          using h2 h12 by auto
                      next
                        assume h12: "x \<noteq> ''d1''"
                        then show "False"
                        proof (case_tac "x = ''d2''")
                          assume h13: "x = ''d2''"
                          have "(''d2'', ''d2'') \<notin> (relOfGr (toGr G1))\<^sup>+"
                            by (simp add: h1 trancl_in)
                          then show "False"
                            using h2 h13 by auto
                        next
                          assume h13: "x \<noteq> ''d2''"
                          show "False"
                            using h1 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
                            by (auto)
                        qed
                      qed
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
   qed
 qed

(* A modified version of Graph of Figure 4, Broman 13 with a cycle*)
definition G2 :: "PDGr"
where
   "G2 = \<lparr>NsG=[''a'', ''b1'', ''b3'', ''b2'', ''b4'', ''c1'',
    ''c3'', ''c2'', ''d1'', ''d2''], 
   EsG = [''e1'', ''e2'', ''e3'', ''e4'', ''e5'', ''e6'', ''e7'', ''e8'', ''e9'', ''e10''], 
   srcG = [(''e1'', ''a''), (''e2'', ''b1''), (''e3'', ''b3''), 
    (''e4'', ''b2''), (''e5'', ''b4''), (''e6'', ''c3''), (''e7'', ''c2''), (''e8'', ''d1''), 
    (''e9'', ''d2''), (''e10'', ''c1'')], 
   tgtG=[(''e1'', ''b1''), (''e2'', ''b4''), (''e3'', ''b2''), 
    (''e4'', ''c1''), (''e5'', ''c3''), (''e6'', ''c2''), (''e7'', ''d1''), (''e8'', ''d2''), 
    (''e9'', ''b3''), (''e10'', ''c2'')]\<rparr>"

axiomatization
where
  Es_G2_in_V_E: "set(EsG G2) \<subseteq> V_E"
  and Ns_G2_in_V_V: "set(NsG G2) \<subseteq> V_V"

(* Checks that the PDG is well-formed"*)
lemma "is_wf_PDG G2"
  using Es_G2_in_V_E Ns_G2_in_V_V
  by (auto simp add: is_wf_PDG_def G2_def toGr_def is_wf_g_def ftotal_on_def ran_def
    EsId_def)

(* The Graph of PDSG, Figure 4 in Broman 14*)
definition G3 :: "PDGr"
where
   "G3 = \<lparr>NsG=[''y1'', ''y2'', ''x'', ''y'', ''s'', ''x1'', ''x2''], 
    EsG = [''e1'', ''e2'', ''e3'', ''e4'', ''e5'', ''e6''], 
   srcG = [(''e1'', ''y1''), (''e2'', ''y2''), (''e3'', ''y2''), 
      (''e4'', ''s''), (''e5'', ''y''), (''e6'',''x'')], 
   tgtG=[(''e1'', ''x''), (''e2'', ''s''), (''e3'', ''x2''), (''e4'', ''y''), (''e5'', ''x1''),
   (''e6'', ''y'')]\<rparr>"

axiomatization
where
  Es_G3_in_V_E: "set(EsG G3) \<subseteq> V_E"
  and Ns_G3_in_V_V: "set(NsG G3) \<subseteq> V_V"

(* Checks that the graph is well-formed"*)
lemma is_wf_G3: "is_wf_PDG G3"
  using Es_G3_in_V_E Ns_G3_in_V_V
  by (auto simp add: G3_def is_wf_g_def is_wf_PDG_def EsId_def ftotal_on_def toGr_def)

(* Checks that the graph is acyclic*)
lemma "acyclicPDGr G3"
  proof -
    let ?rel_G3 = "{(''y1'', ''x''), (''y2'', ''s''), (''y2'', ''x2''), 
      (''s'', ''y''), (''x'', ''y''), (''y'', ''x1'')}"
    have "is_wf_g (toGr G3)"
      using is_wf_G3 by (simp add: is_wf_PDG_def Let_def)
    then have h1: "relOfGr (toGr G3) = ?rel_G3"
      by (simp add: relOfGr_eq_consRel)(eval)
    show "?thesis"
    proof (simp add: acyclicPDGr_def acyclicGr_def acyclic_def, clarify)
      fix x
      assume h2: "(x, x) \<in> (relOfGr (toGr G3))\<^sup>+"
      then have h3 : "x \<in> Domain (relOfGr (toGr G3))"
        by (rule in_trancl_in_Domain)
      show "False"
      proof (case_tac "x = ''y1''")
        assume h4: "x = ''y1''"
        have "(''y1'', ''y1'') \<notin> (relOfGr (toGr G3))\<^sup>+"
          by (simp add: h1 trancl_in)
        then show "False"
          using h2 h4 by auto
      next
        assume h4: "x \<noteq> ''y1''"
        then show "False"
        proof (case_tac "x = ''y2''")
          assume h5: "x = ''y2''"
          have "(''y2'', ''y2'') \<notin> (relOfGr (toGr G3))\<^sup>+"
            by (simp add: h1 trancl_in)
          then show "False"
            using h2 h5 by auto 
        next
          assume h5: "x \<noteq> ''y2''"
          then show "False"
          proof (case_tac "x = ''s''")
            assume h6: "x = ''s''"
            have "(''s'', ''s'') \<notin> (relOfGr (toGr G3))\<^sup>+"
              by (simp add: h1 trancl_in)
            then show "False"
              using h2 h6 by auto 
          next
            assume h6: "x \<noteq> ''s''"
            then show "False"
            proof (case_tac "x = ''y''")
              assume h7: "x = ''y''"
              have "(''y'', ''y'') \<notin> (relOfGr (toGr G3))\<^sup>+"
                by (simp add: h1 trancl_in)
              then show "False"
                using h2 h7 by auto 
            next
              assume h7: "x \<noteq> ''y''"
              show "False"
              proof (case_tac "x = ''x''")
                assume h8: "x = ''x''"
                have "(''x'', ''x'') \<notin> (relOfGr (toGr G3))\<^sup>+"
                  by (simp add: h1 trancl_in)
                then show "False"
                  using h2 h8 by auto 
              next
                assume h8: "x \<noteq> ''x''"
                show "False"
                  using h1 h3 h4 h5 h6 h7 h8 by simp
              qed
            qed
          qed
        qed
      qed
    qed
  qed

(* A variation of the Graph of PDSG, Figure 4 in Broman 14*)
definition G3b :: "PDGr"
where
   "G3b = \<lparr>NsG=[''y1'', ''y2'', ''x'', ''y'', ''s'', ''x1'', ''x2'', ''y3'', ''x0''], 
    EsG = [''e1'', ''e2'', ''e3'', ''e4'', ''e5'', ''e6'', ''e7'', ''e8'', ''e9''], 
   srcG = [(''e1'', ''y1''), (''e2'', ''y2''), (''e3'', ''y2''), 
    (''e4'', ''s''), (''e5'', ''y''), (''e6'', ''x''), (''e7'', ''x1''), (''e8'', ''y3''), 
    (''e9'', ''x0'')], 
   tgtG=[(''e1'', ''x''), (''e2'', ''s''), (''e3'', ''x2''), (''e4'', ''y''), (''e5'', ''x1''),
    (''e6'', ''y''), (''e7'', ''y3''), (''e8'', ''x0''), (''e9'', ''y1'')]\<rparr>"

axiomatization
where
  Es_G3b_in_V_E: "set(EsG G3b) \<subseteq> V_E"
  and Ns_G3b_in_V_V: "set(NsG G3b) \<subseteq> V_V"

(* Checks that the graph is well-formed"*)
lemma is_wf_G3b:"is_wf_PDG G3b"
  using Es_G3b_in_V_E Ns_G3_in_V_V
  by (auto simp add: G3b_def is_wf_g_def is_wf_PDG_def EsId_def ftotal_on_def toGr_def)

(* Checks that the graph is not acyclic*)
lemma "\<not> (acyclicPDGr G3b)"
  proof -
    let ?rel_G3b = "{(''y1'', ''x''), (''y2'', ''s''), (''y2'', ''x2''), 
      (''s'', ''y''),  (''x'', ''y''), (''y'', ''x1''), (''x1'', ''y3''), 
      (''y3'', ''x0''), (''x0'', ''y1'')}"
    have "is_wf_g (toGr G3b)"
      using is_wf_G3b by (simp add: is_wf_PDG_def Let_def)
    then have h1: "relOfGr (toGr G3b) = ?rel_G3b"
      by (simp add: relOfGr_eq_consRel)(eval)
    then have h1: "(''x'', ''x'') \<in> (relOfGr (toGr G3b))\<^sup>+"
      by (simp add: trancl_in)
    from h1 show "?thesis"
      by (simp add: acyclicPDGr_def acyclicGr_def acyclic_def, rule exI[where x="''x''"])
  qed

(* This is an example that is based of Figures 2 and 3 of Broman 2013. 
In this example we explore the leftmost graph of Fig. 3, which does not 
have an algebraic loop.*)

definition G4a :: "PDGr"
where
   "G4a = \<lparr>NsG = [''u'', ''y1'', ''y2'', ''x'', ''y'', ''z''], 
    EsG = [''e1'', ''e2'', ''e3'', ''e4'', ''e5''],
    srcG = [(''e1'', ''x''), (''e2'', ''y''), (''e3'', ''u''), 
      (''e4'', ''y2''), (''e5'', ''y1'')], 
    tgtG =[(''e1'', ''y''), (''e2'', ''u''), (''e3'', ''y2''), (''e4'', ''z''),
       (''e5'', ''x'')]\<rparr>"

axiomatization
where
  Es_G4a_in_V_E: "set(EsG G4a) \<subseteq> V_E"
  and Ns_G4a_in_V_V: "set(NsG G4a) \<subseteq> V_V"

(* Checks that the graph is well-formed"*)
lemma is_wf_G4a: "is_wf_PDG G4a"
  using Es_G4a_in_V_E Ns_G4a_in_V_V
  by (auto simp add: G4a_def is_wf_g_def is_wf_PDG_def ftotal_on_def EsId_def toGr_def)

(* Checks that the graph is acyclic*)
lemma "acyclicPDGr G4a"
  proof -
    let ?rel_G4a = "{(''x'', ''y''), (''y'', ''u''), (''u'', ''y2''), 
      (''y2'', ''z''), (''y1'', ''x'')}"
    have "is_wf_g (toGr G4a)"
      using is_wf_G4a by (simp add: is_wf_PDG_def Let_def)
    then have h1: "relOfGr (toGr G4a) = ?rel_G4a"
      by (simp add: relOfGr_eq_consRel)(eval)
    show "?thesis"
    proof (simp add: acyclicPDGr_def acyclicGr_def acyclic_def, clarify)
      fix x
      assume h2: "(x, x) \<in> (relOfGr (toGr G4a))\<^sup>+"
      then have h3 : "x \<in> Domain (relOfGr (toGr G4a))"
        by (rule in_trancl_in_Domain)
      show "False"
      proof (case_tac "x = ''x''")
        assume h4: "x = ''x''"
        have "(''x'', ''x'') \<notin> (relOfGr (toGr G4a))\<^sup>+"
          by (simp add: h1 trancl_in)
        then show "False"
          using h2 h4 by auto
      next
        assume h4: "x \<noteq> ''x''"
        then show "False"
        proof (case_tac "x = ''y''")
          assume h5: "x = ''y''"
          have "(''y'', ''y'') \<notin> (relOfGr (toGr G4a))\<^sup>+"
            by (simp add: h1 trancl_in)
          then show "False"
            using h2 h5 by auto
        next
          assume h5: "x \<noteq> ''y''"
          then show "False"
          proof (case_tac "x = ''u''")
            assume h6: "x = ''u''"
            have "(''u'', ''u'') \<notin> (relOfGr (toGr G4a))\<^sup>+"
              by (simp add: h1 trancl_in)
            then show "False"
              using h2 h6 by auto
          next
            assume h6: "x \<noteq> ''u''"
            then show "False"
            proof (case_tac "x = ''y2''")
              assume h7: "x = ''y2''"
              have "(''y2'', ''y2'') \<notin> (relOfGr (toGr G4a))\<^sup>+"
                by (simp add: h1 trancl_in)
              then show "False"
                using h2 h7 by auto
            next
              assume h7: "x \<noteq> ''y2''"
              then show "False"
              proof (case_tac "x = ''y1''")
                assume h8: "x = ''y1''"
                have "(''y1'', ''y1'') \<notin> (relOfGr (toGr G4a))\<^sup>+"
                  by (simp add: h1 trancl_in)
                then show "False"
                  using h2 h8 by auto
              next
                assume h8: "x \<noteq> ''y1''"
                then show "False"
                  using h1 h3 h4 h5 h6 h7 h8 by auto
             qed
          qed
        qed
      qed
    qed
  qed
qed

(* This is an example that is based of Figures 2 and 3 of Broman 2013. 
In this example we explore the rightmost graph of Fig. 3, which has 
an algebraic loop.*)
definition G4b :: "PDGr"
where
   "G4b = \<lparr>NsG=[''u'', ''y1'', ''y2'', ''x'', ''y'', ''z''], 
    EsG = [''e1'', ''e2'', ''e3'', ''e4'', ''e5''],
    srcG = [(''e1'', ''x''), (''e2'', ''y''), (''e3'', ''u''), (''e4'', ''y2''), 
      (''e5'', ''y1'')], 
    tgtG = [(''e1'', ''y''), (''e2'', ''u''), (''e3'', ''y2''), (''e4'', ''x''),
       (''e5'', ''z'')]\<rparr>"

axiomatization
where
  Es_G4b_in_V_E: "set (EsG G4b) \<subseteq> V_E"
  and Ns_G4b_in_V_V: "set (NsG G4b) \<subseteq> V_V"

(* Checks that the graph is well-formed"*)
lemma is_wf_G4b: "is_wf_PDG G4b"
  using Es_G4b_in_V_E Ns_G4b_in_V_V
  by (auto simp add: G4b_def is_wf_g_def is_wf_PDG_def ftotal_on_def EsId_def toGr_def)

(* Checks that the graph is not acyclic*)
lemma "\<not> (acyclicPDGr G4b)"
  proof -
    let ?rel_G4b = "{(''x'', ''y''), (''y'', ''u''), (''u'', ''y2''),
      (''y2'', ''x''), (''y1'', ''z'')}"
    have "is_wf_g (toGr G4b)"
      using is_wf_G4b by (simp add: is_wf_PDG_def Let_def)
    then have h1: "relOfGr (toGr G4b) = ?rel_G4b"
      by (simp add: relOfGr_eq_consRel)(eval)
    then have h1: "(''x'', ''x'') \<in> (relOfGr (toGr G4b))\<^sup>+"
      by (simp add: trancl_in)
    from h1 show "?thesis"
      by (simp add: acyclicPDGr_def acyclicGr_def acyclic_def, 
          rule exI[where x="''x''"])
  qed

end
