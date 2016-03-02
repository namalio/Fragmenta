(*  Title:      Theory of the INTO SysML MM, which is defined as fragments.
      This theory includes the global definitions of the MM
    Author:     Nuno Amálio
*)

theory INTO_SysML_MM_Gbl
imports INTO_SysML_MM_Frs PDGs "../Fragmenta/Fragmenta_TyMdlsL"
  
begin

definition GFG_INTO_SysML_MM :: "GFGr_ls"
where
  "GFG_INTO_SysML_MM \<equiv> 
    \<lparr>NsG = [''F_Common'', ''F_Props'', ''F_ASD'', ''F_Blocks'', 
      ''F_PTypes'', ''F_VTypes'', ''F_Comps'', ''F_CD''], 
      EsG= [''E_F_Common'', ''E_F_Props'', ''E_F_ASD'', ''E_F_Blocks'',
        ''E_F_PTypes'', ''E_F_VTypes'', ''E_F_Comps'', ''E_F_CD'',
        ''E_F_ASD_I_F_Common'', ''E_F_Props_I_F_Common'',
        ''E_F_Props_I_F_PTypes'',
        ''E_F_PTypes_I_F_Common'', ''E_F_VTypes_I_F_Props'',
        ''E_F_VTypes_I_F_PTypes'',
        ''E_F_Blocks_I_F_Props'',
        ''E_F_Comps_I_F_Blocks'', ''E_F_Comps_I_F_VTypes'',
        ''E_F_Blocks_C_F_ASD'', ''E_F_Comps_C_F_ASD'', ''E_F_VTypes_C_F_ASD'',
        ''E_F_CD_I_F_Blocks'', ''E_F_CD_I_F_VTypes''], 
      srcG = [(''E_F_Common'', ''F_Common''), (''E_F_Props'', ''F_Props''),
        (''E_F_ASD'', ''F_ASD''), (''E_F_Blocks'', ''F_Blocks''),
        (''E_F_CD'', ''F_CD''),
        (''E_F_PTypes'', ''F_PTypes''), (''E_F_VTypes'', ''F_VTypes''),
        (''E_F_Comps'', ''F_Comps''), 
        (''E_F_ASD_I_F_Common'', ''F_ASD''), 
        (''E_F_Props_I_F_Common'', ''F_Props''), 
        (''E_F_Props_I_F_PTypes'', ''F_Props''),
        (''E_F_PTypes_I_F_Common'', ''F_PTypes''), 
        (''E_F_VTypes_I_F_Props'', ''F_VTypes''),
        (''E_F_VTypes_I_F_PTypes'', ''F_VTypes''),
        (''E_F_Blocks_I_F_Props'', ''F_Blocks''),
        (''E_F_Comps_I_F_Blocks'', ''F_Comps''), 
        (''E_F_Comps_I_F_VTypes'', ''F_Comps''),
        (''E_F_Blocks_C_F_ASD'', ''F_Blocks''), 
        (''E_F_Comps_C_F_ASD'', ''F_Comps''), 
        (''E_F_VTypes_C_F_ASD'', ''F_VTypes''),
        (''E_F_CD_I_F_Blocks'', ''F_CD''), (''E_F_CD_I_F_VTypes'', ''F_CD'')],
      tgtG = [
        (''E_F_Common'', ''F_Common''), (''E_F_Props'', ''F_Props''),
        (''E_F_ASD'', ''F_ASD''), (''E_F_Blocks'', ''F_Blocks''),
        (''E_F_PTypes'', ''F_PTypes''), (''E_F_VTypes'', ''F_VTypes''),
        (''E_F_Comps'', ''F_Comps''), (''E_F_CD'', ''F_CD''),
        (''E_F_ASD_I_F_Common'', ''F_Common''), 
        (''E_F_Props_I_F_Common'', ''F_Common''),
        (''E_F_Props_I_F_PTypes'', ''F_PTypes''),
        (''E_F_PTypes_I_F_Common'', ''F_Common''), 
        (''E_F_VTypes_I_F_Props'', ''F_Props''),
        (''E_F_VTypes_I_F_PTypes'', ''F_PTypes''),
        (''E_F_Blocks_I_F_Props'', ''F_Props''),
        (''E_F_Comps_I_F_Blocks'', ''F_Blocks''), 
        (''E_F_Comps_I_F_VTypes'', ''F_VTypes''),
        (''E_F_Blocks_C_F_ASD'', ''F_ASD''), 
        (''E_F_Comps_C_F_ASD'', ''F_ASD''), 
        (''E_F_VTypes_C_F_ASD'', ''F_ASD''),
        (''E_F_CD_I_F_Blocks'', ''F_Blocks''), (''E_F_CD_I_F_VTypes'', ''F_VTypes'')],
      ext_ty_ls = [
        (''E_F_Common'', eimp), (''E_F_Props'', eimp),
        (''E_F_ASD'', eimp), (''E_F_Blocks'', eimp),
        (''E_F_PTypes'', eimp), (''E_F_VTypes'', eimp),
        (''E_F_Comps'', eimp), (''E_F_CD'', eimp),
        (''E_F_ASD_I_F_Common'', eimp), (''E_F_Props_I_F_Common'', eimp),
        (''E_F_Props_I_F_PTypes'', eimp), (''E_F_PTypes_I_F_Common'', eimp), 
        (''E_F_VTypes_I_F_Props'', eimp), (''E_F_VTypes_I_F_PTypes'', eimp),
        (''E_F_Blocks_I_F_Props'', eimp),
        (''E_F_Comps_I_F_Blocks'', eimp), (''E_F_Comps_I_F_VTypes'', eimp),
        (''E_F_Blocks_C_F_ASD'', econti), (''E_F_Comps_C_F_ASD'', econti), 
        (''E_F_VTypes_C_F_ASD'', econti), (''E_F_CD_I_F_Blocks'', eimp),
        (''E_F_CD_I_F_VTypes'', eimp)]\<rparr>"

axiomatization
where
  Es_GFG_INTO_SysML_MM: "Es (toGFGr(GFG_INTO_SysML_MM)) \<subseteq> E_A"
  and Ns_GFG_INTO_SysML_MM: "Ns (toGFGr(GFG_INTO_SysML_MM)) \<subseteq> V_A"

lemma is_wf_gfg_GFG_INTO_SysML_MM: "is_wf_gfg_ls GFG_INTO_SysML_MM"
  proof -
    have h_wf_g: "is_wf_g (toGFGr GFG_INTO_SysML_MM)"
      using Es_GFG_INTO_SysML_MM Ns_GFG_INTO_SysML_MM
        by (auto simp add: is_wf_g_def GFG_INTO_SysML_MM_def ftotal_on_def toGFGr_def)
    show ?thesis
    proof (simp add: is_wf_gfg_ls_def, rule conjI)
      show "distinct (NsG GFG_INTO_SysML_MM)"
        by (simp add: GFG_INTO_SysML_MM_def)
    next
      apply_end(rule conjI)
      show "distinct (map fst (srcG GFG_INTO_SysML_MM))"
        by (simp add: GFG_INTO_SysML_MM_def)
    next
      apply_end(rule conjI)
      show "distinct (map fst (tgtG GFG_INTO_SysML_MM))"
        by (simp add: GFG_INTO_SysML_MM_def)
    next
      show "is_wf_gfg (toGFGr GFG_INTO_SysML_MM)"
      proof (simp add: is_wf_gfg_def, rule conjI)
        show "is_wf_g (toGFGr GFG_INTO_SysML_MM)"
          using h_wf_g by simp
        next
          apply_end (rule conjI)
          show "ftotal_on (ext_ty (toGFGr GFG_INTO_SysML_MM)) (Es (toGFGr GFG_INTO_SysML_MM)) GFGEdgeTy_set"
            by (simp add: GFG_INTO_SysML_MM_def GFGEdgeTy_set_def ftotal_on_def toGFGr_def)
        next
          apply_end (rule conjI)
          show "NodesWithSelfEdges (toGFGr GFG_INTO_SysML_MM)"
          proof (simp add: NodesWithSelfEdges_def, clarify)
            fix v
            assume "v \<in> Ns (toGFGr GFG_INTO_SysML_MM)"
            then have h1: "v = ''F_Common'' \<or> v = ''F_Props'' \<or> v = ''F_Comps''
              \<or> v = ''F_ASD'' \<or> v = ''F_Blocks''
              \<or> v = ''F_VTypes'' \<or> v = ''F_PTypes'' \<or> v = ''F_CD''"
              by (auto simp add: GFG_INTO_SysML_MM_def toGFGr_def)
            then show "\<exists>e. e \<in> Es (toGFGr GFG_INTO_SysML_MM) 
              \<and> src (toGFGr GFG_INTO_SysML_MM) e = Some v 
              \<and> tgt (toGFGr GFG_INTO_SysML_MM) e = Some v"
            proof (case_tac "v = ''F_Common''")
              assume "v = ''F_Common''"
              then show ?thesis 
                by (simp add: GFG_INTO_SysML_MM_def toGFGr_def)
                  (rule exI[where x="''E_F_Common''"], simp)
            next
              assume h2: "v \<noteq> ''F_Common''"
              then show ?thesis
              proof (case_tac "v = ''F_Props''")
                assume "v = ''F_Props''"
                then show ?thesis 
                  by (simp add: GFG_INTO_SysML_MM_def toGFGr_def)
                    (rule exI[where x="''E_F_Props''"], simp)
              next
                assume h3: "v \<noteq> ''F_Props''"
                then show ?thesis
                proof (case_tac "v = ''F_Comps''")
                  assume "v = ''F_Comps''"
                  then show ?thesis 
                    by (simp add: GFG_INTO_SysML_MM_def toGFGr_def)
                      (rule exI[where x="''E_F_Comps''"], simp)
                next
                  assume h4: "v \<noteq> ''F_Comps''"
                  then show ?thesis
                  proof (case_tac "v = ''F_ASD''")
                    assume "v = ''F_ASD''"
                    then show ?thesis 
                      by (simp add: GFG_INTO_SysML_MM_def toGFGr_def)
                        (rule exI[where x="''E_F_ASD''"], simp)
                  next
                    assume h5: "v \<noteq> ''F_ASD''" 
                    then show ?thesis 
                    proof (case_tac "v = ''F_Blocks''")
                      assume "v = ''F_Blocks''"
                      then show ?thesis 
                        by (simp add: GFG_INTO_SysML_MM_def toGFGr_def)
                          (rule exI[where x="''E_F_Blocks''"], simp)
                    next
                      assume h6: "v \<noteq> ''F_Blocks''" 
                      then show ?thesis 
                      proof (case_tac "v = ''F_VTypes''")
                        assume "v = ''F_VTypes''"
                        then show ?thesis 
                          by (simp add: GFG_INTO_SysML_MM_def toGFGr_def)
                            (rule exI[where x="''E_F_VTypes''"], simp)
                      next
                        assume h7: "v \<noteq> ''F_VTypes''" 
                        then show ?thesis 
                        proof (case_tac "v = ''F_PTypes''") 
                          assume "v = ''F_PTypes''"
                          then show ?thesis 
                            by (simp add: GFG_INTO_SysML_MM_def toGFGr_def)
                              (rule exI[where x="''E_F_PTypes''"], simp)
                        next
                          assume h8: "v \<noteq> ''F_PTypes''" 
                          then show ?thesis 
                          proof (case_tac "v = ''F_CD''") 
                            assume "v = ''F_CD''"
                            then show ?thesis 
                              by (simp add: GFG_INTO_SysML_MM_def toGFGr_def)
                                (rule exI[where x="''E_F_CD''"], simp)
                          next
                            assume "v \<noteq> ''F_CD''"
                            then show ?thesis 
                              using h1 h2 h3 h4 h5 h6 h7 h8
                              by (simp add: GFG_INTO_SysML_MM_def toGFGr_def)
                          qed
                        qed
                      qed
                    qed
                  qed
                qed
              qed
            qed
          qed
        next
          let ?restrict_G = "restrict (toGFGr GFG_INTO_SysML_MM) 
            (Es (toGFGr GFG_INTO_SysML_MM) - EsId (toGFGr GFG_INTO_SysML_MM))"
          show "acyclicGr (?restrict_G)"
            using h_wf_g by (simp add: acyclicGr_def rel_restrict_eq_consRel0, eval)
        qed
      qed
    qed

definition INTO_SysML_MM :: "Mdl_ls"
where
  "INTO_SysML_MM \<equiv> 
    \<lparr>gfgL = GFG_INTO_SysML_MM,
    frdL = [(''F_Common'', F_Common), (''F_Props'', F_Props), 
      (''F_ASD'', F_ASD), (''F_Blocks'', F_Blocks), 
      (''F_PTypes'', F_PTypes), (''F_VTypes'', F_VTypes), 
      (''F_Comps'', F_Comps), (''F_CD'', F_CD)]\<rparr>"

lemma is_wf_INTO_SysML_MM: "is_wf_mdl_ls INTO_SysML_MM"
  proof -
    have ha: "NsG (gfgL INTO_SysML_MM) = map fst (frdL INTO_SysML_MM)"
      by (simp add: INTO_SysML_MM_def GFG_INTO_SysML_MM_def)
    have hb: "distinct (map fst (frdL INTO_SysML_MM))"
      by (simp add: INTO_SysML_MM_def)
    show ?thesis
    proof (simp add: is_wf_mdl_ls_def, rule conjI)
      show "NsG (gfgL INTO_SysML_MM) = map fst (frdL INTO_SysML_MM)"
        by (rule ha)
    next
      apply_end(rule conjI)
      show "distinct (map fst (frdL INTO_SysML_MM))"
        by (rule hb)
    next
      show "is_wf_mdl (toMdl INTO_SysML_MM)"
      proof (simp add: is_wf_mdl_def, rule conjI)
        apply_end(clarify)
        fix F
        assume "F \<in> ran (frd (toMdl INTO_SysML_MM))"
        then have h1: "F = (toFr F_Common) \<or> F = (toFr F_Props) \<or> F = (toFr F_Comps)
          \<or> F = (toFr F_ASD) \<or> F = (toFr F_Blocks)
          \<or> F = (toFr F_VTypes) \<or> F = (toFr F_PTypes) \<or> F = (toFr F_CD)"
          by (auto simp add: INTO_SysML_MM_def toMdl_def)
        then show "is_wf_fr F"
        proof (case_tac "F = toFr F_Common")
          assume "F = toFr F_Common"
          then show "is_wf_fr F"
            by (simp add: wf_F_Common)
        next
          assume h2: "F \<noteq> toFr F_Common" 
          show "is_wf_fr F"
          proof (case_tac "F = toFr F_Props")
            assume "F = toFr F_Props"
            then show "is_wf_fr F"
              by (simp add: wf_F_Props)
          next
            assume h3: "F \<noteq> toFr F_Props"
            show "is_wf_fr F"
            proof (case_tac "F = toFr F_Comps")
              assume "F = toFr F_Comps"
              then show "is_wf_fr F"
                by (simp add: wf_F_Comps)
            next
              assume h4: "F \<noteq> toFr F_Comps"
              then show "is_wf_fr F"
              proof (case_tac "F = toFr F_ASD")
                assume "F = toFr F_ASD"
                then show "is_wf_fr F"
                  by (simp add: wf_F_ASD)
              next
                assume h5: "F \<noteq> toFr F_ASD"
                then show "is_wf_fr F"
                proof (case_tac "F = toFr F_Blocks")
                  assume "F = toFr F_Blocks"
                  then show "is_wf_fr F"
                    by (simp add: wf_F_Blocks)
                next
                  assume h6: "F \<noteq> toFr F_Blocks"
                  then show "is_wf_fr F"
                  proof (case_tac "F = toFr F_PTypes")
                    assume "F = toFr F_PTypes"
                    then show "is_wf_fr F"
                      by (simp add: wf_F_PTypes)
                  next
                    assume h7: "F \<noteq> toFr F_PTypes"
                    then show "is_wf_fr F"
                    proof (case_tac "F = toFr F_VTypes")
                      assume "F = toFr F_VTypes"
                      then show "is_wf_fr F"
                        by (simp add: wf_F_VTypes)
                    next
                      assume h8: "F \<noteq> toFr F_VTypes"
                      then show "is_wf_fr F"
                      proof (case_tac "F = toFr F_CD")
                        assume "F = toFr F_CD"
                        then show "is_wf_fr F"
                          by (simp add: wf_F_CD)
                      next
                        assume h9: "F \<noteq> toFr F_CD"
                        then show "is_wf_fr F"
                          using h1 h2 h3 h4 h5 h6 h7 h8
                          by simp
                      qed
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed   
    next
      apply_end(rule conjI)
      show "is_wf_gfg_ls (gfg (toMdl INTO_SysML_MM))"
        by (simp add: is_wf_gfg_GFG_INTO_SysML_MM toMdl_def INTO_SysML_MM_def)
    next
      apply_end(rule conjI)
      show "ftotal_on (frd (toMdl INTO_SysML_MM)) (set (NsG (gfg (toMdl INTO_SysML_MM)))) fr_set"
        by (auto simp add: ftotal_on_def INTO_SysML_MM_def fr_set_def is_fr_def toGFGr_def 
          toMdl_def GFG_INTO_SysML_MM_def)
    next
      apply_end(rule conjI)
      show "disjMdlFrs (toMdl INTO_SysML_MM)"
        by (simp add: disjMdlFrs_def INTO_SysML_MM_def disjFs_def disjGsL_def 
          GFG_INTO_SysML_MM_def F_Common_def SG_F_Common_def F_Props_def SG_F_Props_def
          toFr_def toMdl_def toSGr_def F_ASD_def SG_F_ASD_def F_Blocks_def SG_F_Blocks_def F_PTypes_def
          SG_F_PTypes_def F_VTypes_def SG_F_VTypes_def F_Comps_def SG_F_Comps_def
          F_CD_def SG_F_CD_def)
    next
      have "UMdlFs (toMdl INTO_SysML_MM) = toFr (consUMdlFs INTO_SysML_MM)"
        using ha hb 
        UMdlFs_Eq_consUMdlFs[of "INTO_SysML_MM" "gfgL INTO_SysML_MM" "frdL INTO_SysML_MM"] 
        by (simp)
      then show "mUM2GFG (toMdl INTO_SysML_MM) 
        \<in> morphF2GFGr (UMdlFs (toMdl INTO_SysML_MM)) (toGFGr (gfg (toMdl INTO_SysML_MM)))"
      proof (simp)
        show "mUM2GFG (toMdl INTO_SysML_MM)
        \<in> morphF2GFGr (toFr (consUMdlFs INTO_SysML_MM)) (toGFGr (gfg (toMdl INTO_SysML_MM)))"
        by (simp add: mUM2GFG_def)
      qed
    qed
  qed
qed

value "consUMdlFs INTO_SysML_MM"

definition INTO_SysML_MM_T:: "TyMdl_ls"
where
  "INTO_SysML_MM_T \<equiv> 
    \<lparr>gfgt_ls = GFG_INTO_SysML_MM,
    frdt_ls = [(''F_Common'', TF_Common), (''F_Props'', TF_Props), 
      (''F_ASD'', TF_ASD), (''F_Blocks'', TF_Blocks), 
      (''F_PTypes'', TF_PTypes), (''F_VTypes'', TF_VTypes), 
      (''F_Comps'', TF_Comps), (''F_CD'', TF_CD)]\<rparr>"

lemma is_wf_INTO_SysML_MM_T: "is_wf_tmdl (toTyMdl INTO_SysML_MM_T)"
  proof (simp add: is_wf_tmdl_def, rule conjI)
    show "\<forall>TF. TF \<in> ran (frdt (toTyMdl INTO_SysML_MM_T)) \<longrightarrow> is_wf_tfr TF"
      proof (clarify)
      fix TF
      assume "TF \<in> ran (frdt (toTyMdl INTO_SysML_MM_T))"
      then have h1: "TF = (toTFr TF_Common) \<or> TF = (toTFr TF_Props) \<or> TF = (toTFr TF_Comps)
        \<or> TF = (toTFr TF_ASD) \<or> TF = (toTFr TF_Blocks)
        \<or> TF = (toTFr TF_VTypes) \<or> TF = (toTFr TF_PTypes) \<or> TF = (toTFr TF_CD)"
        by (auto simp add: INTO_SysML_MM_T_def toTyMdl_def)
      then show "is_wf_tfr TF"
      proof (case_tac "TF = toTFr TF_Common")
        assume "TF = toTFr TF_Common"
        then show "is_wf_tfr TF"
          by (simp add: wf_TF_Common)
      next
        assume h2: "TF \<noteq> toTFr TF_Common" 
        show "is_wf_tfr TF"
        proof (case_tac "TF = toTFr TF_Props")
          assume "TF = toTFr TF_Props"
          then show "is_wf_tfr TF"
            by (simp add: wf_TF_Props)
        next
          assume h3: "TF \<noteq> toTFr TF_Props"
          show "is_wf_tfr TF"
          proof (case_tac "TF = toTFr TF_Comps")
            assume "TF = toTFr TF_Comps"
            then show "is_wf_tfr TF"
              by (simp add: wf_TF_Comps)
          next
            assume h4: "TF \<noteq> toTFr TF_Comps"
            then show "is_wf_tfr TF"
            proof (case_tac "TF = toTFr TF_ASD")
              assume "TF = toTFr TF_ASD"
              then show "is_wf_tfr TF"
                by (simp add: wf_TF_ASD)
            next
              assume h5: "TF \<noteq> toTFr TF_ASD"
              then show "is_wf_tfr TF"
              proof (case_tac "TF = toTFr TF_Blocks")
                assume "TF = toTFr TF_Blocks"
                then show "is_wf_tfr TF"
                  by (simp add: wf_TF_Blocks)
              next
                assume h6: "TF \<noteq> toTFr TF_Blocks"
                then show "is_wf_tfr TF"
                proof (case_tac "TF = toTFr TF_PTypes")
                  assume "TF = toTFr TF_PTypes"
                  then show "is_wf_tfr TF"
                    by (simp add: wf_TF_PTypes)
                next
                  assume h7: "TF \<noteq> toTFr TF_PTypes"
                  then show "is_wf_tfr TF"
                  proof (case_tac "TF = toTFr TF_VTypes")
                    assume "TF = toTFr TF_VTypes"
                    then show "is_wf_tfr TF"
                      by (simp add: wf_TF_VTypes)
                  next
                    assume h8: "TF \<noteq> toTFr TF_VTypes"
                    then show "is_wf_tfr TF"
                    proof (case_tac "TF = toTFr TF_CD")
                      assume "TF = toTFr TF_CD"
                      then show "is_wf_tfr TF"
                        by (simp add: wf_TF_CD)
                    next
                      assume h9: "TF \<noteq> toTFr TF_CD"
                      then show "is_wf_tfr TF"
                      using h1 h2 h3 h4 h5 h6 h7 h8
                      by (simp)
                    qed
                  qed
               qed
              qed
            qed
          qed
        qed
      qed
    qed    
  next
    apply_end(rule conjI)
    show "ftotal_on (frdt (toTyMdl INTO_SysML_MM_T)) (set (NsG (gfgt (toTyMdl INTO_SysML_MM_T))))
     tfr_set"
     by (simp add: toTyMdl_def INTO_SysML_MM_T_def GFG_INTO_SysML_MM_def tfr_set_def
       ftotal_on_def is_tfr_def)
  next
    apply_end(rule conjI)
    show "disjTyMdlFrs (toTyMdl INTO_SysML_MM_T)"
      by (simp add: INTO_SysML_MM_T_def GFG_INTO_SysML_MM_def toTyMdl_def
        disjTyMdlFrs_def TF_Common_def F_Common_def SG_F_Common_def 
        TF_Props_def F_Props_def SG_F_Props_def toTFr_def TF_ASD_def F_ASD_def SG_F_ASD_def
        TF_Blocks_def F_Blocks_def TF_PTypes_def TF_VTypes_def F_VTypes_def TF_CD_def
        SG_F_VTypes_def F_CD_def SG_F_CD_def TF_Comps_def F_Comps_def SG_F_Comps_def 
        toFr_def toSGr_def disjFs_def disjGsL_def SG_F_Blocks_def F_PTypes_def
        SG_F_PTypes_def)
  next
    show "mUTM2GFG (toTyMdl INTO_SysML_MM_T) 
      \<in> morphF2GFGr (fr (UTyMdlFs (toTyMdl INTO_SysML_MM_T)))
        (toGFGr (gfgt (toTyMdl INTO_SysML_MM_T)))"
        by (simp)
  qed

primrec INTO_SysML_toPDG_Nodes0:: "Morph \<Rightarrow> V list \<Rightarrow> V list"
where
  "INTO_SysML_toPDG_Nodes0 m [] = []"
  | "INTO_SysML_toPDG_Nodes0 m (v#vs) = 
    (if (fV m) v = Some ''Port'' then (v#INTO_SysML_toPDG_Nodes0 m vs) 
    else INTO_SysML_toPDG_Nodes0 m vs)"

fun INTO_SysML_toPDG_Nodes:: "Mdl_ls \<Rightarrow> Morph \<Rightarrow> V list"
where
  "INTO_SysML_toPDG_Nodes M mt = INTO_SysML_toPDG_Nodes0 mt ((NsG o sg_ls) (consUMdlFs M))"

primrec INTO_SysML_toPDG_Edges0:: "Morph \<Rightarrow> E list \<Rightarrow> E list"
where
  "INTO_SysML_toPDG_Edges0 m []  = []"
  | "INTO_SysML_toPDG_Edges0 m (e#es)  = 
    (if (fE m) e = Some ''EPort_Port'' then (e#INTO_SysML_toPDG_Edges0 m es) 
    else INTO_SysML_toPDG_Edges0 m es)"

fun consGlFrNodePair:: "Fr \<Rightarrow> V \<Rightarrow> V \<Rightarrow> Gr_ls"
where
  "consGlFrNodePair F v1 v2 = (let e = ''E_''@v1@''_''@v2 in
        \<lparr>NsG = [v1, v2], 
        EsG = [e], 
        srcG= [(e, v1)],
        tgtG= [(e, v2)]\<rparr>)"

fun removeDupNsGL:: "Gr_ls \<Rightarrow> Gr_ls"
where
  "removeDupNsGL GL = \<lparr>NsG = remdups (NsG GL),
    EsG = EsG GL, srcG = srcG GL, tgtG = tgtG GL \<rparr>"

primrec getTgtPortOfC:: "Morph \<Rightarrow> Fr \<Rightarrow> V \<Rightarrow> E list \<Rightarrow> V option"
where
  "getTgtPortOfC m F v [] = None" |
  "getTgtPortOfC m F v (e#es) = (if (src (sg F) e = Some v \<and> (fE m) e = Some ''EC_tgt'') 
      then tgt (sg F) e else getTgtPortOfC m F v es)"

primrec getSrcPortOfC:: "Morph \<Rightarrow> Fr \<Rightarrow> V \<Rightarrow> E list \<Rightarrow> V option"
where
  "getSrcPortOfC m F v [] = None" |
  "getSrcPortOfC m F v (e#es) = (if (src (sg F) e = Some v \<and> (fE m) e = Some ''EC_src'') 
      then tgt (sg F) e else getSrcPortOfC m F v es)"

primrec INTO_SysML_toPDG_GL_Es:: "Morph \<Rightarrow> Fr \<Rightarrow> V \<Rightarrow> E list \<Rightarrow> V list"
where
  "INTO_SysML_toPDG_GL_Es m F v []  =  []" |
  "INTO_SysML_toPDG_GL_Es m F v (e#es) = 
    (if (src (sg F) e) = Some v \<and> ((fE m) e = Some ''EC_src'' \<or> (fE m) e = Some ''EC_tgt'')
      then ((the (tgt (sg F) e))#INTO_SysML_toPDG_GL_Es m F v es) else INTO_SysML_toPDG_GL_Es m F v es)"

fun buildGrForConnector:: "Morph \<Rightarrow> Fr_ls \<Rightarrow> V \<Rightarrow> Gr_ls"
where
  "buildGrForConnector m FL v = 
    consGlFrNodePair (toFr FL) (the (getSrcPortOfC m (toFr FL) v (EsG (sg_ls FL))))
        (the (getTgtPortOfC m (toFr FL) v (EsG (sg_ls FL))))"

fun getBlockInstanceOfPort:: "Morph \<Rightarrow> Fr_ls \<Rightarrow> V \<Rightarrow>V"
where
  "getBlockInstanceOfPort m FL v = the (src (sg (toFr FL)) (hd (filter (\<lambda> e. tgt (sg (toFr FL)) e = Some v 
      \<and> (fE m) e = Some ''EBIports'') ((EsG o sg_ls) FL))))"

fun getFlowPortTypeOfPort :: "Morph \<Rightarrow>Fr_ls \<Rightarrow> V \<Rightarrow>V"
where
  "getFlowPortTypeOfPort m FL v = the (tgt (sg (toFr FL)) (hd (filter (\<lambda> e. src (sg (toFr FL)) e = Some v 
      \<and> (fE m) e = Some ''EPortType'' 
      \<and> (fV m) (the(tgt (sg (toFr FL)) e)) = Some ''PrFlowPort2'') ((EsG o sg_ls) FL))))"

fun getOtherInternalPorts :: "Morph \<Rightarrow> Fr_ls \<Rightarrow> V \<Rightarrow> V list"
where
  "getOtherInternalPorts m FL v = 
    (let v_bi = getBlockInstanceOfPort m FL v in
      (map the (map (tgt ((sg (toFr FL))))  
        (filter (\<lambda> e. (fE m) e = Some ''EBIports'' 
          \<and> src (sg (toFr FL)) e = Some v_bi \<and> tgt (sg (toFr FL)) e \<noteq> Some v) ((EsG o sg_ls) FL)))))"

fun getDependentPortOfV:: "Morph \<Rightarrow> Fr_ls \<Rightarrow> V \<Rightarrow> V set \<Rightarrow> V"
where
  "getDependentPortOfV m FL v depFPs = 
    the (tgt (sg (toFr FL)) (hd (filter (\<lambda> e. (fE m) e = Some ''EBIports'' 
      \<and> src (sg (toFr FL)) e = Some (getBlockInstanceOfPort m FL v)
      \<and> the (tgt (sg (toFr FL))e) \<in> set (getOtherInternalPorts m FL v)
      \<and> getFlowPortTypeOfPort m FL (the (tgt (sg (toFr FL))e)) \<in> depFPs) ((EsG o sg_ls) FL))))"

primrec consGLFrDepends:: "Morph \<Rightarrow> Fr_ls \<Rightarrow> V \<Rightarrow> E list \<Rightarrow> Gr_ls"
where
  "consGLFrDepends m FL v [] = emptyGL" |
  "consGLFrDepends m FL v (e#es) = (let vdeps = (set (consTgtStF FL)) ``{e} in
    consUG (consGlFrNodePair (toFr FL) 
      (getDependentPortOfV m FL v vdeps) v) (consGLFrDepends m FL v es))"

fun buildGrForInternalPortConnections:: "Morph \<Rightarrow> Fr_ls \<Rightarrow> V \<Rightarrow> V \<Rightarrow> Gr_ls"
where
  "buildGrForInternalPortConnections m FL v p_ty = 
      consGLFrDepends m FL v
          (filter (\<lambda> e. p_ty \<in> (set (consSrcStF FL)) ``{e})
            (filter (\<lambda> e. (fE m) e = Some ''EFlowPortDepends'') (EsG (sg_ls FL))))"

primrec INTO_SysML_toPDG_GL:: "Morph \<Rightarrow> Fr_ls \<Rightarrow> V list \<Rightarrow> Gr_ls"
where
  "INTO_SysML_toPDG_GL m FL []  = emptyGL" |
  "INTO_SysML_toPDG_GL m FL (v#vs)  = 
    (let restL = (INTO_SysML_toPDG_GL m FL vs) in
    (if (fV m) v = Some ''Connector'' 
      then consUG (buildGrForConnector m FL v) restL
      else (if (fV m) v = Some ''Port'' 
        then consUG (buildGrForInternalPortConnections m FL v (getFlowPortTypeOfPort m FL v)) restL
        else restL)))"

(*primrec INTO_SysML_toPDG_GL2:: "MorphTuple \<Rightarrow> Fr_ls \<Rightarrow> V list \<Rightarrow> Gr_ls"
where
  "INTO_SysML_toPDG_GL2 m FL []  = emptyGL" |
  "INTO_SysML_toPDG_GL2 m FL (v#vs)  = 
    (let restL = (INTO_SysML_toPDG_GL2 m FL vs) in
    (if (fV m) v = Some ''Port'' 
        then consUG (buildGrForInternalPortConnections m FL v 
          (filter (\<lambda> e. src (sg (toFr FL)) e = Some v \<and> (fE m) e = Some ''EPortType'')
            (EsG (sg_ls FL)))) restL
        else restL))"*)

fun INTO_SysML_toPDG_Edges:: "Mdl_ls \<Rightarrow> Morph \<Rightarrow> E list"
where
  "INTO_SysML_toPDG_Edges M mt = INTO_SysML_toPDG_Edges0 mt ((EsG o sg_ls) (consUMdlFs M))"

fun INTO_SysML_toPDG:: "MdlTy_ls \<Rightarrow> PDGr"
where
  "INTO_SysML_toPDG MLT = 
    removeDupNsGL(INTO_SysML_toPDG_GL 
      (toMorph (mtyL MLT)) (consUMdlFs (mdlL MLT)) ((NsG o sg_ls) (consUMdlFs (mdlL MLT))))"

end