(*  Theory: 'INTO_SysML_ToPDG'
    Description:  Contains functions that build PDGs out of INTO-SysML models
    Author:     Nuno Amálio
*)

theory INTO_SysML_ToPDG
imports INTO_SysML_MM_Gbl
  
begin

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
  "buildGrForConnector m FL v = (if v \<in> Ns (sg (toFr FL))
      then consGlFrNodePair (toFr FL) (the (getSrcPortOfC m (toFr FL) v (EsG (sg_ls FL))))
        (the (getTgtPortOfC m (toFr FL) v (EsG (sg_ls FL))))
      else emptyGL)"

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

fun buildGrForInternalPortConnections:: "Morph \<Rightarrow> Fr_ls \<Rightarrow> V \<Rightarrow> Gr_ls"
where
  "buildGrForInternalPortConnections m FL v = 
      consGLFrDepends m FL v
          (filter (\<lambda> e. (getFlowPortTypeOfPort m FL v) \<in> (set (consSrcStF FL)) ``{e})
            (filter (\<lambda> e. (fE m) e = Some ''EFlowPortDepends'') (EsG (sg_ls FL))))"

primrec INTO_SysML_toPDG_GL:: "Morph \<Rightarrow> Fr_ls \<Rightarrow> V list \<Rightarrow> Gr_ls"
where
  "INTO_SysML_toPDG_GL m FL []  = emptyGL" |
  "INTO_SysML_toPDG_GL m FL (v#vs)  = 
    (let restL = (INTO_SysML_toPDG_GL m FL vs) in
    (if (fV m) v = Some ''Connector'' 
      then consUG (buildGrForConnector m FL v) restL
      else (if (fV m) v = Some ''Port'' 
        then consUG (buildGrForInternalPortConnections m FL v) restL
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