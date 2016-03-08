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

(*Function that retrieves the nodes of a certain metamodel node type*)
fun nodesOfMMTy :: "Fr_ls  \<Rightarrow> Morph \<Rightarrow> V \<Rightarrow> V list"
where
   "nodesOfMMTy FL m vty = [v \<leftarrow>((NsG o sg_ls) FL). (fV m) v = Some vty]"

(*Function that retrieves the edges of a certain metamodel edge type*)
fun edgesOfMMTy :: "Fr_ls \<Rightarrow> Morph \<Rightarrow> E \<Rightarrow>E list"
where
   "edgesOfMMTy FL m e = [e'\<leftarrow>((EsG o sg_ls) FL).  (fE m) e' = Some e]"

fun getTgtPortOfC:: "Morph \<Rightarrow> Fr_ls \<Rightarrow> V \<Rightarrow> V option"
where
  "getTgtPortOfC m FL v  = tgt (sg (toFr FL)) (the (find (\<lambda>e. src (sg (toFr FL)) e = Some v) 
    (edgesOfMMTy FL m ''EC_tgt'')))" 

fun getSrcPortOfC:: "Morph \<Rightarrow> Fr_ls \<Rightarrow> V \<Rightarrow> V option"
where
  "getSrcPortOfC m FL v  = tgt (sg (toFr FL)) (the (find (\<lambda>e. src (sg (toFr FL)) e = Some v) 
    (edgesOfMMTy FL m ''EC_src'')))" 
(*
  "getSrcPortOfC m F v (e#es) = (if (src (sg F) e = Some v \<and> (fE m) e = Some ''EC_src'') 
      then tgt (sg F) e else getSrcPortOfC m F v es)"*)

primrec INTO_SysML_toPDG_GL_Es:: "Morph \<Rightarrow> Fr \<Rightarrow> V \<Rightarrow> E list \<Rightarrow> V list"
where
  "INTO_SysML_toPDG_GL_Es m F v []  =  []" |
  "INTO_SysML_toPDG_GL_Es m F v (e#es) = 
    (if (src (sg F) e) = Some v \<and> ((fE m) e = Some ''EC_src'' \<or> (fE m) e = Some ''EC_tgt'')
      then ((the (tgt (sg F) e))#INTO_SysML_toPDG_GL_Es m F v es) else INTO_SysML_toPDG_GL_Es m F v es)"

(*fun buildGrForConnector:: "Morph \<Rightarrow> Fr_ls \<Rightarrow> V \<Rightarrow> Gr_ls"
where
  "buildGrForConnector m FL v = (if v \<in> set (NodesOfMMTy FL m ''Connector'')
      then consGlFrNodePair (toFr FL) (the (getSrcPortOfC m FL v))
        (the (getTgtPortOfC m FL v))
      else emptyGL)"*)

primrec buildGrForConnectors:: "Morph \<Rightarrow> Fr_ls \<Rightarrow> V list \<Rightarrow> Gr_ls"
where
  "buildGrForConnectors m FL [] = emptyGL" |
  "buildGrForConnectors m FL (v#vs) = 
    consUG (consGlFrNodePair (toFr FL) (the (getSrcPortOfC m FL v))
        (the (getTgtPortOfC m FL v))) (buildGrForConnectors m FL vs)"

(* (if v \<in> set (NodesOfMMTy FL m ''Connector'')
      then consGlFrNodePair (toFr FL) (the (getSrcPortOfC m FL v))
        (the (getTgtPortOfC m FL v))
      else emptyGL)"*)

fun getBlockInstanceOfPort:: "Morph \<Rightarrow> Fr_ls \<Rightarrow> V \<Rightarrow>V"
where
  "getBlockInstanceOfPort m FL v = the (src (sg (toFr FL)) 
    (hd ([e\<leftarrow>((EsG o sg_ls) FL) . tgt (sg (toFr FL)) e = Some v 
      \<and> (fE m) e = Some ''EBIports''])))"

fun getFlowPortTypeOfPort :: "Morph \<Rightarrow>Fr_ls \<Rightarrow> V \<Rightarrow>V"
where
  "getFlowPortTypeOfPort m FL v = the (tgt (sg (toFr FL)) 
    (hd ([e\<leftarrow>((EsG o sg_ls) FL). src (sg (toFr FL)) e = Some v 
      \<and> (fE m) e = Some ''EPortType'' 
      \<and> (fV m) (the(tgt (sg (toFr FL)) e)) = Some ''PrFlowPort2''] )))"

fun getOtherInternalPorts :: "Morph \<Rightarrow> Fr_ls \<Rightarrow> V \<Rightarrow> V list"
where
  "getOtherInternalPorts m FL v = 
    (let v_bi = getBlockInstanceOfPort m FL v in
      (map the (map (tgt ((sg (toFr FL))))  
        [e\<leftarrow> ((EsG o sg_ls) FL). (fE m) e = Some ''EBIports'' 
          \<and> src (sg (toFr FL)) e = Some v_bi \<and> tgt (sg (toFr FL)) e \<noteq> Some v] )))"

fun getDependentPortOfV:: "Morph \<Rightarrow> Fr_ls \<Rightarrow> V \<Rightarrow> V set \<Rightarrow> V"
where
  "getDependentPortOfV m FL v depFPs = 
    the (tgt (sg (toFr FL)) (the (List.find (\<lambda> e. (fE m) e = Some ''EBIports'' 
      \<and> src (sg (toFr FL)) e = Some (getBlockInstanceOfPort m FL v)
      \<and> the (tgt (sg (toFr FL))e) \<in> set (getOtherInternalPorts m FL v)
      \<and> getFlowPortTypeOfPort m FL (the (tgt (sg (toFr FL))e)) \<in> depFPs) ((EsG o sg_ls) FL))))"

primrec consGLFrDepends:: "Morph \<Rightarrow> Fr_ls \<Rightarrow> V \<Rightarrow> E list \<Rightarrow> (E\<times>V) list \<Rightarrow> Gr_ls"
where
  "consGLFrDepends m FL v [] evps = emptyGL" |
  "consGLFrDepends m FL v (e#es) evps = (let vdeps = set(map snd [p\<leftarrow>evps. (fst p) = e ]) in
    consUG (consGlFrNodePair (toFr FL) 
      (getDependentPortOfV m FL v vdeps) v) (consGLFrDepends m FL v es evps))"

fun buildGrForInternalPortConnections:: "Morph \<Rightarrow> Fr_ls \<Rightarrow> V \<Rightarrow> Gr_ls"
where
  "buildGrForInternalPortConnections m FL v = 
      consGLFrDepends m FL v
          (map fst ([p\<leftarrow>consSrcStF FL. (fst p) \<in> set (edgesOfMMTy FL m ''EFlowPortDepends'')
          \<and> (snd p) = (getFlowPortTypeOfPort m FL v)])) (consTgtStF FL)"

primrec buildGrForPort:: "Morph \<Rightarrow> Fr_ls \<Rightarrow> V list \<Rightarrow> (E\<times>V) list \<Rightarrow> (E\<times>V) list \<Rightarrow> Gr_ls" 
where
  "buildGrForPort m FL [] evpsSrc evpsTgt = emptyGL" |
  "buildGrForPort m FL (v#vs) evpsSrc evpsTgt = 
    consUG (consGLFrDepends m FL v 
      (map fst ([p\<leftarrow>evpsSrc. (snd p) = (getFlowPortTypeOfPort m FL v)])) evpsTgt)
      (buildGrForPort m FL vs evpsSrc evpsTgt)"

fun buildGrForInternalDependenciesOfPorts:: "Morph \<Rightarrow> Fr_ls \<Rightarrow> Gr_ls" 
where
  "buildGrForInternalDependenciesOfPorts m FL = 
    buildGrForPort m FL (nodesOfMMTy FL m ''Port'') 
      ([p\<leftarrow>consSrcStF FL. (fst p) \<in> set (edgesOfMMTy FL m ''EFlowPortDepends'')])
      ([p\<leftarrow>consTgtStF FL. (fst p) \<in> set (edgesOfMMTy FL m ''EFlowPortDepends'')])"

(*primrec INTO_SysML_toPDG_GL_old:: "Morph \<Rightarrow> Fr_ls \<Rightarrow> V list \<Rightarrow> Gr_ls"
where
  "INTO_SysML_toPDG_GL_old m FL []  = emptyGL" |
  "INTO_SysML_toPDG_GL_old m FL (v#vs)  = 
    (if (fV m) v = Some ''Connector'' 
      then consUG (buildGrForConnector m FL v) (INTO_SysML_toPDG_GL m FL vs)
      else (if (fV m) v = Some ''Port'' 
        then consUG (buildGrForInternalPortConnections m FL v) (INTO_SysML_toPDG_GL m FL vs)
        else INTO_SysML_toPDG_GL_old m FL vs))"*)

fun INTO_SysML_toPDG_GL:: "Morph \<Rightarrow> Fr_ls \<Rightarrow> Gr_ls"
where
  "INTO_SysML_toPDG_GL m FL = consUG 
    (buildGrForConnectors m FL (nodesOfMMTy FL m ''Connector''))
    (buildGrForInternalDependenciesOfPorts m FL)" 

(*|
  "INTO_SysML_toPDG_GL3 m FL (v#vs)  = 
    (if (fV m) v = Some ''Connector'' 
      then consUG (buildGrForConnector m FL v) (INTO_SysML_toPDG_GL m FL vs)
        else INTO_SysML_toPDG_GL m FL vs)"*)

fun INTO_SysML_toPDG_Edges:: "Mdl_ls \<Rightarrow> Morph \<Rightarrow> E list"
where
  "INTO_SysML_toPDG_Edges M mt = INTO_SysML_toPDG_Edges0 mt ((EsG o sg_ls) (consUMdlFs M))"

fun INTO_SysML_toPDG:: "MdlTy_ls \<Rightarrow> PDGr"
where
  "INTO_SysML_toPDG MLT = INTO_SysML_toPDG_GL (toMorph (mtyL MLT)) 
    (consUMdlFs (mdlL MLT))"


end