(********  
  Theory: 'PDG_To_CSP '
  Description:  Theory to converts PDGs to CSP
  Author:     Nuno Amálio
***********)

theory PDG_To_CSP 
imports CSP_Print PDGs

begin

abbreviation acyclic_exp :: Exp
where
  "acyclic_exp \<equiv> (if_then_else 
  ((expid ''empty'') \<lparr>\<rparr> [(expid ''E'')]) 
  SKIP 
  (repExtChoice (stmt ''e'' (expid ''E'')) ((expid ''e'') \<longrightarrow> 
    (exppar(((expid ''Acyclic'') \<lparr>\<rparr>
      [(expid ''diff'') \<lparr>\<rparr> [(expid ''E''), (ext [expid ''e''])]])
      \<sqinter> SKIP)))))"

abbreviation limited_exp :: Exp
where
  "limited_exp \<equiv> (if_then_else 
  (expid ''n'' |>| num 0) 
  (repExtChoice (stmt ''e'' (expid ''E'')) ((expid ''e'') \<longrightarrow> 
    (exppar(((expid ''Limited0'') \<lparr>\<rparr>
      [(expid ''E''), (expid ''n'' |-|(num 1))])
      \<sqinter> SKIP)))) 
  STOP)"

abbreviation acyclic_Pr :: Decl
where
  "acyclic_Pr \<equiv> ((expid ''AcyclicNetwork'') \<lparr>\<rparr> [(expid ''edges'')]) \<triangleq> 
    (let_within [(((expid ''Acyclic'') \<lparr>\<rparr> [expid ''E'']) \<triangleq> acyclic_exp)] ((expid  ''Acyclic'') \<lparr>\<rparr> [expid ''edges'']))"  

abbreviation assert_acyclic_Decl :: Decl
where
  "assert_acyclic_Decl \<equiv> ((expid ''AcyclicNetwork'') \<lparr>\<rparr>  [(expid ''edges'')]) 
    \<sqsubseteq> (expid ''PortDependancyGraph'')"

definition limited_Pr :: "nat \<Rightarrow> Decl"
where
  "limited_Pr n \<equiv> (expid ''Limited'') \<triangleq> 
    (let_within [(((expid ''Limited0'') \<lparr>\<rparr> [expid ''E'', expid ''n'']) \<triangleq> limited_exp)] ((expid  ''Limited0'') \<lparr>\<rparr> [expid ''edges'', num (int n)]))"  

abbreviation assert_limited_Decl :: Decl
where
  "assert_limited_Decl \<equiv> (expid ''Limited'') 
    \<sqsubseteq> (expid ''PortDependancyGraph'')"

value "wrExp acyclic_exp"
value "wrDecl acyclic_Pr"
value "wrDecl assert_acyclic_Decl"
value "wrExp limited_exp"
value "wrDecl (limited_Pr 5)"

value "wrCSP (csp [acyclic_Pr, assert_acyclic_Decl])"

(*Tests with declarations*)
value "wrDecl (channel [''e1'', ''e2'', ''e3'', ''e4'', ''e5'', ''e6''])"

value "wrDecl ((expid ''edges'') \<triangleq> (ext [(expid ''e1''), (expid ''e2''), 
  (expid ''e3''), (expid ''e4''), (expid ''e5''), (expid ''e6'')]))"


definition toCSP_of_PDG_edges :: "PDGr \<Rightarrow> Decl list"
where
  "toCSP_of_PDG_edges PDG \<equiv> 
    (let es = EsG PDG in
      [channel es, 
      (expid ''edges'') \<triangleq> toSetExt es])"

(* Takes string corresponding to edge and the natural number corresponding to the
successor node and returns the expression *)
definition buildCSPExpOfEdge :: "E \<Rightarrow>nat option\<Rightarrow> Exp"
where
  "buildCSPExpOfEdge e i \<equiv> prfx (expid e) 
    (if i = None 
      then SKIP
      else ((expid ''P'') \<lparr>\<rparr> [(num (int (the i) +1))]))"

primrec buildCSPExpOfEdges :: "E list \<Rightarrow>PDGr\<Rightarrow> Exp"
where
  "buildCSPExpOfEdges [] PDG = SKIP"
  | "buildCSPExpOfEdges (e#es) PDG = 
    (let f_idx_tgt = (map_of (enum(nonOutNodes PDG))) \<circ>\<^sub>m map_of((tgtG PDG)) in
      (let exp = buildCSPExpOfEdge e (f_idx_tgt e) in
        (if es = [] then exp else (exp \<box> (buildCSPExpOfEdges es PDG)))))"

definition toCSP_of_PDG_Graph_NPrdecl :: "(V \<times> nat) \<Rightarrow> PDGr \<Rightarrow> Decl"
where
  "toCSP_of_PDG_Graph_NPrdecl vp PDG \<equiv> 
    (let es_inc_src = incidentEsSrc_ls PDG (fst vp) in
    (((expid ''P'') \<lparr>\<rparr> [(num (int (snd vp + 1)))])\<triangleq> (buildCSPExpOfEdges es_inc_src PDG)))"

primrec toCSP_of_PDG_Graph_decls::"(V \<times> nat) list \<Rightarrow> PDGr \<Rightarrow> Decl list"
where
  "toCSP_of_PDG_Graph_decls [] PDG = []"
  | "toCSP_of_PDG_Graph_decls (v#vs) PDG = 
    (toCSP_of_PDG_Graph_NPrdecl v PDG)#toCSP_of_PDG_Graph_decls vs PDG"

(*definition toCSP_of_PDG_Graph_decls::"PDGr => Decl list"
where
  "toCSP_of_PDG_Graph_decls PDG \<equiv> 
    (let ns = enum(NsG PDG) in
      toCSP_of_PDG_Graph_decls0 ns PDG)"*)

definition toCSP_of_PDG_Graph_def::"PDGr => Exp"
where
  "toCSP_of_PDG_Graph_def PDG \<equiv> 
    (let ns = enum(nonOutNodes PDG) in
      let_within 
      (toCSP_of_PDG_Graph_decls ns PDG) 
      (\<box> (stmt ''i'' ((num 1) .. (num (int(length ns))))) (expid ''P'' \<lparr>\<rparr> [(expid ''i'')])))"

definition toCSP_of_PDG :: "PDGr => Decl"
where
  "toCSP_of_PDG PDG \<equiv> (expid ''PortDependancyGraph'') \<triangleq> (toCSP_of_PDG_Graph_def PDG)"

definition toCSP :: "PDGr \<Rightarrow> CSPSpec"
where
  "toCSP PDG \<equiv> csp ((toCSP_of_PDG_edges PDG)@[(limited_Pr (length (EsG PDG))), 
    toCSP_of_PDG PDG, assert_limited_Decl])"

(*definition buildCSPExpOfEdges :: "string list \<Rightarrow> PDGr \<Rightarrow> Exp"
where
  "buildCSPExpOfEdges"

(* Takes natural number corresponding to node and the list of 
incident edges of the node and returns the expression*)
definition buildCSPPrOfNode :: "nat\<Rightarrow>string list\<Rightarrow> PDGr \<Rightarrow> Decl"
where
  "buildCSPPrOfNode i es \<equiv> (((expid ''P'') \<lparr>\<rparr> [(num (int i))])\<triangleq> SKIP)"*)

(*definition buildCSPrOfNode :: "nat\<Rightarrow>PDGr\<Rightarrow> Decl"
where
  "buildCSPrOfNode i PDG \<equiv> 

    (let v = (nth (NsG PDG)  i) in 
    (let esS = incidentEsSrc (toGr PDG) v in 
      ((expid ''P'') \<lparr>\<rparr> [(num (int i))])\<triangleq> SKIP))"*)

(*ML {*
   open Example;
  fun ls_charsToStr [] = ""
    | ls_charsToStr (c::cs) = str c^ls_charsToStr cs
  val file = TextIO.openOut("test.txt");
  TextIO.output (file, ls_charsToStr (wrCSP (toCSP g1)));
*}*)


end