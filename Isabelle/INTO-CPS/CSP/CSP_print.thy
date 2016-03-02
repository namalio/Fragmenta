
(********  
  Title:      Pretty printing of CSP specs used to generate CSP
  Author:     Nuno Amálio
***********)

theory CSP_print
imports Main CSP_ast "~~/src/HOL/Library/Code_Char" 

begin

code_printing 
  type_constructor String.literal \<rightharpoonup>  
    (SML) "string"

primrec wrStrsWithSep :: "string list \<Rightarrow> string \<Rightarrow> string"
where 
  "wrStrsWithSep [] sep = ''''"
  | "wrStrsWithSep (s#ss) sep = (if ss=[] then s else s@sep@'' ''@wrStrsWithSep ss sep)"

(*Tests the function above*)
value "wrStrsWithSep [''a'', ''b''] '',''"

primrec wrDecl :: "Decl \<Rightarrow> string"
  and wrStmt :: "Stmt \<Rightarrow> string"
  and wrExp :: "Exp \<Rightarrow> string"
  and wrExps :: "Exp list \<Rightarrow> string"
  and wrDecls :: "Decl list \<Rightarrow> string"
where
  "wrDecl (channel nms) = ''channel ''@(wrStrsWithSep nms '','')"
  | "wrDecl (e1 \<triangleq> e2) = (wrExp e1)@'' = ''@(wrExp e2)"
  | "wrDecl (e1 \<sqsubseteq> e2) = ''assert ''@(wrExp e1)@'' [T= ''@(wrExp e2)"
  | "wrStmt (stmt nm e) = nm@'' : ''@(wrExp e)"
  | "wrExp (expid nm) = nm"
  | "wrExp (e1 \<lparr>\<rparr> es) = (wrExp e1)@''(''@(wrExps es)@'')''"
  | "wrExp (exppar e) = ''(''@(wrExp e)@'')''"
  | "wrExp (num n) = (str_int n)"
  | "wrExp (ne1 |+| ne2) = (wrExp ne1)@''+''@(wrExp ne2)"
  | "wrExp (ne1 |-| ne2) = (wrExp ne1)@''-''@(wrExp ne2)"
  | "wrExp (ne1 |>| ne2) = (wrExp ne1)@'' > ''@(wrExp ne2)"
  | "wrExp (ne1 |\<ge>| ne2) = (wrExp ne1)@'' >= ''@(wrExp ne2)"
  | "wrExp (ne1 |<| ne2) = (wrExp ne1)@'' < ''@(wrExp ne2)"
  | "wrExp (ne1 |\<le>| ne2) = (wrExp ne1)@'' <= ''@(wrExp ne2)"
  | "wrExp (ne1 .. ne2) = ''{''@ (wrExp ne1) @ ''..'' @ (wrExp ne2) @ ''}''"
  | "wrExp (ext exps) = ''{'' @  (wrExps exps) @ ''}''"
  | "wrExp (e1 \<longrightarrow> e2) = (wrExp e1)@'' -> ''@(wrExp e2)"
  | "wrExp (STOP) = ''STOP''"
  | "wrExp (SKIP) = ''SKIP''"
  | "wrExp (let_within ds e) = ''let \<newline>''@wrDecls(ds)@''\<newline> within ''@(wrExp e)"
  | "wrExp (if_then_else e1 e2 e3) = 
      ''if ''@(wrExp e1)@''\<newline> then ''@(wrExp e2)@''\<newline> else ''@(wrExp e3)"
  | "wrExp (e1 |;| e2) = (wrExp e1)@'';''@(wrExp e2)"
  | "wrExp (parallel e1 e2 a) = (wrExp e1)@''[|''@(wrExps a )@''|]''@(wrExp e2)"
  | "wrExp (e1 \<sqinter> e2) = (wrExp e1)@'' |~| ''@(wrExp e2)"
  | "wrExp (e1 \<box> e2) = (wrExp e1)@'' [] ''@(wrExp e2)"
  | "wrExp (e1 \<parallel>| e2) = (wrExp e1)@'' ||| ''@(wrExp e2)"
  | "wrExp (\<box> s e) = ''[] ''@(wrStmt s)@'' @ ''@(wrExp e)"
  | "wrExps [] = []"
  | "wrExps (e#es) = (if es = [] then (wrExp e) else (wrExp e)@'', ''@(wrExps es))"
  | "wrDecls [] = []"
  | "wrDecls (d#ds) = (if ds = [] then (wrDecl d) else (wrDecl d)@''\<newline>''@(wrDecls ds))"

primrec wrCSP :: "CSPSpec \<Rightarrow> string"
where
  "wrCSP (csp ds) = wrDecls (ds)"

(*Tests with numerical expressions*)
value "wrExp ((num 2) |+| (num 2))"
value "wrExp ((num 2) |-| (num 2))"

(*Tests set expressions*)
value "wrExp ((num 2)..(num 3))"
value "wrExp (ext [(num 1), (num 2), (num 3)])"

(*primrec toSetExt0 :: "string list \<Rightarrow> Exp list"
where
  "toSetExt0 ([]) = []"
  | "toSetExt0 (s#l) = (expid s)#(toSetExt0 l)"*)

definition toSetExt :: "string list \<Rightarrow> Exp"
where
  "toSetExt l = (ext (map expid l))"

(*ML {*   
  (*open CSP;
  val ind_unit = "   ";
  fun maybe_nl ind = (if ind="" then "\n" else "")
  (*Code prints to enable the translation into CSPm*)
  fun wrStrsWithSep_ [] sep = ""
  | wrStrsWithSep_ (s::ss) sep = (if null ss then s else s^sep^" "^wrStrsWithSep_ ss sep)
  fun charsToStr [] = ""
    | charsToStr (c::cs) = str c^charsToStr cs
  fun charslsToStrs [] = []
    | charslsToStrs (cs::lcs) = (charsToStr cs)::(charslsToStrs lcs)
  fun wrDecls_ [] ind = ""
  | wrDecls_ (d :: ds) ind = 
    (if null ds then wrDecl_ d ind
      else (wrDecl_ d ind)^"\n"^ind^wrDecls_ ds ind)
  and wrExp_ (Expid nm) ind = charsToStr nm
  | wrExp_ (Expapp (e1, es)) ind =
    wrExp_ e1 ind ^ "("  ^ (wrExps_ es ind) ^ ")"
  | wrExp_ (Exppar e) ind = "(" ^ wrExp_ e ind^ ")"
  | wrExp_ (Num n) ind = charsToStr (str_int n)
  | wrExp_ (PlusExp (ne1, ne2)) ind =
    wrExp_ ne1 ind ^ "+" ^ wrExp_ ne2 ind
  | wrExp_ (MinusExp (ne1, ne2)) ind =
    wrExp_ ne1 ind ^ "-" ^ wrExp_ ne2 ind
  | wrExp_ (Srange (ne1, ne2)) ind =
      "{" ^ wrExp_ ne1 ind ^ ".." ^ wrExp_ ne2 ind ^"}"
  | wrExp_ (Ext exps) ind =
      "{"^ wrExps_ exps ind ^ "}"
  | wrExp_ (Prfx (e1, e2)) ind =
      wrExp_ e1 ind ^ "->"^ wrExp_ e2 ind
  | wrExp_ STOP ind = "STOP"
  | wrExp_ SKIP ind = "SKIP"
  | wrExp_ (Let_within (ds, e)) ind =
    let val ind_let = ind^ind_unit^ind_unit 
    in
    "\n"^ind^ind_unit^"let\n"^ind_let
      ^wrDecls_ ds ind_let
      ^"\n"^ind^ind_unit^"within\n"^ind_let^(wrExp_ e ind_let)
    end
  | wrExp_ (If_then_else (e1, e2, e3)) ind =
    let val ind_pre = ind^ind_unit
      val ind_post = ind_pre^ind_unit
    in
    "\n"^ind_pre^"if "
      ^wrExp_ e1 ind_pre^ "\n"^ind_post
      ^"then "^wrExp_ e2 ind_post^"\n"^ind_post^"else "^wrExp_ e3 ind_post
    end
  | wrExp_ (SeqComp (e1, e2)) ind = ind^wrExp_ e1 ind ^";"^wrExp_ e2 ind
  | wrExp_ (Parallel (e1, e2, a)) ind =
    wrExp_ e1 ind^"[|"^wrExps_ a ind^"|]"^wrExp_ e2 ind
  | wrExp_ (IntChoice (e1, e2)) ind = wrExp_ e1 ind ^" |~| "^wrExp_ e2 ind
  | wrExp_ (Interleave (e1, e2)) ind = wrExp_ e1 ind ^" ||| "^wrExp_ e2 ind
  | wrExp_ (RepExtChoice (s, e)) ind = "[] " ^ wrStmt_ s ^ " @ "^wrExp_ e ind
and wrDecl_ (Channel nms) ind = 
  (maybe_nl ind)^"channel "^wrStrsWithSep_ (charslsToStrs nms) ","
  | wrDecl_ (Eqdecl (e1, e2)) ind = 
    (maybe_nl ind)^wrExp_ e1 ind ^" = "^wrExp_ e2 ind
  | wrDecl_ (Assert (e1, e2)) ind = 
    (maybe_nl ind)^"assert "^wrExp_ e1 ind^" [T= "^wrExp_ e2 ind
and wrExps_ [] ind = ""
  | wrExps_ (e :: es) ind =
    (if null es then wrExp_ e ind
      else wrExp_ e ind ^", "^ wrExps_ es ind)
and wrStmt_ (Stmt (nm, e)) = (charsToStr nm)^" : "^wrExp_ e "";

fun wrCSP_ (Csp ds) = wrDecls_ ds "";*)

val dir = OS.FileSys.getDir()^"/Work/UoYWorkGit/Models/CSP/FMI_loops/";
val file = TextIO.openOut(dir^"G1.csp");
  TextIO.output (file, wrCSP_ (toCSP g1));
  TextIO.closeOut(file);

val file = TextIO.openOut(dir^"G2.csp");
  TextIO.output (file, wrCSP_ (toCSP g2));
  TextIO.closeOut(file);

val file = TextIO.openOut(dir^"G3.csp");
  TextIO.output (file, wrCSP_ (toCSP g3));
  TextIO.closeOut(file);

val file = TextIO.openOut(dir^"G3b.csp");
  TextIO.output (file, wrCSP_ (toCSP g3b));
  TextIO.closeOut(file);

val file = TextIO.openOut(dir^"G4a.csp");
  TextIO.output (file, wrCSP_ (toCSP g4a));
  TextIO.closeOut(file);

val file = TextIO.openOut(dir^"G4b.csp");
  TextIO.output (file, wrCSP_ (toCSP g4b));
  TextIO.closeOut(file);
*}*)

end