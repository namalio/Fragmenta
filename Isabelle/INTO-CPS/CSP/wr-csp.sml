
open CSP;
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
|  wrExp_ (GtExp  (ne1, ne2)) ind =
   wrExp_ ne1 ind ^ " > " ^ wrExp_ ne2 ind
|  wrExp_ (GtEqExp  (ne1, ne2)) ind =
    wrExp_ ne1 ind ^ " >= " ^ wrExp_ ne2 ind
|  wrExp_ (LtExp  (ne1, ne2)) ind =
    wrExp_ ne1 ind ^ " < " ^ wrExp_ ne2 ind
|  wrExp_ (LtEqExp  (ne1, ne2)) ind =
    wrExp_ ne1 ind ^ " <= " ^ wrExp_ ne2 ind
| wrExp_ (Srange (ne1, ne2)) ind =
    "{" ^ wrExp_ ne1 ind ^ ".." ^ wrExp_ ne2 ind ^"}"
| wrExp_ (Ext exps) ind =
    "{"^ wrExps_ exps ind ^ "}"
| wrExp_ (Prfx (e1, e2)) ind =
    wrExp_ e1 ind ^ " -> "^ wrExp_ e2 ind
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
| wrExp_ (ExtChoice (e1, e2)) ind = wrExp_ e1 ind ^" [] "^wrExp_ e2 ind
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

fun wrCSP_ (Csp ds) = wrDecls_ ds "";
