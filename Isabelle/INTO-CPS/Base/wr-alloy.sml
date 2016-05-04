
open CSP_Alloy;

val ind_unit = "   ";

(*Code prints to enable the translation into Alloy*)
fun wrStrsWithSep [] sep = ""
  | wrStrsWithSep (s::ss) sep =
  (if null ss then s else s^sep^" "^wrStrsWithSep ss sep)

fun charsToStr [] = ""
  | charsToStr (c::cs) = (str c)^charsToStr cs

fun charslsToStrs [] = []
  | charslsToStrs (cs::lcs) = (charsToStr cs)::(charslsToStrs lcs)

fun wrAlloyIds ids = wrStrsWithSep ids ","

fun wrSigTy (Sabstract) = "abstract "
  | wrSigTy (Snormal) = ""

fun wrMult (Mlone) = "lone"
  | wrMult (Mone) = "one"
  | wrMult (Msome) = "some"

fun wrMultOption (NONE) = ""
  | wrMultOption (SOME m) = wrMult(m)

fun wrAExp (AExpid aid ) = charsToStr aid
  | wrAExp (AExpset e) = "set "^wrAExp (e)
  | wrAExp (AExpTrcl e) = "^"^wrAExp (e)
  | wrAExp (AExpno e) = "no "^wrAExp (e)
  | wrAExp (AExpthis) = "this"
  | wrAExp (AExpIdn) = "iden"
  | wrAExp (AExpnone) = "none"
  | wrAExp (AExpeq (e1, e2)) = wrAExp (e1)^" = "^wrAExp (e2)
  | wrAExp (AExpneq (e1, e2)) = wrAExp (e1)^" != "^wrAExp (e2)
  | wrAExp (AExpDot (e1, e2)) = wrAExp (e1)^"."^wrAExp (e2)
  | wrAExp (AExpPlus (e1, e2)) = wrAExp (e1)^" + "^wrAExp (e2)
  | wrAExp (AExpAnd (e1, e2)) = wrAExp (e1)^" & "^wrAExp (e2)

fun wrDeclExp (Dset(m, e)) = (wrMultOption m)^" " ^(wrAExp e)

fun wrDecl (Dc (lids, de)) = (wrAlloyIds (charslsToStrs lids))^" : "^(wrDeclExp de)

fun wrDecls [] ind = ""
  | wrDecls (d::ds) ind = ind^(wrDecl d)^"\n"^(wrDecls ds ind)

fun wrAExps [] ind = ""
  | wrAExps (e::es) ind = ind^(wrAExp e)^"\n"^(wrAExps es ind)

fun wrSigCnts (es) = (if null es then "" else "{\n"^(wrAExps es ind_unit)^"}")

fun wrSigExtends (NONE) = ""
  | wrSigExtends (SOME aid) = " extends "^charsToStr(aid)^" "

fun wrSigDecl (Sig (sty, m, aids, oext_id, ds, es)) =
  (wrSigTy sty)^wrMultOption(m)^" sig "
    ^ wrAlloyIds (charslsToStrs aids)^wrSigExtends(oext_id)
  ^" {\n" ^(wrDecls ds ind_unit)^"}"^(wrSigCnts es)

fun wrFactDecl (Fact (aid, es)) =
  "fact "^charsToStr(aid)^"{\n"^(wrAExps es ind_unit)^"}"

fun wrAssertDecl (Assert (aid, es)) =
  "assert "^charsToStr(aid)^" {\n"^(wrAExps es ind_unit)^"}"

fun wrCheckDecl (Check (aid, n)) =
  "check "^charsToStr(aid)^" for "^charsToStr(str_nat n)

fun wrParagraph (Psig p) = wrSigDecl (p)
  | wrParagraph (Pfact p) = wrFactDecl (p)
  | wrParagraph (Passert p) = wrAssertDecl (p)
  | wrParagraph (Pcheck p) = wrCheckDecl (p)

fun wrParagraphs ps = wrStrsWithSep (map wrParagraph ps) "\n\n"

fun wrAlloyModule (Amodule (aid, aps)) =
  "module " ^charsToStr(aid)^"\n\n"^(wrParagraphs aps)
