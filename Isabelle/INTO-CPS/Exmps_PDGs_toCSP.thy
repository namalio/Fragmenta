(********  
  Title:      Theory defining pretty printing of CSP specs used to generate CSP
  Author:     Nuno Amálio
***********)

theory Exmps_PDGs_toCSP
imports "CSP/CSP_Print" Exmp_PDGs_Grs PDG_To_CSP

begin

definition output_dir:: "string"
where
  "output_dir = ''/Users/wv8599/Work/Fragmenta/Isabelle/INTO-CPS/CSP/''"

export_code toCSP expid csp str_int G1 G2 G3 G3b G4a G4b output_dir
  in SML module_name CSP file "CSP/csp.sml"

ML_file "CSP/csp.sml"

ML_file "CSP/wr-csp.sml"

ML {*  
val dir1 = OS.FileSys.getDir();
val dir = charsToStr(output_dir);
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
*}

end