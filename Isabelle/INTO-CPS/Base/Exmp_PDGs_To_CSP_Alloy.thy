(********  
  Theory: 'Exmp_PDGs_To_CSP_Alloy'
  Description:  Theory that generates PDGs for both CSP and Alloy
  Author:     Nuno Amálio
***********)

theory Exmp_PDGs_To_CSP_Alloy
imports CSP_Print Exmp_PDGs_Grs PDG_To_CSP PDG_To_Alloy

begin

definition output_dir:: "string"
where
  "output_dir = ''/Users/wv8599/Work/Fragmenta/Isabelle/INTO-CPS/Generated/''"

export_code toCSP CSP_ast.expid Alloy_ast.AExpid Alloy_ast.dset Alloy_ast.dc Alloy_ast.sig 
  Alloy_ast.fact Alloy_ast.assert Alloy_ast.check Alloy_ast.psig Alloy_ast.amodule Alloy_ast.snormal 
  Alloy_ast.mone toAlloy csp str_int str_nat G1 G2 G3 G3b G4a G4b PDG_WT1
  output_dir in SML module_name CSP_Alloy file "csp-alloy.sml"

ML_file "csp-alloy.sml"

ML_file "wr-csp.sml"

ML_file "wr-alloy.sml"

ML {*
open CSP_Alloy;

(*val dir1 = OS.FileSys.getDir();*)
val dir = charsToStr(output_dir);
val file_csp = TextIO.openOut(dir^"G1.csp");
  TextIO.output (file_csp, wrCSP_ (toCSP g1));
  TextIO.closeOut(file_csp);

val file_alloy = TextIO.openOut(dir^"G1.als");
  TextIO.output (file_alloy, wrAlloyModule (toAlloy g1));
  TextIO.closeOut(file_alloy);

val file_csp = TextIO.openOut(dir^"G2.csp");
  TextIO.output (file_csp, wrCSP_ (toCSP g2));
  TextIO.closeOut(file_csp);

val file_alloy = TextIO.openOut(dir^"G2.als");
  TextIO.output (file_alloy, wrAlloyModule (toAlloy g2));
  TextIO.closeOut(file_alloy);

val file_csp = TextIO.openOut(dir^"G3.csp");
  TextIO.output (file_csp, wrCSP_ (toCSP g3));
  TextIO.closeOut(file_csp );

val file_alloy = TextIO.openOut(dir^"G3.als");
  TextIO.output (file_alloy , wrAlloyModule (toAlloy g3));
  TextIO.closeOut(file_alloy );

val file_csp = TextIO.openOut(dir^"G3b.csp");
  TextIO.output (file_csp, wrCSP_ (toCSP g3b));
  TextIO.closeOut(file_csp);

val file_alloy = TextIO.openOut(dir^"G3b.als");
  TextIO.output (file_alloy , wrAlloyModule (toAlloy g3b));
  TextIO.closeOut(file_alloy );

val file_csp = TextIO.openOut(dir^"G4a.csp");
  TextIO.output (file_csp, wrCSP_ (toCSP g4a));
  TextIO.closeOut(file_csp);

val file_alloy = TextIO.openOut(dir^"G4a.als");
  TextIO.output (file_alloy , wrAlloyModule (toAlloy g4a));
  TextIO.closeOut(file_alloy );

val file_csp = TextIO.openOut(dir^"G4b.csp");
  TextIO.output (file_csp, wrCSP_ (toCSP g4b));
  TextIO.closeOut(file_csp);

val file_alloy = TextIO.openOut(dir^"G4b.als");
  TextIO.output (file_alloy , wrAlloyModule (toAlloy g4b));
  TextIO.closeOut(file_alloy );

val file_csp = TextIO.openOut(dir^"PDG_WT1.csp");
  TextIO.output (file_csp, wrCSP_ (toCSP pDG_WT1));
  TextIO.closeOut(file_csp);

val file_alloy = TextIO.openOut(dir^"PDG_WT1.als");
  TextIO.output (file_alloy , wrAlloyModule (toAlloy pDG_WT1));
  TextIO.closeOut(file_alloy );
*}

end