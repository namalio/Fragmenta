(********  
  Theory: 'Exmp_PDGs_To_CSP_Alloy'
  Description:  Theory that converts the example PDGs to both CSP and Alloy
  Author:     Nuno Amálio
***********)

theory Exmp_PDGs_To_CSP_Alloy
imports "CSP_Print" Exmp_PDGs_Grs PDG_To_CSP PDG_To_Alloy

begin

definition CSP_output_dir:: "string"
where
  "CSP_output_dir = ''/Users/wv8599/Work/Fragmenta/Isabelle/INTO-CPS/CSP/''"

definition Alloy_output_dir:: "string"
where
  "Alloy_output_dir = ''/Users/wv8599/Work/Fragmenta/Isabelle/INTO-CPS/Alloy/''"

export_code toCSP CSP_ast.expid Alloy_ast.AExpid Alloy_ast.dset Alloy_ast.dc Alloy_ast.sig 
  Alloy_ast.fact Alloy_ast.assert Alloy_ast.check Alloy_ast.psig Alloy_ast.amodule Alloy_ast.snormal 
  Alloy_ast.mone toAlloy csp str_int str_nat G1 G2 G3 G3b G4a G4b 
  CSP_output_dir Alloy_output_dir
  in SML module_name CSP_Alloy file "csp-alloy.sml"

ML_file "csp-alloy.sml"

ML_file "wr-csp.sml"

ML_file "wr-alloy.sml"

ML {*
open CSP_Alloy;

(*val dir1 = OS.FileSys.getDir();*)
val dir_csp = charsToStr(cSP_output_dir);
val dir_alloy = charsToStr(alloy_output_dir);
val file_csp = TextIO.openOut(dir_csp^"G1.csp");
  TextIO.output (file_csp, wrCSP_ (toCSP g1));
  TextIO.closeOut(file_csp);

val file_alloy = TextIO.openOut(dir_alloy^"G1.als");
  TextIO.output (file_alloy, wrAlloyModule (toAlloy g1));
  TextIO.closeOut(file_alloy);

val file_csp = TextIO.openOut(dir_csp^"G2.csp");
  TextIO.output (file_csp, wrCSP_ (toCSP g2));
  TextIO.closeOut(file_csp);

val file_alloy = TextIO.openOut(dir_alloy^"G2.als");
  TextIO.output (file_alloy, wrAlloyModule (toAlloy g2));
  TextIO.closeOut(file_alloy);

val file_csp = TextIO.openOut(dir_csp^"G3.csp");
  TextIO.output (file_csp, wrCSP_ (toCSP g3));
  TextIO.closeOut(file_csp );

val file_alloy = TextIO.openOut(dir_alloy^"G3.als");
  TextIO.output (file_alloy , wrAlloyModule (toAlloy g3));
  TextIO.closeOut(file_alloy );

val file_csp = TextIO.openOut(dir_csp^"G3b.csp");
  TextIO.output (file_csp, wrCSP_ (toCSP g3b));
  TextIO.closeOut(file_csp);

val file_alloy = TextIO.openOut(dir_alloy^"G3b.als");
  TextIO.output (file_alloy , wrAlloyModule (toAlloy g3b));
  TextIO.closeOut(file_alloy );

val file_csp = TextIO.openOut(dir_csp^"G4a.csp");
  TextIO.output (file_csp, wrCSP_ (toCSP g4a));
  TextIO.closeOut(file_csp);

val file_alloy = TextIO.openOut(dir_alloy^"G4a.als");
  TextIO.output (file_alloy , wrAlloyModule (toAlloy g4a));
  TextIO.closeOut(file_alloy );

val file_csp = TextIO.openOut(dir_csp^"G4b.csp");
  TextIO.output (file_csp, wrCSP_ (toCSP g4b));
  TextIO.closeOut(file_csp);

val file_alloy = TextIO.openOut(dir_alloy^"G4b.als");
  TextIO.output (file_alloy , wrAlloyModule (toAlloy g4b));
  TextIO.closeOut(file_alloy );
*}

end