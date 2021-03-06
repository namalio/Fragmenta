
(*  Theory:      'INTO_SysML_3WTs_toCSP'
    Description: Generates CSPm files for the 3 water tanks models that can be run in FDR3
      and Alloy files to be run on Alloy 4.
    Author:      Nuno Amálio
*)

theory INTO_SysML_3WTs_toCSP
imports INTO_SysML_3WTs INTO_SysML_3WTs_loop "../Base/CSP_print" "../Base/PDG_To_CSP" 
  "../Base/PDG_To_Alloy"
  
begin

(*This needs configuring for each local machine.*)
definition CSP_output_dir:: "string"
where
  "CSP_output_dir = ''/Users/wv8599/Work/Fragmenta/Isabelle/INTO-CPS/Generated/''"

definition Alloy_output_dir:: "string"
where
  "Alloy_output_dir = ''/Users/wv8599/Work/Fragmenta/Isabelle/INTO-CPS/Generated/''"

export_code toCSP expid Alloy_ast.AExpid Alloy_ast.dset Alloy_ast.dc Alloy_ast.sig 
  Alloy_ast.fact Alloy_ast.assert Alloy_ast.check Alloy_ast.psig Alloy_ast.amodule 
  Alloy_ast.snormal Alloy_ast.mone toAlloy csp str_int str_nat INTO_SysML_toPDG
  MdlTy_3WTs MdlTy_3WTs_loop mdlL mtyL CSP_output_dir Alloy_output_dir
  in SML module_name CSP_Alloy file "csp-alloy.sml"

ML_file "csp-alloy.sml"

ML_file "../Base/wr-csp.sml" 

ML_file "../Base/wr-alloy.sml" 

ML {*
(*val dir1 = OS.FileSys.getDir();*)
val dir_csp = charsToStr(cSP_output_dir);
val dir_alloy = charsToStr(alloy_output_dir);

val file = TextIO.openOut(dir_csp^"3WTs.csp");
  TextIO.output (file, 
    wrCSP_ (toCSP (iNTO_SysML_toPDG mdlTy_3WTs)));
  TextIO.closeOut(file);

val file = TextIO.openOut(dir_alloy^"3WTs.als");
  TextIO.output (file, 
    wrAlloyModule (toAlloy (iNTO_SysML_toPDG mdlTy_3WTs)));
  TextIO.closeOut(file);

val file = TextIO.openOut(dir_csp^"3WTs_loop.csp");
  TextIO.output (file, 
    wrCSP_ (toCSP (iNTO_SysML_toPDG mdlTy_3WTs_loop)));
  TextIO.closeOut(file);

val file = TextIO.openOut(dir_alloy^"3WTs_loop.als");
  TextIO.output (file, 
    wrAlloyModule (toAlloy (iNTO_SysML_toPDG mdlTy_3WTs_loop)));
  TextIO.closeOut(file);
*}

end