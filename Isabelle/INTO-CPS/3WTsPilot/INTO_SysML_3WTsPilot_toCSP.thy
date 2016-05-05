
(*  Theory:  'INTO_SysML_3WTsPilot_toCSP'
    Description: Generates the CSPm to check algebraic loops, corresponding to the 
    pilot version of the 3 water tanks INTO-SysML model, to be run in the FDR3 
    refinement checker
    Author: Nuno Amálio
*)

theory INTO_SysML_3WTsPilot_toCSP
imports INTO_SysML_3WTsPilot_Gbl INTO_SysML_3WTsPilot_loop_Gbl "../Base/CSP_print" "../Base/PDG_To_CSP" 
  "../Base/PDG_To_Alloy"
  
begin

(*This needs configuring for each local machine.*)
definition CSP_output_dir:: "string"
where
  "CSP_output_dir = ''/Users/wv8599/Work/Fragmenta/Isabelle/INTO-CPS/GeneratedWTs/''"

definition Alloy_output_dir:: "string"
where
  "Alloy_output_dir = ''/Users/wv8599/Work/Fragmenta/Isabelle/INTO-CPS/GeneratedWTs/''"

export_code toCSP expid Alloy_ast.AExpid Alloy_ast.dset Alloy_ast.dc Alloy_ast.sig 
  Alloy_ast.fact Alloy_ast.assert Alloy_ast.check Alloy_ast.psig Alloy_ast.amodule 
  Alloy_ast.snormal Alloy_ast.mone toAlloy csp str_int str_nat INTO_SysML_toPDG
  MdlTy_3WTsP MdlTy_3WTsP_loop mdlL mtyL CSP_output_dir Alloy_output_dir
  in SML module_name CSP_Alloy file "csp-alloy.sml"

ML_file "csp-alloy.sml"

ML_file "../Base/wr-csp.sml" 

ML_file "../Base/wr-alloy.sml" 

ML {*
(*val dir1 = OS.FileSys.getDir();*)
val dir_csp = charsToStr(cSP_output_dir);
val dir_alloy = charsToStr(alloy_output_dir);

val file = TextIO.openOut(dir_csp^"3WTs_Pilot.csp");
  TextIO.output (file, 
    wrCSP_ (toCSP (iNTO_SysML_toPDG mdlTy_3WTsP)));
  TextIO.closeOut(file);

val file = TextIO.openOut(dir_alloy^"3WTs_Pilot.als");
  TextIO.output (file, 
    wrAlloyModule (toAlloy (iNTO_SysML_toPDG mdlTy_3WTsP)));
  TextIO.closeOut(file);

val file = TextIO.openOut(dir_csp^"3WTs_Pilot_loop.csp");
  TextIO.output (file, 
    wrCSP_ (toCSP (iNTO_SysML_toPDG mdlTy_3WTsP_loop)));
  TextIO.closeOut(file);

val file = TextIO.openOut(dir_alloy^"3WTs_Pilot_loop.als");
  TextIO.output (file, 
    wrAlloyModule (toAlloy (iNTO_SysML_toPDG mdlTy_3WTsP_loop)));
  TextIO.closeOut(file);
*}

end