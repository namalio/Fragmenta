
(*  Theory:      'INTO_SysML_3WTs_toCSP'
    Description: Generates CSPm files for the 3 water tanks models that can be run in FDR3
    Author:      Nuno Amálio
*)

theory INTO_SysML_3WTs_toCSP
imports INTO_SysML_3WTs INTO_SysML_3WTs_loop CSP_print PDG_To_CSP
  
begin

(*This needs configuring for each local machine.*)
definition output_dir:: "string"
where
  "output_dir = ''/Users/wv8599/Work/Fragmenta/Isabelle/INTO-CPS/CSP/''"

export_code toCSP expid csp str_int INTO_SysML_toPDG
  MdlTy_3WTs MdlTy_3WTs_loop mdlL mtyL output_dir
  in SML module_name CSP file "csp.sml"

ML_file "csp.sml"

ML_file "wr-csp.sml"

ML {*
(*val dir1 = OS.FileSys.getDir();*)
val dir = charsToStr(output_dir);

val file = TextIO.openOut(dir^"3WTs.csp");
  TextIO.output (file, 
    wrCSP_ (toCSP (iNTO_SysML_toPDG mdlTy_3WTs)));
  TextIO.closeOut(file);

val file = TextIO.openOut(dir^"3WTs_loop.csp");
  TextIO.output (file, 
    wrCSP_ (toCSP (iNTO_SysML_toPDG mdlTy_3WTs_loop)));
  TextIO.closeOut(file);
*}

end