(********  
  Theory: 'WaterTanksn_Generate'
  Description:  Theory that generates CSP and Alloy for PDGs produced using 'WaterTanksn'
  Author:     Nuno Amálio
***********)

theory WaterTanksn_Generate
imports WaterTanksn "../Base/CSP_Print" "../Base/PDG_To_CSP" "../Base/PDG_To_Alloy"
begin

definition output_dir:: "string"
where
  "output_dir = ''/Users/wv8599/Work/Fragmenta/Isabelle/INTO-CPS/WaterTanksn/Generated/''"


export_code toCSP CSP_ast.expid Alloy_ast.AExpid Alloy_ast.dset Alloy_ast.dc Alloy_ast.sig 
  Alloy_ast.fact Alloy_ast.assert Alloy_ast.check Alloy_ast.psig Alloy_ast.amodule Alloy_ast.snormal 
  Alloy_ast.mone toAlloy csp str_int str_nat Suc src tgt NsG EsG toGr
  output_dir genPDGOfWtsn genPDGOfWtsn_loop in SML 
  module_name CSP_Alloy file "csp-alloy.sml"

ML_file "csp-alloy.sml"

ML_file "../Base/wr-csp.sml"

ML_file "../Base/wr-alloy.sml"

ML_file "../Base/wr-graphml.sml"

(*Some tests*)
value "genPDGOfWtsn 150"
value "genPDGOfWtsn_loop 1"
value "toCSP(genPDGOfWtsn 1)"

value "toGraphML (genPDGOfWtsn 1)"
value "toGraphML emptyGL"

ML {*

open CSP_Alloy;

val dir = charsToStr(output_dir);

fun to_Int Zero_nat = 0
  | to_Int (Suc n) = (to_Int n)+1

fun wrTxtSpec file txt = 
  (TextIO.output (file, txt); 
  TextIO.closeOut(file))

fun wrPDG_CSP n pdg pdg_loop = 
    let val file_csp = TextIO.openOut(dir^"WTsn_"^(charsToStr (str_nat n))^".csp")
      and file_csp_loop = TextIO.openOut(dir^"WTsn_"^(charsToStr (str_nat n))^"_loop.csp")
    in 
      wrTxtSpec file_csp (wrCSP_ (toCSP pdg));
      wrTxtSpec file_csp_loop (wrCSP_ (toCSP pdg_loop))
    end

fun wrPDG_Alloy n pdg pdg_loop = 
  let val file_alloy = TextIO.openOut(dir^"WTsn_"^(charsToStr (str_nat n))^".als")
    and file_alloy_loop = TextIO.openOut(dir^"WTsn_"^(charsToStr (str_nat n))^"_loop.als")
  in 
    wrTxtSpec file_alloy (wrAlloyModule (toAlloy pdg));
    wrTxtSpec file_alloy_loop (wrAlloyModule (toAlloy pdg_loop))
  end

fun wrPDG_GraphML n pdg pdg_loop = 
  let val file_graphml = TextIO.openOut(dir^"WTsn_"^(charsToStr (str_nat n))^".xml")
    and file_graphml_loop = TextIO.openOut(dir^"WTsn_"^(charsToStr (str_nat n))^"_loop.xml")
  in 
    wrTxtSpec file_graphml (toGraphML pdg);
    wrTxtSpec file_graphml_loop (toGraphML pdg_loop)
  end

fun wrPDG n = 
  if (to_Int n) > 0  then
    let val pdg = genPDGOfWtsn n
      and pdg_loop = genPDGOfWtsn_loop n
    in 
      wrPDG_CSP n pdg pdg_loop;
      wrPDG_Alloy n pdg pdg_loop;
      wrPDG_GraphML n pdg pdg_loop
   end
   else ()

fun wrPDGs Zero_nat = wrPDG Zero_nat
  | wrPDGs (Suc m) = (wrPDG (Suc m); (wrPDGs m))

fun to_nat0 0 = Zero_nat
  | to_nat0 n = Suc (to_nat0 (n -1))

fun to_nat i = to_nat0 (Int.abs i);
val pdg = genPDGOfWtsn (to_nat 1);

(*The water tank systems to generate according to function 'WaterTanksn'*)
(*wrPDGs (to_nat 50);*)
*}
end