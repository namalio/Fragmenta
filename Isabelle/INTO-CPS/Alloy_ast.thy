(********  
  Theory: 'Alloy_ast'
  Description:  Defines abstract syntax of Alloy
  Author:     Nuno Amálio
***********)

theory Alloy_ast
imports Main "My_Str" "../Extra/List_Extra" "~~/src/HOL/Library/Code_Char"
begin

(* Type 'AlloyId'*)
type_synonym AlloyId = "string"

datatype sigTy = abstract | normal

datatype decl = vdecl (AlloyId list) declExp
  and declExp = declSetExp | declRelExp
  and declSetExp = 
datatype sigDecl = sig sigTy AlloyId sigBody
  and sigBody =  

