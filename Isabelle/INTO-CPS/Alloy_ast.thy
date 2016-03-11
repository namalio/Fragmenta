(********  
  Theory: 'Alloy_ast'
  Description:  Defines the abstract syntax of Alloy
  Author:     Nuno Amálio
***********)

theory Alloy_ast
imports Main "My_Str" "../Extra/List_Extra" "~~/src/HOL/Library/Code_Char"
begin

(* Type 'AlloyId' of Alloy identifiers*)
type_synonym AlloyId = "string"

datatype SigTy = sabstract | snormal
datatype Mult = mlone | mone | msome

datatype AExp = 
    AExpid AlloyId 
    | AExpset AExp  ("\<aa>set")
    | AExpTrcl AExp ("\<aa>^")
    | AExpno AExp ("\<aa>no")
    | AExpthis ("\<aa>this")
    | AExpIdn ("\<aa>iden")
    | AExpnone ("\<aa>none")
    | AExpeq AExp AExp (infix "\<aa>=" 60)
    | AExpneq AExp AExp (infix "\<aa>!=" 60)
    | AExpDot AExp AExp (infix "\<aa>." 60)
    | AExpPlus AExp AExp (infix "\<aa>+" 60)
    | AExpAnd AExp AExp (infix "\<aa>&" 60)

datatype DeclExp = dset "Mult option" AExp 
datatype Decl = dc "AlloyId list" DeclExp
datatype SigDecl = sig SigTy "Mult option" "AlloyId list" "AlloyId option" "Decl list" "AExp list"
datatype FactDecl = fact "AlloyId" "AExp list"
datatype AssertDecl = assert "AlloyId" "AExp list"
datatype CheckDecl = check "AlloyId" nat

datatype AlloyParagraph = psig SigDecl | pfact FactDecl | passert AssertDecl |pcheck CheckDecl
datatype AlloyModule = amodule "AlloyId" "AlloyParagraph list"

end

