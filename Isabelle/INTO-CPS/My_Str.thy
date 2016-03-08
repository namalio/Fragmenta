
(********  
  Title:      Theory providing definitions related with strings
  Author:     Nuno Amálio
***********)

theory My_Str
imports Main
begin

(* This defines functions that yield strings corresponding to CSP Specs*)
fun str_nat :: "nat \<Rightarrow> string"
where
  "str_nat n = (if n < 10 then [char_of_nat (48 + n)] else 
     str_nat (n div 10) @ [char_of_nat (48 + (n mod 10))])"

definition str_int :: "int \<Rightarrow> string"
where
  "str_int i = (if i < 0 then ''-'' @ str_nat (nat (- i)) else 
     str_nat (nat i))"

end