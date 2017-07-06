theory Booleanos
imports Main
begin

section "Ejemplo de cálculo con booleanos"

value "True \<and> \<not>False"                        
  (* da "True" :: "bool"*)
value "\<not>(True \<or> \<not>False)"                     
  (* da "False" :: "bool"*)
value "(True \<and> \<not>False) = (True \<or> \<not>False)"    
  (* da "True" :: "bool"*)
value "True \<and> \<not>False \<longleftrightarrow> True \<or> \<not>False"      
  (* da "True" :: "bool"*)
value "True \<and> B"                              
  (* da B :: "bool"*)
value "True \<or> B"                              
 (* da "True" :: "bool"*)

section "Ejemplo de definición no recursiva con definition"

text {* (xor F G) se verifica si exactamente una de de las fórmulas F y
  G es verdadera. Por ejemplo, 
     xor True True  = False
     xor True False = True
*}
definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" 
where
  "xor F G \<equiv> (F \<noteq> G)"
    
value "xor True True"  (* da False *)
value "xor True False" (* da True *)
  
section "Ejemplo de definición con patrones usando fun"

text {* (conjuncion F G) se verifica si F y G son verdaderas. Por
  ejemplo,  
     conjuncion True  True = True 
     conjuncion False True = False
*} 
fun conjuncion :: "bool \<Rightarrow> bool \<Rightarrow> bool" 
where
  "conjuncion True G  = G"
| "conjuncion False _ = False"  

value "conjuncion True  True" (* da True *)
value "conjuncion False True" (* da False *)

section "Ejemplo de demostración por simplificación" 

lemma "conjuncion True B = B" by simp

section "Ejemplo de exportación a Haskell"

export_code conjuncion in Haskell

(* da
  module Booleanos(conjuncion) where {

  import Prelude ...
  import qualified Prelude;

  conjuncion :: Bool -> Bool -> Bool;
  conjuncion True g = g;
  conjuncion False uu = False;

  }
*)

end
