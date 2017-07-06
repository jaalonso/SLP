theory Booleanos
imports Main
begin

text {* Ejemplo de cálculo con booleanos. *}
value "True \<and> \<not>False"                        (* da "True"  :: "bool"*)
value "\<not>(True \<or> \<not>False)"                     (* da "False" :: "bool"*)
value "(True \<and> \<not>False) = (True \<or> \<not>False)"    (* da "True"  :: "bool"*)
value "True \<and> \<not>False \<longleftrightarrow> True \<or> \<not>False"      (* da "True"  :: "bool"*)
value "True \<and> B"                              (* da B       :: "bool"*)
value "True \<or> B"                              (* da "True"  :: "bool"*)

text {* Ejemplo de definición no recursiva: (xor F G) se verifica si
  exactamente una de de las fórmulas F y G es verdadera. Por ejemplo,
     xor True True  = False
     xor True False = True
*}
definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" 
where
  "xor F G \<equiv> (F \<noteq> G)"
    
value "xor True True"  (* da False *)
value "xor True False" (* da True *)
  
text {* Ejemplo de definición con patrones: (conjuncion F G) se verifica
  si F y G son verdaderas. Por ejemplom 
     conjuncion True  True = True 
     conjuncion False True = False
  
*} 
fun conjuncion :: "bool \<Rightarrow> bool \<Rightarrow> bool" 
where
  "conjuncion True G  = G"
| "conjuncion False _ = False"  

value "conjuncion True  True" (* da True *)
value "conjuncion False True" (* da False *)

end
