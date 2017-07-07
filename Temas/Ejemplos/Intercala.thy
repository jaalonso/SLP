theory Intercala
imports Main
begin

section {* Ejemplo de función recursiva no primitiva recursiva *}

text {* (intercala x ys) es la lista obtenida intercalando x entre los
  elementos de ys. Por ejemplo, 
     intercala a [x,y,z] = [x, a, y, a, z]" by simp
*} 
fun intercala :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intercala a []       = []" 
| "intercala a [x]      = [x]" 
| "intercala a (x#y#zs) = x # a # intercala a (y#zs)"

value "intercala a [x,y,z]"
lemma "intercala a [x,y,z] = [x, a, y, a, z]" by simp

end
