theory Cuadrado
imports Main
begin

text {* (cuadrado x) es el cuadrado de x. Por ejemplo,
     cuadrado 3 = 9  
*}
definition cuadrado :: "int \<Rightarrow> int" where
  "cuadrado n = n*n"

value "cuadrado 3"  
lemma "cuadrado 3 = 9" by (simp add: cuadrado_def)  

end
