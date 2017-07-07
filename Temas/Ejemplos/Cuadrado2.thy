theory Cuadrado2
imports Main
begin

text {* (cuadrado2 x) es el cuadrado de x. Por ejemplo,
     cuadrado2 3 = 9  
*}
abbreviation cuadrado2 :: "int \<Rightarrow> int" where
  "cuadrado2 n \<equiv> n*n"

value "cuadrado2 3"  
lemma "cuadrado2 3 = 9" by simp

end
