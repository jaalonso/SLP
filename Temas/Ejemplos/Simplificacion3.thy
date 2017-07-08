theory Simplificacion3
imports Main
begin

section {* Reescritura con definiciones *}

text {* Ejemplo de definición: (cuadrado x) es el cuadrado de x. Por
  ejemplo, 
     cuadrado (Suc (Suc 0)) = Suc (Suc (Suc (Suc 0)))
*}
definition cuadrado :: "nat \<Rightarrow> nat" where
  "cuadrado n = n*n"

value "cuadrado (Suc (Suc 0))"

text {* Ejemplo de lema con reescritura usando definición: *}
lemma "cuadrado (Suc (Suc 0)) = Suc (Suc (Suc (Suc 0)))" 
apply (simp add: cuadrado_def)
done

text {* Ejemplo de lema con reescritura usando definición: *}
lemma "cuadrado(n*n) = cuadrado(n)*cuadrado(n)"
apply (simp add: cuadrado_def) 
done

end
