theory Simplificacion2
imports Main
begin

section {* Reescritura condicional *}

lemma aux1: "P 0"
sorry

lemma aux2: "P x \<Longrightarrow> f x = g x"
sorry

lemma "f 0 \<Longrightarrow> g 0"
apply (simp add: aux1 aux2)
done

lemma "f 1 \<Longrightarrow> g 1"
apply (simp add: aux1 aux2)
oops

end
