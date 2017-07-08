theory Simplificacion1
imports Main
begin

section {* Seguimiento de la simplificación  *}

lemma "rev [x] = [x]"
using [[simp_trace]] 
apply simp
done

text {* El resultado de la traza es
     proof (prove)
     goal:
     No subgoals! 
     [1]SIMPLIFIER INVOKED ON THE FOLLOWING TERM:
     rev [x] = [x] 
     [1]Applying instance of rewrite rule "??.unknown":
     rev (?x1 # ?xs1) \<equiv> rev ?xs1 @ [?x1] 
     [1]Rewriting:
     rev [x] \<equiv> rev [] @ [x] 
     [1]Applying instance of rewrite rule "??.unknown":
     rev [] \<equiv> [] 
     [1]Rewriting:
     rev [] \<equiv> [] 
     [1]Applying instance of rewrite rule "List.append.append_Nil":
     [] @ ?y \<equiv> ?y 
     [1]Rewriting:
     [] @ [x] \<equiv> [x] 
     [1]Applying instance of rewrite rule "HOL.simp_thms_6":
     ?x1 = ?x1 \<equiv> True 
     [1]Rewriting:
     [x] = [x] \<equiv> True
     
  El significado de la traza es
       (rev [x]      = [x])
     = (rev [] @ [x] = [x])     [por "rev (x1 # xs1) = rev xs1 @ [x1]"] 
     = ([]     @ [x] = [x])     [por "rev [] = []"]
     = ([x]          = [x])     [por List.append.append_Nil]
     = True                     [por HOL.simp_thms_6]
*}

text{* Ejemplo de simplificación no condicional *}
lemma "(ys @ [] = []) = 
       (ys = [])"
apply simp
done

text{* Ejemplo de simplificación usando supuestos *}
lemma "\<lbrakk> xs @ zs = ys @ xs
       ; [] @ xs = [] @ [] \<rbrakk> 
       \<Longrightarrow> ys = zs"
apply simp
done

lemma 
  "\<lbrakk>  0 + n           = n
   ; (Suc m) + n     = Suc (m + n)
   ; (Suc m \<le> Suc n) = (m \<le> n)
   ; (0 \<le> m)         = True \<rbrakk>
   \<Longrightarrow> 0 + Suc 0 \<le> (Suc 0) + x"
apply simp
done

text {* Ejemplo de simplificación con reglas auxiliares *}
lemma "(a+b)*(a-b) = a*a - b*(b::int)"
apply (simp add: algebra_simps)
done

text {* Las reglas de algebra_simps son 
  (a + b) + c = a + (b + c)
  a + b = b + a
  b + (a + c) = a + (b + c)
  (a * b) * c = a * (b * c)
  a * b = b * a
  b * (a * c) = a * (b * c)
  a - (b - c) = a - (b + c)
  a + (b - c) = a + b - c
  (a - b = c) = (a = c + b)
  (a = c - b) = (a + b = c)
  a - (b - c) = (a + c) - b
  (a - b) + c = (a + c) - b
  (a - b < c) = (a < c + b)
  (a < c - b) = (a + b < c)
  (a - b \<le> c) = (a \<le> c + b)
  (a \<le> c - b) = (a + b \<le> c)
  (a + b) * c = a * c + b * c
  a * (b + c) = a * b + a * c
  a * (b - c) = a * b - a * c
  (b - c) * a = b * a - c * a
  a * (b - c) = a * b - a * c
  (a - b) * c = a * c - b * c
*}
thm algebra_simps [no_vars]

text {* Declaración de reglas como de simplificación *}
declare algebra_simps [simp]

text {* Ejemplo de simplificación con declaradas como simplificadores *}
lemma "(a+b)*(a-b) = a*a - b*(b::int)"
apply simp
done

end
