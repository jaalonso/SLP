theory Naturales 
imports Main
begin

section "Ejemplo de cálculo con los naturales"

value "Suc 0 + Suc (Suc 0)" 
  (* da "Suc (Suc (Suc 0))" *)
value "Suc (Suc (Suc 0)) - Suc (Suc 0)" 
  (* da "Suc 0" *)
value "Suc (Suc 0) - Suc (Suc (Suc 0))" 
  (* da "0" *) 
value "Suc (Suc 0) * Suc (Suc (Suc 0))" 
  (* da "Suc (Suc (Suc (Suc (Suc (Suc 0)))))" *)
value "int (Suc (Suc 0) * Suc (Suc (Suc 0)))" 
  (* da  "6" :: int *)
value "int (Suc (Suc 0) ^ Suc (Suc (Suc 0)))"  
  (* da "8" *)  
value "Suc (Suc (Suc (Suc (Suc (Suc 0))))) div Suc (Suc 0)"
  (* da "Suc (Suc (Suc 0))" *)  
value "Suc (Suc (Suc (Suc (Suc 0)))) div Suc (Suc 0)"
  (* da "Suc (Suc 0)" *)  
value "Suc (Suc (Suc (Suc (Suc 0)))) mod Suc (Suc 0)"
  (* da "Suc 0" *)  
value "Suc 0 + Suc 0 < Suc (Suc (Suc 0))"
  (* da True *)
value "Suc 0 + Suc 0 < Suc (Suc 0)"
  (* da False *)
value "max (Suc 0 + Suc 0) (Suc (Suc (Suc 0)))"
  (* da "Suc (Suc (Suc 0))" *)
value "min (Suc 0 + Suc 0) (Suc (Suc (Suc 0)))"
  (* da "Suc (Suc 0)" *)
  
section "Ejemplo de definición recursiva sobre los naturales"

text {* (suma m n) es la suma de los números naturales m y n. Por
  ejemplo,
     suma (Suc (Suc 0)) (Suc (Suc (Suc 0)))
     = Suc (Suc (Suc (Suc (Suc 0))))
*} 
fun suma :: "nat \<Rightarrow> nat \<Rightarrow> nat" 
where
  "suma 0 n       = n" 
| "suma (Suc m) n = Suc (suma m n)"

value "suma (Suc (Suc 0)) (Suc (Suc (Suc 0)))"
value "int (suma (Suc (Suc 0)) (Suc (Suc (Suc 0))))"
lemma "suma (Suc (Suc 0)) (Suc (Suc (Suc 0)))
       = Suc (Suc (Suc (Suc (Suc 0))))" by simp

section "Ejemplo de demostración pos inducción sobre los naturales"       
       
text {* En esta sección se demuestra, por inducción sobre los naturales,
  que 0 es el neutro por la derecha de la suma. *} 

text {* Demostración aplicativa *}
lemma suma_0: 
  "suma m 0 = m"
apply (induction m)
apply auto
done

text {* Demostración estructurada *}
lemma suma_0': 
  "suma m 0 = m"
by (induction m) auto

text {* Los lemas demostrado se pueden consultar son thm *}
thm suma_0
  (* da "suma ?m 0 = ?m" *)

text {*  Los lemas demostrado se pueden consultar son thm y no_vars *}
thm suma_0 [no_vars]
  (* da "suma m 0 = m" *)
  
end

