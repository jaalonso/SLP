theory InduccionGeneral
imports Main
begin

section {* La función mitad *}

text {* (mitad x) es la mitad del número natural x. Por ejemplo, 
     mitad (Suc (Suc (Suc (Suc 0)))) = Suc (Suc 0) 
     mitad (Suc (Suc (Suc 0)))       = Suc 0 
*}
fun mitad :: "nat \<Rightarrow> nat" where
  "mitad 0             = 0" 
| "mitad (Suc 0)       = 0" 
| "mitad (Suc (Suc n)) = 1 + mitad n"

value "mitad (Suc (Suc (Suc (Suc 0))))"
lemma "mitad (Suc (Suc (Suc (Suc 0)))) = Suc (Suc 0)" by simp 
value "mitad (Suc (Suc (Suc 0)))"
lemma "mitad (Suc (Suc (Suc 0))) = Suc 0" by simp 

text {* El esquema de inducción correspondiente a la función mitad es
     \<lbrakk>P 0; P (Suc 0); \<And>n. P n \<Longrightarrow> P (Suc (Suc n))\<rbrakk> \<Longrightarrow> P a
  es decir, para demostrar que todo número a tiene la propiedad P basta
  demostrar que:
  · 0 tiene la propiedad P
  · (Suc 0) tiene la propiedad P
  · si n tiene la propiedad P, entonces (Suc (Suc n)) también la tiene.
*}
thm mitad.induct [no_vars]

text {* Prop.: Para todo n, 2 * mitad n \<le> n *}
lemma "2 * mitad n \<le> n"
apply (induction n rule: mitad.induct)
apply auto
done

section {* La función intercala *}

text {* (intercala x ys) es la lista obtenida intercalando x entre los
  elementos de ys. Por ejemplo, 
     intercala a [x,y,z] = [x, a, y, a, z]" by simp
*} 
fun intercala :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" 
where
  "intercala a []       = []" 
| "intercala a [x]      = [x]" 
| "intercala a (x#y#zs) = x # a # intercala a (y#zs)"

value "intercala a [x,y,z]"
lemma "intercala a [x,y,z] = [x, a, y, a, z]" by simp

text {* El esquema de inducción correspondiente a la función intercala es
     \<lbrakk>\<And>a. P a []; 
      \<And>a x. P a [x]; 
      \<And>a x y zs. P a (y # zs) \<Longrightarrow> P a (x # y # zs)\<rbrakk> 
     \<Longrightarrow> P b xs
  es decir, para demostrar que para todo b y xs el par (b,xs) se tiene
  la propiedad P basta demostrar que:
  · para todo a, el par (a,[]) tiene la propiedad P
  · para todo a, el par (a,[x]) tiene la propiedad P
  · para todo a, x, y, zs, si el par (a,y#zs) tiene la propiedad P
    entonces el par (a,x#y#zs) tiene la propiedad P.
*}
thm intercala.induct [no_vars]

text {* Prop.: Aplicar la función f al resultado de intercalar a en xs
  es lo mismo que intercalar (f a) en las imágenes de xs mediante f. *} 
lemma "map f (intercala a xs) = intercala (f a) (map f xs)"
apply (induction a xs rule: intercala.induct)
apply auto
done

end
