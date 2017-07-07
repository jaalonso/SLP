theory Induccion
imports Main
begin

section {* Definiciones de la función inversa *}

text {* (inversa xs) es la inversa de xs. Por ejemplo,
     inversa [a,b,c] = [c,b,a]
*}
fun inversa :: "'a list \<Rightarrow> 'a list" where
  "inversa []     = []"
| "inversa (x#xs) = inversa xs @ [x]"

value "inversa [a,b,c]"
lemma "inversa [a,b,c] = [c,b,a]" by simp

text {* (inversaIaux xs) es la inversa de xs calculada de manera
  iterativa. Por ejemplo, 
     inversaIaux [a,b,c] = [c,b,a]
*}
fun inversaIaux :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "inversaIaux [] ys     = ys" 
| "inversaIaux (x#xs) ys = inversaIaux xs (x#ys)"

definition inversaI :: "'a list \<Rightarrow> 'a list"
where
  "inversaI xs = inversaIaux xs []"

value "inversaI [a,b,c]"
lemma "inversaI [a,b,c] = [c,b,a]" by (simp add: inversaI_def)

section {* Equivalencia de las definiciones de inversa *}

text {* El objetivo de esta sección es demostrar la equivalencia de las
  dos definiciones; es decir,
     equiv_inversa: "inversaI xs = inversa xs"
  
  A la vista de la definición de inversaI, se observa que la propiedad
  anterior es un corolario de 
     equiv_inversa_aux: "inversaIaux xs [] = inversa xs"

  Vamos a demostrar equiv_inversa_aux usando heurísticas de inducción.  
*}  

text {* 1\<ordmasculine> intento de prueba de equiv_inversa_aux *}
lemma equiv_inversa_aux_1:
  "inversaIaux xs [] = inversa xs"
apply (induction xs)  
apply auto
oops

text {* Se observa que se queda sin demostrar el objetivo 
     inversaIaux xs [] = inversa xs \<Longrightarrow> 
     inversaIaux xs [a] = inversa xs @ [a]
  
  La causa es que el enunciado era demasiado específico al tener como
  segundo argumento la lista vacía. Lo generalizamos a
     equiv_inversa_aux_2: inversaIaux xs ys = inversa xs @ ys
*}

text {* 2\<ordmasculine> intento de prueba de equiv_inversa_aux *}
lemma equiv_inversa_aux_2:
  "inversaIaux xs ys = inversa xs @ ys"
apply (induction xs)  
apply auto
oops

text {* Se observa que se queda sin demostrar el objetivo 
     inversaIaux xs ys = inversa xs @ ys \<Longrightarrow> 
     inversaIaux xs (a # ys) = inversa xs @ a # ys
  
  La causa es que aunque el segundo argumento es la variable ys, no se
  ha tenido en cuenta que su valor varía. Por tanto, hay que declararla
  como arbitraria.
*}

text {* Prueba de equiv_inversa_aux *}
lemma equiv_inversa_aux:
  "inversaIaux xs ys = inversa xs @ ys"
apply (induction xs arbitrary: ys)  
apply auto
done

text {* Prueba de equiv_inversa *}
corollary equiv_inversa: 
  "inversaI xs = inversa xs"
apply (simp add: inversaI_def equiv_inversa_aux)
done

end
