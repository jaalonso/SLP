theory R01Sol

imports Main
begin

text {* Relación 1 *}

text {* 
  ----------------------------------------------------------------------
  Ejercicio 1. [Cálculo con números naturales]
  Calcular el valor de las siguientes expresiones con números naturales:
  + 2 + (2::nat)
  + 2 + (2::int)
  + (2::nat) * (3 + 1)
  + (3::nat) * 4 - 2 * (7 + 1)
  + (3::int) * 4 - 2 * (7 + 1)"
  ------------------------------------------------------------------- *}

value "2 + (2::nat)"
  (* da "Suc (Suc (Suc (Suc 0)))" :: nat *)

value "2 + (2::int)"
  (* da "4" :: int *)

value "(2::nat) * (3 + 1)"
  (* da "Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))" *)
  
value "(3::nat) * 4 - 2 * (7 + 1)"
  (* da "0" :: nat *)

value "(3::int) * 4 - 2 * (7 + 1)"
  (* da "- 4" :: int *)
  
text {*
  ----------------------------------------------------------------------
  Ejercicio 2.1 [Propiedades de los números naturales]
  Usando la siguiente definición de suma de números naturales
     fun suma :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
       "suma 0 n = n" 
     | "suma (Suc m) n = Suc (suma m n)"
  demostrar que la suma de los naturales es conmutativa.
  ------------------------------------------------------------------- *}

fun suma :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "suma 0 n = n" 
| "suma (Suc m) n = Suc (suma m n)"

lemma suma_asociativa: 
  "suma (suma x y) z = suma x (suma y z)"
apply (induction x)
apply auto
done

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.2. Demostrar que la suma de los naturales es conmutativa.
  ------------------------------------------------------------------- *}

text {* 1\<ordfeminine> intento *}  
lemma suma_conmutativa_1: 
  "suma x y = suma y x"
apply (induction x)
apply simp
oops

text {* Queda sin demostrar 
     y = suma y 0
  por lo que se introduce el siguiente lema.
*}

lemma suma_0: 
  "suma x 0 = x"
apply (induction x)
apply auto
done

text {* 2\<ordfeminine> intento *}  
lemma suma_conmutativa_2: 
  "suma x y = suma y x"
apply (induction x)
apply (simp add: suma_0)
oops

text {* Queda pendiente el objetivo
     \<And>x. suma x y = suma y x \<Longrightarrow> suma (Suc x) y = suma y (Suc x)
  por lo que se introduce el siguiente lema.
*}

lemma suma_1: 
  "suma x (Suc y) = Suc (suma x y)"
apply (induction x) 
apply auto
done 

text {* 3\<ordfeminine> intento *}  
lemma suma_conmutativa_3: 
  "suma x y = suma y x"
apply (induction x)
apply (simp add: suma_0)
apply (simp add: suma_1)
done

text {* La demostración anterior se puede simplificar como sigue. *}
lemma suma_conmutativa: 
  "suma x y = suma y x"
by (induction x) (simp_all add: suma_0 suma_1)

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.3. Definir, por inducción,
     fun doble :: "nat \<Rightarrow> nat" 
  tal que (doble n) es el doble de n. Por ejemplo,
     doble 3 = 6
  ------------------------------------------------------------------- *}

fun doble :: "nat \<Rightarrow> nat" 
where
  "doble 0       = 0"
| "doble (Suc n) = suma (doble n) (Suc (Suc 0))"

value "int (doble 3)"
  (* da "6" :: int *)
lemma "doble 3 = 6" by normalization

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.4. Demostrar que
     doble x = suma x x
  ------------------------------------------------------------------- *}

text {* 1\<ordfeminine> demostración *}  
lemma doble_suma_1: 
  "doble x = suma x x"
apply (induction x)
apply simp
apply (simp add: suma_0 suma_1)
done

text {* 2\<ordfeminine> demostración *}  
lemma doble_suma: 
  "doble x = suma x x"
by (induction x) (simp_all add: suma_0 suma_1)

text {*
  ----------------------------------------------------------------------
  Ejercicio 3.1. [Ocurrencias de un elemento en una lista]
  Definir la función
     cuenta :: "'a list \<Rightarrow> 'a \<Rightarrow> nat"
  tal que (cuenta xs y) es el número de ocurrencia de y en xs. Por
  ejemplo,   
     cuenta [3, 2] 4 = 0
     cuenta [3, 2] 3 = Suc 0
     cuenta [3, 3] 3 = Suc (Suc 0)
     cuenta []     3 = 0
*}

fun cuenta :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "cuenta [] _       = 0" 
| "cuenta (x # xs) y = (if x = y 
                        then Suc (cuenta xs y) 
                        else cuenta xs y)"

value "cuenta [3, 2] (4::nat)" 
  (* da "0" *)
value "cuenta [3, 2] (3::nat)"
  (* da "Suc 0" *)
value "cuenta [3, 3] (3::nat)"
  (* da "Suc (Suc 0)" *)
value "cuenta [] (3::nat)"
  (* da "0" *)

text{*
  ----------------------------------------------------------------------
  Ejercicio 3.2. Demostrar que el número de ocurrencia de cualquier
  elemento en una lista es menor o igual que la longitud de la lista. 
  ------------------------------------------------------------------- *}

theorem "cuenta xs x \<le> length xs"
apply (induct xs)
apply auto
done

text {*
  ----------------------------------------------------------------------
  Ejercicio 4.1. [Añadiendo los elementos al final de la lista e inversa]
  Definir, por recursión, la función
     snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list"
  tal que (snoc xs y) es la lista obtenida añadiendo y al final de xs.
  Por ejemplo, 
     snoc [3,5,2] 7 = [3,5,2,7]
  ----------------------------------------------------------------------   
*}

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] x       = [x]" 
| "snoc (y # ys) x = y # (snoc ys x)" 

value "snoc [3,5,2] (7::int)"
  (* da "[3, 5, 2, 7]" *)
lemma "snoc [3,5,2] (7::int) = [3,5,2,7]"
by simp

text {*
  ----------------------------------------------------------------------
  Ejercicio 4.2. Definir, sin recursión, la función
     snoc2 :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list"
  tal que (snoc2 xs y) es la lista obtenida añadiendo y al final de xs.
  Por ejemplo, 
     snoc2 [3,5,2] 7 = [3,5,2,7]
  ----------------------------------------------------------------------   
*}

definition snoc2 :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc2 xs x \<equiv> xs @ [x]"

value "snoc2 [3,5,2] (7::int)"  
  (* da "[3, 5, 2, 7]" *)
lemma "snoc2 [3,5,2] (7::int) = [3, 5, 2, 7]" by normalization  

text {*
  ----------------------------------------------------------------------
  Ejercicio 4.3. Demostrar que las funciones snoc y snoc2 son
  equivalentes.
  ------------------------------------------------------------------- *}

lemma snoc_snoc2:
  "snoc xs x = snoc2 xs x"
apply (induction xs)
apply (simp_all add: snoc2_def)
done
  
text {*
  ----------------------------------------------------------------------
  Ejercicio 4.4. Definir, por recursión, la función
     inversa :: "'a list \<Rightarrow> 'a list"
  tal que (inversa xs) es la lista obtenida invirtiendo el orden de los
  elementos de xs. Por ejemplo,
     inversa [a, b, c] = [c, b, a]
  ------------------------------------------------------------------- *}

fun inversa :: "'a list \<Rightarrow> 'a list"  where
  "inversa []       = []" 
| "inversa (x # xs) = snoc (inversa xs) x" 

value "inversa [a, b, c]"
  (* da "[c, b, a]" *)
lemma "inversa [a, b, c] = [c, b, a]"
by simp

text {*
  ----------------------------------------------------------------------
  Ejercicio 4.5. Demostrar que 
     inversa (inversa xs) = xs"
  Nota: Se necesita un lema relacionando las funciones inversa y snoc.   
  ------------------------------------------------------------------- *}

text {* 1\<ordmasculine> intento *}  
theorem inversa_inversa_1: 
  "inversa (inversa xs) = xs"
apply (induction xs) 
apply simp
apply simp
oops
  
text {* Se quda sin demostrar 
     inversa (inversa xs) = xs \<Longrightarrow> 
     inversa (snoc (inversa xs) a) = a # xs
  por lo que se introduce el siguiente lema.   
*}
lemma inversa_snoc: 
  "inversa (snoc xs y) = y # inversa xs"
by (induct xs) auto

text {* Demostración *}
theorem inversa_inversa
  "inversa (inversa xs) = xs"
by (induct xs) (auto simp add: inversa_snoc)

text {*
  ----------------------------------------------------------------------
  Ejercicio 4.6. Definir la función 
     inversa_it :: "'a list \<Rightarrow> 'a list"
  tal que (inversa_it xs) es la inversa de xs calculada con un
  acumulador. Por ejemplo,
     inversa_it [a,b,c] = [c,b,a]
  ------------------------------------------------------------------- *}

fun inversa_it_aux :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "inversa_it_aux ys [] = ys" 
| "inversa_it_aux ys (x # xs) = inversa_it_aux (x # ys) xs"

fun inversa_it :: "'a list \<Rightarrow> 'a list" where 
"inversa_it xs = inversa_it_aux [] xs"

value "inversa_it [a,b,c]"
  (* da "[c, b, a]" *)
lemma "inversa_it [a,b,c] = [c, b, a]" by simp

text {*
  ----------------------------------------------------------------------
  Ejercicio 4.7. Demostrar que
     inversa_it (inversa_it xs) = xs"
  ------------------------------------------------------------------- *}

lemma inversa_it_aux_lemma:
  "\<forall>ys. inversa_it_aux [] (inversa_it_aux ys xs) = inversa_it_aux xs ys"
by (induct xs) auto

lemma "inversa_it (inversa_it xs) = xs"
by (simp add: inversa_it_aux_lemma)

text {*
  ----------------------------------------------------------------------
  Ejercicio 4.8. Demostrar que las funciones inversa y rev son
  equivalentes.
  ------------------------------------------------------------------- *}

lemma inversa_rev: 
  "inversa xs = rev xs"
apply (induction xs)
apply simp
apply (simp add: snoc_snoc2 snoc2_def)
done  

text {*
  ----------------------------------------------------------------------
  Ejercicio 4.9. Buscar los teoremas de la forma
     rev (rev _) = _
  ------------------------------------------------------------------- *}

find_theorems "rev (rev _) = _"
  (* Encuentra el teorema
        List.rev_rev_ident: rev (rev ?xs) = ?xs
  *)

text {*
  ----------------------------------------------------------------------
  Ejercicio 4.10. Demostrar, usando el teorema encontrado en el apartado
  anterior, que  
     inversa (inversa xs) = xs"
  ------------------------------------------------------------------- *}
  
lemma "inversa (inversa xs) = xs"
using [[simp_trace_new mode=full]]
apply (simp add: inversa_rev)
done

(* Se puede observar la traza del simplificador:
  Simplifier invoked 
  inversa (inversa xs) = xs 
    Apply rewrite rule? 
      Instance of R01Sol.inversa_rev: inversa xs \<equiv> rev xs
      Trying to rewrite: inversa xs 
        Successfully rewrote 
          inversa xs \<equiv> rev xs 
    Apply rewrite rule? 
      Instance of R01Sol.inversa_rev: inversa (rev xs) \<equiv> rev (rev xs)
      Trying to rewrite: inversa (rev xs) 
        Successfully rewrote 
          inversa (rev xs) \<equiv> rev (rev xs) 
    Apply rewrite rule? 
      Instance of List.rev_rev_ident: rev (rev xs) \<equiv> xs
      Trying to rewrite: rev (rev xs) 
        Successfully rewrote 
          rev (rev xs) \<equiv> xs 
    Apply rewrite rule? 
      Instance of HOL.simp_thms_6: xs = xs \<equiv> True
      Trying to rewrite: xs = xs 
        Successfully rewrote 
          xs = xs \<equiv> True
*)

text {*
  ----------------------------------------------------------------------
  Ejercicio 5.1. [Suma de los primeros números naturales]
  Definir la función
     suma_hasta :: "nat \<Rightarrow> nat" where
  tal que (suma_hasta n) es la suma de los números naturales hasta n.
  Por ejemplo, 
     suma_hasta 3 = 6
  ------------------------------------------------------------------- *}

fun suma_hasta :: "nat \<Rightarrow> nat" where
  "suma_hasta 0      = 0"
| "suma_hasta (Suc n) = suma_hasta n + Suc n"  
  
lemma "suma_hasta 3 = 6" by normalization

text {*
  ----------------------------------------------------------------------
  Ejercicio 5.2. Demostrar que
     suma_hasta n = n * (n + 1) div 2
  ------------------------------------------------------------------- *}

lemma "suma_hasta n = n * (n + 1) div 2"
apply (induction n)
apply simp_all
done

end

