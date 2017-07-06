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
     fun suma :: "nat \<Rightarrow> nat \<Rightarrow> nat" 
     where
       "suma 0 n = n" 
     | "suma (Suc m) n = Suc (suma m n)"
  demostrar que la suma de los naturales es conmutativa.
  ------------------------------------------------------------------- *}

fun suma :: "nat \<Rightarrow> nat \<Rightarrow> nat" 
where
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
  Ejercicio 3. [Ocurrencias de un elemento en una lista]
  
  Ejercicio 3.1. Definir la función
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
value "cuenta [3, 2] (3::nat)"
value "cuenta [3, 3] (3::nat)"
value "cuenta [] (3::nat)"

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
  Ejercicio 4. [Añadiendo los elementos al final de la lista e inversa]
  
  Ejercicio 4.1. Definir, por recursión, la función
     snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list"
  tal que (snoc xs y) es la lista obtenida añadiendo y al final de xs.
  Por ejemplo, 
     snoc [3,5,2] 7 = [3,5,2,7]
*}

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] x       = [x]" 
| "snoc (y # ys) x = y # (snoc ys x)" 

value "snoc [3,5,2] (7::int)"

lemma "snoc [3,5,2] (7::int) = [3,5,2,7]"
by simp

text {*
  ----------------------------------------------------------------------
  Ejercicio 4.2. Definir, por recursión, la función
     inversa :: "'a list \<Rightarrow> 'a list"
  tal que (inversa xs) es la lista obtenida invirtiendo el orden de los
  elementos de xs. Por ejemplo,
     inversa [a, b, c] = [c, b, a]
  ------------------------------------------------------------------- *}

fun inversa :: "'a list \<Rightarrow> 'a list"  where
  "inversa []       = []" 
| "inversa (x # xs) = snoc (inversa xs) x" 

value "inversa [a, b, c]"

lemma "inversa [a, b, c] = [c, b, a]"
by simp

text {*
  ----------------------------------------------------------------------
  Ejercicio 4.3. Demostrar que 
     inversa (inversa xs) = xs"
  Nota: Se necesita un lema relacionando las funciones inversa y snoc.   
  ------------------------------------------------------------------- *}

lemma inversa_snoc: "inversa (snoc xs y) = y # inversa xs"
by (induct xs) auto

theorem "inversa (inversa xs) = xs"
by (induct xs) (auto simp suma: inversa_snoc)

text {*
  ----------------------------------------------------------------------
  Ejercicio 4.4. Definir la función 
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

text {*
  ----------------------------------------------------------------------
  Ejercicio 4.5. Demostrar que
     inversa_it (inversa_it xs) = xs"
  ------------------------------------------------------------------- *}

lemma inversa_it_aux_lemma:
  "\<forall>ys. inversa_it_aux [] (inversa_it_aux ys xs) = inversa_it_aux xs ys"
by (induct xs) auto

lemma "inversa_it (inversa_it xs) = xs"
by (simp suma: inversa_it_aux_lemma)

end

