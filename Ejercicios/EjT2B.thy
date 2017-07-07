theory EjT2B
imports Main
begin

section "Ejercicio 2.6: Suma de elementos de un árbol"

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.6.1. En este ejercicio se usa el tipo de los árboles
  definido por 
     datatype 'a arbol = Hoja | Nodo "'a arbol" 'a "'a arbol"
  Por ejemplo, el árbol
      9
     / \
   .    4
        /\
       .   .
  se define por
     abbreviation ejArbol1 :: "int arbol" where
       "ejArbol1 \<equiv> Nodo Hoja (9::int) (Nodo Hoja 4 Hoja)"
  Definir la función
     elementos :: "'a arbol \<Rightarrow> 'a list"
  tal que (elementos t) es la lista de los elementos del árbol t. Por
  ejemplo, 
     elementos ejArbol1                   = [9,4]
     elementos (Nodo ejArbol1 7 ejArbol1) = [9,4,7,9,4]
  ------------------------------------------------------------------- *}

datatype 'a arbol = Hoja | Nodo "'a arbol" 'a "'a arbol"

abbreviation ejArbol1 :: "int arbol" where
  "ejArbol1 \<equiv> Nodo Hoja (9::int) (Nodo Hoja 4 Hoja)"

fun elementos :: "'a arbol \<Rightarrow> 'a list" where
  "elementos Hoja = []"
| "elementos (Nodo i x d) = elementos i @ [x] @ elementos d"

value "elementos ejArbol1"
lemma "elementos ejArbol1 = [9,4]" by simp
value "elementos (Nodo ejArbol1 7 ejArbol1) = [9, 4, 7, 9, 4]"

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.6.2. Definir la función
     suma_arbol :: "int arbol \<Rightarrow> int" 
  tal que (suma_arbol t) es la suma de los elementos del árbol t. Por
  ejemplo, 
     suma_arbol ejArbol1 = 13 
     suma_arbol (Nodo ejArbol1 7 ejArbol1) = 33
  ------------------------------------------------------------------- *}

fun suma_arbol :: "int arbol \<Rightarrow> int" where
  "suma_arbol Hoja = 0"
| "suma_arbol (Nodo i x d) = suma_arbol i + x + suma_arbol d"  

value "suma_arbol ejArbol1 = 13" 
value "suma_arbol (Nodo ejArbol1 7 ejArbol1) = 33"

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.6.3. Demostrar que
     suma_arbol t = listsum (elementos t)
  ------------------------------------------------------------------- *}

lemma "suma_arbol t = listsum (elementos t)"
apply (induction t)
apply simp_all
done

section "Ejercicio 2.7: Recorrido de árboles e imagen especular"

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.7.1. Definir el tipo arbol2 para representar los árboles
  con valores en las hojas. Por ejemplo, el árbol
       /\
      /\ 1
     3  5
  se define por   
     abbreviation ejArbol2 :: "int arbol2" where
       "ejArbol2 \<equiv> N (N (H 3) (H 5)) (H (1::int))"
  ------------------------------------------------------------------- *}

datatype 'a arbol2 = H "'a" 
                   | N "'a arbol2" "'a arbol2"

abbreviation ejArbol2 :: "int arbol2" where
  "ejArbol2 \<equiv> N (N (H 3) (H 5)) (H (1::int))"
 
text {*
  ----------------------------------------------------------------------
  Ejercicio 2.7.2. Definir la función
     espejo :: "'a arbol2 \<Rightarrow> 'a arbol2" where
  tal que (espejo t) es la imagen especular de t. Por ejemplo,
     espejo ejArbol2 = N (H 1) (N (H 5) (H 3))
  ------------------------------------------------------------------- *}
  
fun espejo :: "'a arbol2 \<Rightarrow> 'a arbol2" where
  "espejo (H x)   = H x"
| "espejo (N i d) = N (espejo d) (espejo i)"  

value "espejo ejArbol2 = N (H 1) (N (H 5) (H 3))"

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.7.3. Definir la función
     pre_orden :: "'a arbol2 \<Rightarrow> 'a list"
  tal que (pre_orden t) es el recorrido pre orden de t. Por ejemplo,
     pre_orden ejArbol2 = [3, 5, 1]
  ------------------------------------------------------------------- *}

fun pre_orden :: "'a arbol2 \<Rightarrow> 'a list" where
  "pre_orden (H x) = [x]"
| "pre_orden (N i d) = pre_orden i @ pre_orden d"  

value "pre_orden ejArbol2 = [3, 5, 1]"

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.7.4. Definir la función
     post_orden :: "'a arbol2 \<Rightarrow> 'a list"
  tal que (post_orden t) es el recorrido post orden de t. Por ejemplo,
     post_orden ejArbol2 = [1, 5, 3]
  ------------------------------------------------------------------- *}

fun post_orden :: "'a arbol2 \<Rightarrow> 'a list" where
  "post_orden (H x)   = [x]"
| "post_orden (N i d) = post_orden d @ post_orden i"  

value "post_orden ejArbol2 = [1, 5, 3]"

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.7.5. Demostrar que
     pre_orden (espejo t) = post_orden t
  ------------------------------------------------------------------- *}

lemma "pre_orden (espejo t) = post_orden t"
apply (induction t)
apply simp_all
done

section "Ejercicio 2.8: Intercalado de un elemento"

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.8.1. Definir la función
     intercala :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list
  tal que (intercala x ys) es la lista obtenida intercalando x entre los
  elementos consecutivos de ys. Por ejemplo,
     intercala x [a,b,c] = [a,x,b,x,c]
  ------------------------------------------------------------------- *}

fun intercala :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intercala x []     = []"
| "intercala x [y]    = [y]"  
| "intercala x (y#ys) = y # x # intercala x ys"  

value "intercala x [a,b,c] = [a,x,b,x,c]"

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.8.2. Demostrar que
     map f (intercala a xs) = intercala (f a) (map f xs)
  ------------------------------------------------------------------- *}

lemma "map f (intercala a xs) = intercala (f a) (map f xs)"
apply (induction xs rule: intercala.induct)
apply simp_all
done

section "Ejercicio 2.9: Definición iterativa de suma de naturales"

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.9.1. Definir, como recursiva final, la función
     sumaIt :: "nat \<Rightarrow> nat \<Rightarrow> nat
  tal que (sumaIt n m) es la suma de n y m. Por ejemplo,
     sumaIt 3 2 = 5
  Nota: Que sumaIt es recursiva final significa que en la llamada
  recursiva, la aplicación de sumaIt es la última; es decir,
     sumaIt (Suc n) m = sumaIt ...
  ------------------------------------------------------------------- *}

fun sumaIt :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sumaIt 0 m = m"
| "sumaIt (Suc n) m = sumaIt n (Suc m)"  

value "sumaIt 3 2 = 5" 

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.9.2. Demostrar que la función suma It es equivalente a
  suma definida por
     fun suma :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
       "suma 0 m      = m"
     | "suma (Suc n) m = Suc (suma n m)"  
  ------------------------------------------------------------------- *}

fun suma :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "suma 0 m      = m"
| "suma (Suc n) m = Suc (suma n m)"  

text {* 1\<ordmasculine> intento *}
lemma "sumaIt n m = suma n m"
apply (induction n)
apply simp_all
oops

text {* Queda pendiente
     sumaIt n m = suma n m \<Longrightarrow> sumaIt n (Suc m) = Suc (suma n m)
  Para probarlo se introduce el siguiente lema. *}

lemma sumaIt1:
  "sumaIt n (Suc m) = Suc (sumaIt n m)"
sorry

text {* 2\<ordmasculine> intento *}
lemma "sumaIt n m = suma n m"
apply (induction n)
apply (simp_all add: sumaIt1)
done

end
