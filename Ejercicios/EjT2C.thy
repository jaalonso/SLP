theory EjT2C
imports Main
begin

section "Ejercicio 2.10: Número de nodos en copias de árboles binarios"

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.10.1. Definir el tipo arbol0 para representar los
  árboles binarios sin valores en los nodos ni en las hojas. Por
  ejemplo, el árbol
       /\
      /\
  se define por
     abbreviation ejArbol0 :: arbol0 where
       "ejArbol0 \<equiv> N (N H H) H"
  ------------------------------------------------------------------- *}

datatype arbol0 = H
                | N arbol0 arbol0
                
abbreviation ejArbol0 :: arbol0 where
  "ejArbol0 \<equiv> N (N H H) H"

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.10.2. Definir la función
     nNodos :: "arbol0 \<Rightarrow> nat
  tal que (nNodos t) es el número de los nodos (internos u hojas) del
  árbol t. Por ejemplo, 
     nNodos ejArbol0 = 3
  ------------------------------------------------------------------- *}
  
fun nNodos :: "arbol0 \<Rightarrow> nat" where
  "nNodos H       = 1"
| "nNodos (N i d) = nNodos i + nNodos d"  

value "nNodos ejArbol0 = 3"

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.10.3. Definir la función
     copias :: "nat \<Rightarrow> arbol0 \<Rightarrow> arbol0
  tal que (copias n t) es es árbol con 2^n copias de t. Por ejemplo,
     copias 0 t = t
     copias 1 t = N t t
     copias 2 t = N (N t t) (N t t)
     copias 3 t = N (N (N t t) (N t t)) (N (N t t) (N t t))
  ------------------------------------------------------------------- *}

fun copias :: "nat \<Rightarrow> arbol0 \<Rightarrow> arbol0" where
  "copias 0 t       = t" 
| "copias (Suc n) t = copias n (N t t)"

value "copias 0 t = t"
value "copias 1 t = N t t"
value "copias 2 t = N (N t t) (N t t)"
value "copias 3 t = N (N (N t t) (N t t)) (N (N t t) (N t t))"

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.10.4. Demostrar que
     nNodos (copias n t) = 2^n * nNodos t
  ------------------------------------------------------------------- *}

lemma "nNodos (copias n t) = 2^n * nNodos t"
apply (induction n arbitrary: t)
apply simp_all
done

section "Ejercicio 2.11: Expresiones aritméticas y polinomios"

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.11.1. Las expresiones aritméticas sobre los enteros, con 
  una variable como máximo,se definen mediante el siguiente tipo de
  datos 
     datatype exp = Var | Const int | Suma exp exp | Mult exp exp
  
  Definir la función
     valor :: "exp \<Rightarrow> int \<Rightarrow> int
  tal que (valor e n) es e valor de la expresión e cuando se le asigna a
  su variable el valor n. Por ejemplo, 
     valor (Suma (Mult (Const 2) Var) (Const 3)) i = 2*i+3
  ------------------------------------------------------------------- *}

datatype exp = Var | Const int | Suma exp exp | Mult exp exp

fun valor :: "exp \<Rightarrow> int \<Rightarrow> int" where
  "valor Var n          = n" 
| "valor (Const x) _    = x"
| "valor (Suma e1 e2) n = valor e1 n + valor e2 n"
| "valor (Mult e1 e2) n = valor e1 n * valor e2 n"

value "valor (Suma (Mult (Const 2) Var) (Const 3)) i = 2*i+3"

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.11.2. Los polinomios se pueden representar mediante la
  lista de sus coeficientes. Por ejemplo, el polinomio 4+2x-x^2+3x^3
  se puede representar por [4,2,-1,3].
  
  Definir la función
     valorP :: "int list \<Rightarrow> int \<Rightarrow> int
  tal que (valorP p n) es el valor del polinomio p cuando se sustituye
  su variable por el número n. Por ejemplo, 
     valorP [4]        2 = 4
     valorP [4,2]      2 = 8
     valorP [4,2,-1]   2 = 4
     valorP [4,2,-1,3] 2 = 28
  ------------------------------------------------------------------- *}

fun valorP :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "valorP [] _ = 0"
| "valorP (c#cs) n = c + n * valorP cs n"

value "valorP [4]        2 = 4"
value "valorP [4,2]      2 = 8"
value "valorP [4,2,-1]   2 = 4"
value "valorP [4,2,-1,3] 2 = 28"

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.11.3. Definir la función
     coeficientes :: "exp \<Rightarrow> int list" where
  tal que (coeficientes e) es la lista de los coeficientes del polinomio
  correspondiente a la expresión e. Por ejemplo, 
     coeficientes (Suma Var (Const 3)) = [3,1]
     coeficientes (Suma Var (Const (-3))) = [-3,1]
     coeficientes (Mult (Suma Var (Const 3)) (Suma Var (Const (-3)))) 
     = [-9,0,1]
  ------------------------------------------------------------------- *}

text {* (sumaP p1 p2) es la suma de los polinomios p1 y p2. Por ejemplo.
     sumaP [2,3,5] [1,4] = [3,7,5]
*}  
fun sumaP :: "int list \<Rightarrow> int list \<Rightarrow> int list" where 
  "sumaP [] p2           = p2"
| "sumaP p1 []           = p1"
| "sumaP (c1#p1) (c2#p2) = (c1 + c2) # sumaP p1 p2"

value "sumaP [2,3,5] [1,4] = [3,7,5]"

text {* (multE x p) es el producto del número x por el polinomio p. Por
  ejemplo, 
*}
fun multE :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "multE _ []    = []"
| "multE x (c#p) = (x*c) # multE x p"   

value "multE 2 [3,1,4] = [6,2,8]"

text {* (multP p1 p2) es el producto de los polinomios p1 y p2. Por
  ejemplo,
     multP [3,1] [-3,1]  = [-9,0,1]
     multP [2,1] [1,4,3] = [2,9,10,3]
*}
fun multP :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "multP [] _ = []"
| "multP _ [] = []"  
| "multP (c#p) p2 = sumaP (multE c p2) (0 # multP p p2)"
  
value "multP [3,1] [-3,1]  = [-9,0,1]"
value "multP [2,1] [1,4,3] = [2,9,10,3]"

fun coeficientes :: "exp \<Rightarrow> int list" where
  "coeficientes Var          = [0,1]"
| "coeficientes (Const n)    = [n]"
| "coeficientes (Suma e1 e2) = sumaP (coeficientes e1) (coeficientes e2)"
| "coeficientes (Mult e1 e2) = multP (coeficientes e1) (coeficientes e2)"

value "coeficientes (Suma Var (Const 3)) = [3,1]"
value "coeficientes (Suma Var (Const (-3))) = [-3,1]"
value "coeficientes (Mult (Suma Var (Const 3)) (Suma Var (Const (-3))))
       = [-9,0,1]"

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.11.4. Demostrar que la función coeficientes preserva los
  valores de las expresiones.
  
  Nota: Se pueden usar las reglas de simplificación algebraica
  algebra_simps.
  ------------------------------------------------------------------- *}

lemma valorP_sumaP: 
  "valorP (sumaP p1 p2) x = valorP p1 x + valorP p2 x"
apply (induction p1 p2 rule: sumaP.induct)
apply (simp_all add: algebra_simps)
done

lemma valorP_multE: 
  "valorP (multE n p) x = n * valorP p x"
apply (induction p)
apply (simp_all add: algebra_simps)
done

lemma valorP_multP: 
  "valorP (multP p1 p2) x = valorP p1 x * valorP p2 x"
apply (induction p1 p2 rule: multP.induct)
apply (simp_all add: valorP_sumaP
                     valorP_multE
                     algebra_simps)
done

theorem valorP_coeficientes: 
  "valorP (coeficientes e) x = valor e x"
apply (induction e rule: exp.induct)
apply (simp_all add: valorP_sumaP
                     valorP_multP)
done

section "Ejercicio 2.12: Plegados sobre árboles"

text {* 
  ----------------------------------------------------------------------
  Ejercicio 2.12.1. Definir el tipo de dato arbolH para representar los
  árboles binarios que sólo tienen valores en las hojas. Por ejemplo, el
  árbol 
       ·
      / \
     3   ·
        / \
       5   7
  se representa por
     Nodo (Hoja 3) (Nodo (Hoja 5) (Hoja 7))
  ------------------------------------------------------------------- *}

datatype 'a arbolH = 
  Hoja 'a 
| Nodo "'a arbolH" "'a arbolH"

abbreviation ejArbolH1 :: "int arbolH" 
where
  "ejArbolH1 \<equiv> Nodo (Hoja (3::int)) (Nodo (Hoja 5) (Hoja 7))"

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.12.2. Definir la función
     infijo :: "'a arbolH \<Rightarrow> 'a list" 
  tal que (infijo x) es el recorrido infijo del árbol hoja x. Por
  ejemplo,
     infijo ejArbolH1 = [3,5,7]
  ------------------------------------------------------------------- *}

fun infijo :: "'a arbolH \<Rightarrow> 'a list" 
where
  "infijo (Hoja x)   = [x]"
| "infijo (Nodo i d) = infijo i @ infijo d"  

value "infijo ejArbolH1"
lemma "infijo ejArbolH1 = [3,5,7]" by simp

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.12.3. Consultar la definición de la función fold de plegado
  de listas.
  ------------------------------------------------------------------- *}

-- "Una forma de consultarlo es"  
thm fold.simps  

text {*
  El resultado es   
     fold ?f []         = id
     fold ?f (?x # ?xs) = fold ?f ?xs \<circ> ?f ?x
  *}

-- "Otra forma de consultarlo es"  
thm fold_simps

text {*
  El resultado es
     fold ?f [] ?s         = ?s
     fold ?f (?x # ?xs) ?s = fold ?f ?xs (?f ?x ?s)
  *}

-- "Se puede comprobar la definición"  
lemma 
  "fold f [] s     = s"
  "fold f (x#xs) s = fold f xs (f x s)" 
by simp_all

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.12.4. Definir la función
     fold_arbolH :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a arbolH \<Rightarrow> 'b \<Rightarrow> 'b"
  tal que (fold_arbolH f x y) es plegado del árbol hoja x con la
  operación f y el valor inicial x. Por ejemplo,
     fold_arbolH op+ ejArbolH1 0 = 15
     fold_arbolH op* ejArbolH1 1 = 105
  ------------------------------------------------------------------- *}
  
fun fold_arbolH :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a arbolH \<Rightarrow> 'b \<Rightarrow> 'b" 
where
  "fold_arbolH f (Hoja x) y   = f x y"
| "fold_arbolH f (Nodo i d) y = fold_arbolH f d (fold_arbolH f i y)"

value "fold_arbolH op+ ejArbolH1 0"
lemma "fold_arbolH op+ ejArbolH1 0 = 15" by simp
value "fold_arbolH op* ejArbolH1 1"
lemma "fold_arbolH op* ejArbolH1 1 = 105" by simp

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.12.5. Demostrar que
     fold_arbolH f x y = fold f (infijo x) y
  ------------------------------------------------------------------- *}

lemma "fold_arbolH f x y = fold f (infijo x) y"  
by (induction x arbitrary: y) auto

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.12.6. Definir la función
     espejo :: "'a arbolH \<Rightarrow> 'a arbolH"
  tal que (espejo x) es la imagen especular del árbol x. Por ejemplo,
     espejo ejArbolH1 = Nodo (Nodo (Hoja 7) (Hoja 5)) (Hoja 3)
  ------------------------------------------------------------------- *}

fun espejo :: "'a arbolH \<Rightarrow> 'a arbolH" 
where
  "espejo (Hoja x)   = Hoja x"  
| "espejo (Nodo i d) = Nodo (espejo d) (espejo i)"

value "espejo ejArbolH1"
lemma "espejo ejArbolH1 = Nodo (Nodo (Hoja 7) (Hoja 5)) (Hoja 3)" 
  by simp

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.12.7. Demostrar que
     infijo (espejo t) = rev (infijo t)
  ------------------------------------------------------------------- *}
    
lemma "infijo (espejo t) = rev (infijo t)"  
by (induction t) auto

section "Ejercicio 2.13: Alineamientos de listas"

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.13.1. Un alineamiento de dos lista xs e ys es una lista
  cuyos elementos son los de xs e ys consevando su orden original. Por
  ejemplo, un alineamiento de [a,b] y [c,d,e] es [a,c,d,b,e] y otro es
  [c,a,d,e,b]. 
  
  Definir la función
     alineamientos :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list" 
  tal que (alineamientos xs ys) es la lista de los alineamientos de xs e
  ys. Por ejemplo, 
     alineamientos [a,b] [c,d,e] 
     = [[a,b,c,d,e],[a,c,b,d,e],[a,c,d,b,e],[a,c,d,e,b],[c,a,b,d,e],
        [c,a,d,b,e],[c,a,d,e,b],[c,d,a,b,e],[c,d,a,e,b],[c,d,e,a,b]]
  ------------------------------------------------------------------- *}

fun alineamientos :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list"  
where
  "alineamientos xs []         = [xs]"
| "alineamientos [] ys         = [ys]"  
| "alineamientos (x#xs) (y#ys) = 
    map (op # x) (alineamientos xs (y#ys)) @ 
    map (op # y) (alineamientos (x#xs) ys)"  
   
value "alineamientos [a,b] [c,d,e]"
lemma "alineamientos [a,b] [c,d,e] =
       [[a,b,c,d,e],[a,c,b,d,e],[a,c,d,b,e],[a,c,d,e,b],[c,a,b,d,e],
        [c,a,d,b,e],[c,a,d,e,b],[c,d,a,b,e],[c,d,a,e,b],[c,d,e,a,b]]"
  by simp

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.13.2. Demostrar que la longitud de cualquier alineamiento de
  las listas xs e ys es la suma de las longitudes de los alineamientos
  de xs e ys.
  ------------------------------------------------------------------- *}

lemma "zs \<in> set (alineamientos xs ys) \<Longrightarrow> 
       length zs = length xs + length ys"
apply (induction xs ys arbitrary: zs rule: alineamientos.induct)
apply auto  
done  

text {* Nota. La función set convierte una lista en el conjunto de sus
  elementos. Por ejemplo, el resultado de
     value "set [a,b,c]"
  es   
     "{a, b, c}"
      :: "'a set"
  *}

section "Ejercicio 2.14: Plegado de listas"
  

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.14.1. Definir, por recursión, la función
     suma1 :: "int list \<Rightarrow> int" 
  tal que (suma1 xs) es la suma de los elementos de la lista xs. Por
  ejemplo, 
     suma1 [3,1,4] = 8
  ------------------------------------------------------------------- *}
  
fun suma1 :: "int list \<Rightarrow> int" 
where
  "suma1 []     = 0"
| "suma1 (x#xs) = x + suma1 xs"  

value "suma1 [3,1,4]"
lemma "suma1 [3,1,4] = 8" by simp

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.14.2. Definir, por plegado, la función
     suma2 :: "int list \<Rightarrow> int" 
  tal que (suma2 xs) es la suma de los elementos de la lista xs. Por
  ejemplo, 
     suma2 [3,1,4] = 8
  ------------------------------------------------------------------- *}
  
definition suma2 :: "int list \<Rightarrow> int" 
where 
  "suma2 xs \<equiv> fold op+ xs 0"

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.14.3. Demostrar que las funciones suma1 y suma2 son
  equivalentes.
  ------------------------------------------------------------------- *}

lemma aux: "fold op+ xs a = suma1 xs + a"  
by (induction xs arbitrary: a) auto
  
lemma "suma1 xs = suma2 xs"
by (simp add: aux suma2_def)

section "Ejercicio 2.15: Lista con elementos distintos"

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.15.1. Definir, por recursión, la función
     pertenece :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" 
  tal que (pertenece x ys) se verifica si x es un elemento de ys. Por
  ejemplo, 
     pertenece 2 [7,2,5] = True
     pertenece 4 [7,2,5] = False
  ------------------------------------------------------------------- *}

fun pertenece :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" 
where
  "pertenece x []     = False"
| "pertenece x (y#ys) = (x = y \<or> pertenece x ys)"

value "pertenece 4 [7,2,(5::nat)]"
lemma "pertenece 4 [7,2,(5::nat)] = False" by simp
value "pertenece 2 [7,2,(5::nat)]"
lemma "pertenece 2 [7,2,(5::nat)] = True" by simp

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.15.2. Definir la función
     distintos :: "'a list \<Rightarrow> bool
  tal que (distintos xs) se verifica si la lista xs no tiene elementos
  repetidos. Por ejemplo, 
     distintos [7,2,5] = True
     distintos [7,2,7] = False
  ------------------------------------------------------------------- *}

fun distintos :: "'a list \<Rightarrow> bool" 
where
  "distintos []     = True"
| "distintos (x#xs) = (\<not>(pertenece x xs) \<and> distintos xs)"

value "distintos [7,2,(5::nat)]"
lemma "distintos [7,2,(5::nat)] = True" by simp
value "distintos [7,2,(7::nat)]"
lemma "distintos [7,2,(7::nat)] = False" by simp

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.15.3. Demostrar que la inversa de una lista no tiene
  repeticiones si, y sólo si, la lista original no tiene repeticiones. 
  ------------------------------------------------------------------- *}

lemma pertenece_conc:
  "pertenece x (ys @ zs) = (pertenece x ys \<or> pertenece x zs)"
by (induction ys) simp_all

lemma pertenece_rev:
  "pertenece x (rev ys) = pertenece x ys"
by (induction ys) (auto simp add: pertenece_conc)

lemma distintos_conc:
  "distintos (xs @ [y]) = ( \<not>(pertenece y xs) \<and> distintos xs)"
by (induction xs) (auto simp add: pertenece_conc)  

lemma "distintos (rev xs) = distintos xs"
by (induction xs) (auto simp add: distintos_conc pertenece_rev)

section "Ejercicio 2.16: Plegados de listas por la derecha y por la izquierda"

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.16.1. Consultar las definiciones de fold y foldr
  ------------------------------------------------------------------- *}

thm fold.simps
thm foldr.simps

text {*
  El resultado es
    fold ?f []         = id
    fold ?f (?x # ?xs) = fold ?f ?xs \<circ> ?f ?x
    
    foldr ?f []         = id
    foldr ?f (?x # ?xs) = ?f ?x \<circ> foldr ?f ?xs
*}

lemma "fold  f [a,b,c] d = f c (f b (f a d))" by simp
lemma "foldr f [a,b,c] d = f a (f b (f c d))" by simp

lemma "foldr (op-) [1,2,3::int] 7 = (1 - (2 - (3 - 7)))" by auto
lemma "fold  (op-) [1,2,3::int] 7 = 3 - (2 - (1 - 7)) " by auto

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.16.2. Definir, usando fold, la función
     longitud1 :: "'a list \<Rightarrow> nat" 
  tal que (longitud1 xs) es la longitud de la lista xs. Por ejemplo,
     longitud1 [a,b,c] = 3
  ------------------------------------------------------------------- *}

definition longitud1 :: "'a list \<Rightarrow> nat" 
where
  "longitud1 xs = fold (\<lambda>x. Suc) xs 0"

value "longitud1 [a,b,c]"  
lemma "longitud1 [a,b,c] = 3" by (simp add: longitud1_def)  
  
text {*
  ----------------------------------------------------------------------
  Ejercicio 2.16.3. Definir, usando fold, la función
     longitud2 :: "'a list \<Rightarrow> nat" 
  tal que (longitud2 xs) es la longitud de la lista xs. Por ejemplo,
     longitud2 [a,b,c] = 3
  ------------------------------------------------------------------- *}

definition longitud2 :: "'a list \<Rightarrow> nat" 
where
  "longitud2 xs = foldr (\<lambda>x. Suc) xs 0"
  
value "longitud2 [a,b,c]"  
lemma "longitud2 [a,b,c] = 3" by (simp add: longitud2_def)  

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.16.4. Demostrar que las funciones longitud1 y length son
  equivalentes.
  ------------------------------------------------------------------- *}

lemma aux_fold:
  "fold (\<lambda>x. Suc) xs y  = y + length xs"
by (induction xs arbitrary: y) auto

lemma "longitud1 xs = length xs"
by (simp add: longitud1_def aux_fold)

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.16.5. Demostrar que las funciones longitud2 y length son
  equivalentes.
  ------------------------------------------------------------------- *}

lemma aux_foldr:
  "foldr (\<lambda>x. Suc) xs y  = y + length xs"
by (induction xs arbitrary: y) auto

lemma "longitud2 xs = length xs"
by (simp add: longitud2_def aux_foldr)

section "Ejercicio 2.17: Cortes de listas"

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.17.1. Dada una lista xs, el corte de xs de longitud menor
  o igual que m con inicio en i es la lista formada por el elemento de
  xs en la posición i y en las m-1 siguientes posiciones (si existen
  dichos elementos).  
  
  Definir la función
     corte :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list"
  tal que (corte xs i m) es el corte de xs de longitud menor o igual que
  m que empieza en la posición i. Por ejemplo, 
     "corte [0,1,2,3,4,5,6] 2 3 = [2,3,4] 
     "corte [0,1,2,3,4,5,6] 2 9 = [2,3,4,5,6] 
     "corte [0,1,2,3,4,5,6] 9 9 = []
  ------------------------------------------------------------------- *}

definition corte :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list"
where
  "corte xs i m = take m (drop i xs)"

declare corte_def [simp]
  
lemma "corte [0,1,2,3,4,5,6 ::int] 2 3 = [2,3,4]" by simp
lemma "corte [0,1,2,3,4,5,6 ::int] 2 9 = [2,3,4,5,6]" by simp 
lemma "corte [0,1,2,3,4,5,6 ::int] 9 9 = []" by simp
  
text {*
  ----------------------------------------------------------------------
  Ejercicio 2.17.2. Demostrar que la concatenación de dos cortes adyacentes
  se puede expresar como un único corte.
  ------------------------------------------------------------------- *}

lemma "corte xs i m1 @ corte xs (i + m1) m2 = corte xs i (m1 + m2)"
by (induction xs) (auto simp add: take_add add.commute)

text {*
  Los lemas utilizados son
  + take_add:    take (i + j) xs = take i xs @ take j (drop i xs)
  + add.commute: a + b = b + a
*}

text {*
  ----------------------------------------------------------------------
  Ejercicio 2.17.3. Demostrar que los cortes en listas de elementos no
  repetidos no tienen elementos repetidos.
  ------------------------------------------------------------------- *}

lemma pertenece_take:
  "pertenece a (take n xs) \<Longrightarrow> pertenece a xs"
by (metis append_take_drop_id pertenece_conc)
 
lemma distintos_take:
  "distintos xs \<Longrightarrow> distintos (take n xs)"
apply (induction xs arbitrary: n)
apply simp
apply (case_tac n)
  apply (auto simp add: pertenece_take)
done

lemma pertenece_drop:
  "pertenece a (drop n xs) \<Longrightarrow> pertenece a xs"
by (metis append_take_drop_id pertenece_conc)

lemma distintos_drop:
  "distintos xs \<Longrightarrow> distintos (drop n xs)"
apply (induction xs arbitrary: n)
apply simp
apply (case_tac n)
  apply (auto simp add: pertenece_drop)
done
  
lemma "distintos xs \<Longrightarrow> distintos (corte xs i m)"
by (induct xs) (auto simp add: distintos_take distintos_drop)

end

