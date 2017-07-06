theory Listas
imports Main
begin

section "El tipo de las listas"

text {* ('a list) es el tipo de las listas con elementos de tipo 'a *}
datatype 'a lista = Nil | Cons "'a" "'a lista"

text {* Ejemplos de inferencia de tipo. *}
term "Nil"        
  (* da "lista.Nil" :: "'a lista" *)
term "Cons 1 Nil" 
  (* da "lista.Cons 1 lista.Nil" :: "'a lista" *)

text {* Declaración para acortar los nombres. *}
declare [[names_short]]

text {* Ejemplos de inferencia de tipo con nombres acortados. *}
term "Nil"        
  (* da "Nil" :: "'a lista" *)
term "Cons 1 Nil" 
  (* da "Cons 1 lista.Nil" :: "'a lista" *)

section "Funciones sobre listas: conc e inversa"

text {* (conc xs ys) es la concatenación de las listas xs e ys. Por
  ejemplo,   
     conc (Cons a (Cons b Nil)) (Cons c (Cons d Nil))
     = Cons a (Cons b (Cons c (Cons d Nil)))
*}
fun conc :: "'a lista \<Rightarrow> 'a lista \<Rightarrow> 'a lista" 
where
  "conc Nil ys         = ys" 
| "conc (Cons x xs) ys = Cons x (conc xs ys)"

value "conc (Cons a (Cons b Nil)) (Cons c (Cons d Nil))"
lemma "conc (Cons a (Cons b Nil)) (Cons c (Cons d Nil))
       = Cons a (Cons b (Cons c (Cons d Nil)))" by simp
       
text {* (inversa xs) es la inversa de la lista xs. Por ejemplo,  
*}
fun inversa :: "'a lista \<Rightarrow> 'a lista" 
where
  "inversa Nil         = Nil" 
| "inversa (Cons x xs) = conc (inversa xs) (Cons x Nil)"

value "inversa (Cons a (Cons b (Cons c Nil)))"
lemma "inversa (Cons a (Cons b (Cons c Nil)))
       = Cons c (Cons b (Cons a Nil))" by simp

export_code inversa in Haskell
(* El resultado es
  module Listas (Lista, inversa) where {

  import Prelude ((==), ...
  import qualified Prelude;

  data Lista a = Nil | Cons a (Lista a);

  conc :: forall a. Lista a -> Lista a -> Lista a;
  conc Nil ys = ys;
  conc (Cons x xs) ys = Cons x (conc xs ys);

  inversa :: forall a. Lista a -> Lista a;
  inversa Nil = Nil;
  inversa (Cons x xs) = conc (inversa xs) (Cons x Nil);
}
*)
       
section "Ejemplo de búsqueda descendente de la demostración"

text {* El objetivo de esta sección es mostrar cómo se conjeturan lemas
  auxiliares para la demostración de la idempotencia de la función
  inversa.
  
  Se mostrarán cómo los errores de las pruebas ayudan a conjeturar los
  lemas.
*}
       
text {* Primer intento de prueba de inversa_inversa. *}
theorem inversa_inversa_1: 
  "inversa (inversa xs) = xs"
apply (induction xs)
apply auto
oops

text {* Queda sin demostrar el siguiente objetivo:
     inversa (inversa xs) = xs \<Longrightarrow> 
     inversa (conc (inversa xs) (Cons x1 Nil)) = Cons x1 xs
            
  Se observa que contiene la expresión 
     inversa (conc (inversa xs) (Cons x1 Nil))
  que se puede simplificar a 
     conc (Cons x1 Nil) (inversa (inversa xs)) 
  con el siguiente lema:
     inversa (conc xs ys) = conc (inversa ys) (inversa xs)
*}

text {* Primer intento de prueba de inversa_conc. *}
lemma inversa_conc_1: 
  "inversa (conc xs ys) = conc (inversa ys) (inversa xs)"
apply (induction xs)
apply auto
oops

text {* Queda sin demostrar el objetivo
     inversa ys = conc (inversa ys) Nil
  Se puede demostrar con el siguiente lema
     conc xs Nil = xs
*}

text {* Prueba de conc_Nil2. *}
lemma conc_Nil2: 
  "conc xs Nil = xs"
apply (induction xs)
apply auto
done

text {* Segundo intento de prueba de inversa_conc usando conc_Nil2. *}
lemma inversa_conc_2: 
  "inversa (conc xs ys) = conc (inversa ys) (inversa xs)"
apply (induction xs)
apply (auto simp add: conc_Nil2)
oops

text {* Queda sin probar el objetivo
     inversa (conc xs ys) = conc (inversa ys) (inversa xs) \<Longrightarrow>
       conc (conc (inversa ys) (inversa xs)) (Cons x1 Nil) =
       conc (inversa ys) (conc (inversa xs) (Cons x1 Nil))
  que se puede simplificar usando la propiedad asociativa de conc.       
*}

text {* Prueba de asociatividad de conc. *}
lemma conc_asoc: 
  "conc (conc xs ys) zs = conc xs (conc ys zs)"
apply (induction xs)
apply auto
done

text {* Prueba de inversa_conc usando conc_Nil2 y conc_asoc. *}
lemma inversa_conc: 
  "inversa (conc xs ys) = conc (inversa ys) (inversa xs)"
apply (induction xs)
apply (auto simp add: conc_Nil2 conc_asoc)
done

text {* Prueba de inversa_inversa usando inversa_conc. *}
theorem inversa_inversa: 
  "inversa (inversa xs) = xs"
apply (induction xs)
apply (auto simp add: inversa_conc)
done

text {* Una vez encontrada la demostración, se puede modificar la
  presentación declarando los lemas como reglas de simplificación, como
  se muestra a continuación. *} 

lemma conc_Nil2' [simp]: 
  "conc xs Nil = xs"
by (induction xs) auto

lemma conc_asoc' [simp]: 
  "conc (conc xs ys) zs = conc xs (conc ys zs)"
by (induction xs) auto

lemma inversa_conc' [simp]: 
  "inversa (conc xs ys) = conc (inversa ys) (inversa xs)"
by (induction xs) auto

theorem inversa_inversa': 
  "inversa (inversa xs) = xs"
by (induction xs) auto

section "Ejemplo de cálculo con listas"

value "a # [b,c]"
  (* da "[a, b, c]" *)  
value "hd [a,b,c]"
  (* da "a" *)
value "tl [a,b,c]"
  (* da "[b, c]" *)
value "set [b,a,c]"
  (* da "{b, a, c}" :: "'a set" *)
value "set [b,a,c] = set [c,a,b,a,c]"
  (* da "True" *)
value "map f [a,b,c]"
  (* da "[f a, f b, f c]" *)
value "last [a,b,c]"
  (* da "c" *)
value "butlast [a,b,c]"
  (* da  "[a, b]" *)
value "[a,b] @ [c,a,d]"
  (* da "[a, b, c, a, d]" *)
value "rev [a,b,c,d]"
  (* da "[d, c, b, a]" *)
value "filter (op > (Suc (Suc 0))) [0,Suc 0, Suc (Suc (Suc 0)), 0]"
  (* da "[0, Suc 0, 0]" *)
value "filter (\<lambda>n::nat. n<2) [0,2,1] = [0,1]"
  (* da "True" *)
value "fold f [a,b,c] x" 
  (* da "f c (f b (f a x))" *)
value "fold (op +) [Suc 0, Suc (Suc 0), Suc 0] 0"
  (* da "Suc (Suc (Suc (Suc 0)))" *)  
value "foldr f [a,b,c] x"
  (* da "f a (f b (f c x))" *)
value "foldr (op -) [Suc (Suc (Suc 0)), Suc 0, Suc 0] 0"
  (* da ""Suc (Suc (Suc 0))" *)  
value "foldl f x [a,b,c]"
  (* da "f (f (f x a) b) c" *)
value "foldl (op -) 0 [Suc (Suc (Suc 0)), Suc 0, Suc 0]"
  (* da "0" *)  
value "concat [[a,b],[c],[d,a,c]]"
  (* da "[a, b, c, d, a, c]" *)
value "drop 2 [a,b,c,d]"
  (* da "[c, d]" *)
value "drop 6 [a,b,c,d]"
  (* da "[]" *)
value "take 2 [a,b,c,d]"
  (* da "[a, b]" *)
value "take 6 [a,b,c,d]"
  (* da "[a, b, c, d]" *)
value "nth [a,b,c,d] (Suc (Suc 0))"
  (* da "c" *)
value "list_update [a,b,c,d] (Suc (Suc 0)) g"
  (* da "[a, b, g, d]" *)
value "[a,b,c,d][Suc (Suc 0) := g]"
  (* da "[a, b, g, d]" *)
value "takeWhile (op > (Suc (Suc 0))) [0,Suc 0, Suc (Suc (Suc 0)), 0]"
  (* da "[0, Suc 0]" *)
value "dropWhile (op > (Suc (Suc 0))) [0,Suc 0, Suc (Suc (Suc 0)), 0]"
  (* da "[Suc (Suc (Suc 0)), 0]" *)
value "zip [a,b,c] [d,e,f,g]"
  (* da "[(a, d), (b, e), (c, f)]" *)
value "List.product [a,b] [c,d]" 
  (* da "[(a, c), (a, d), (b, c), (b, d)]" *)
value "product_lists [[a,b], [c], [d,e]]"
  (* da "[[a, c, d], [a, c, e], [b, c, d], [b, c, e]]" *)
value "List.insert (Suc 0) [0,Suc (Suc 0)]"
  (* da "[Suc 0, 0, Suc (Suc 0)]" *)
value "List.insert (Suc (Suc 0)) [0,Suc (Suc 0)]"
  (* da "[0, Suc (Suc 0)]" *)
value "List.union [0,Suc 0] [0,Suc (Suc 0)]"
  (* da "[Suc 0, 0, Suc (Suc 0)]" *)
value "find (op = (Suc 0)) [0,Suc 0, Suc (Suc (Suc 0)), 0]"
  (* da "Some (Suc 0)" *)
value "find (op = (Suc (Suc 0))) [0,Suc 0, Suc (Suc (Suc 0)), 0]"
  (* da "None" *)
value "count_list [0,Suc 0,0, Suc (Suc 0), 0] 0"
  (* da "Suc (Suc (Suc 0))" *)
value "remove1 0 [Suc 0, 0, Suc (Suc 0), 0]"
  (* da "[Suc 0, Suc (Suc 0), 0]" *)
value "removeAll 0 [Suc 0, 0, Suc (Suc 0), 0]"
  (* da "[Suc 0, Suc (Suc 0)]" *)
value "distinct [1::nat,2,3]"
  (* da "True" *)
value "distinct [1::nat,2,1]"
  (* da "False" *)
value "remdups [1::nat,2,1]"
  (* da "[Suc (Suc 0), Suc 0]" *)
value "replicate 3 a"
  (* da "[a, a, a]" *)
value "length [a,b,c]"
  (* da "Suc (Suc (Suc 0))" :: nat*)
value "int (length [a,b,c])"
  (* da "3" :: int *)
value "int (size [a,b,c])"
  (* da "3" :: int *)
value "enumerate 0 [b,a,c]"
  (* da "[(0, b), (Suc 0, a), (Suc (Suc 0), c)]" *)
value "enumerate 1 [b,a,c]"
  (* da "[(Suc 0, b), (Suc (Suc 0), a), (Suc (Suc (Suc 0)), c)]" *)
value "[1..<4]"
  (* da  "[Suc 0, Suc (Suc 0), Suc (Suc (Suc 0))]" *)
value "rotate1 [a,b,c]"
  (* da "[b, c, a]" *)
value "rotate1 [b,c,a]"
  (* da "[c, a, b]" *)
value "(rotate1 ^^ 2) [a,b,c]"
  (* da "[c, a, b]" *)
value "rotate 2 [a,b,c]"
  (* da "[c, a, b]" *)
value "sublists [a,b,c]"
  (* da "[[a, b, c], [a, b], [a, c], [a], [b, c], [b], [c], []]" *)
value "splice [a,b,c] [x,y,z]"
  (* da "[a, x, b, y, c, z]" *)
value "splice [a,b,c,d] [x,y]"
  (* da "[a, x, b, y, c, d]" *)
value "List.n_lists 2 [a,b,c]"
  (* da [[a,a], [b,a], [c,a], [a,b], [b,b], [c,b], [a,c], [b,c], [c,c]]" *)
value "sort [Suc 0, 0, Suc (Suc 0)]"
  (* da "[0, Suc 0, Suc (Suc 0)]" *)
  
end
