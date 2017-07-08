chapter "Expresiones aritméticas y booleanas"

theory ExpA 
imports Main 
begin

section "Expresiones aritméticas"

subsection "Sintaxis"

text {* Los nombres de las variables de las expresiones aritméticas son
cadenas y se representan por nombreV *} 
type_synonym nombreV = string

text {* Una expresión aritmética ~expA~ es un número entero, una
  variable o la suma de dos expresiones aritméticas. Por ejemplo,
     Suma (N 5) (V x1)      :: expA
     Suma (N 5) (V ''x 1'') :: expA
  *} 
datatype expA = N int | V nombreV | Suma expA expA

term "N 5"
term "V x1"
term "Suma (N 5) (V x1)"
term "Suma (N 5) (V ''x 1'')"

text {* La igualdad entre expresiones aritméticas es sintática, no
  semántica. Por ejemplo,
     N 0 = N 0
     Suma (N 0) (N 0) \<noteq> N 0
  *} 

value "N 0 = N 0"
value "Suma (N 0) (N 0) \<noteq> N 0"
  
subsection "Semántica"

text {* Los valores son números enteros y su tipo se representa por val
*} 
type_synonym val = int

text {* Los estados son funciones de los nombres de variables en
  valores. *} 
type_synonym estado = "nombreV \<Rightarrow> val"

text {* (valor a s) es el valor de la expresión aritmética a en el
  estado s. Por ejemplo, 
     valorA (Suma (V x) (N 5)) (\<lambda>y. 0) = 5
     valorA (Suma (V x) (N 5)) (\<lambda>y. if y = x then 7 else 0) = 12
     valorA (Suma (V x) (N 5)) ((\<lambda>x. 0) (x:= 7)) = 12
  *} 
fun valorA :: "expA \<Rightarrow> estado \<Rightarrow> val" where
  "valorA (N n) s       = n" 
| "valorA (V x) s       = s x" 
| "valorA (Suma a\<^sub>1 a\<^sub>2) s = valorA a\<^sub>1 s + valorA a\<^sub>2 s"

value "valorA (Suma (V x) (N 5)) (\<lambda>y. 0) = 5"
value "valorA (Suma (V x) (N 5)) (\<lambda>y. if y = x then 7 else 0) = 12"
value "valorA (Suma (V x) (N 5)) ((\<lambda>x. 0) (x:= 7)) = 12"

text {* <x1 := a1, x2 := a2, ..., xn := an> es el estado que le asigna a
  x1 el valor a1, a x2 el valor a2, ..., a xn el valor an y a las demás
  variables el valor 0. Por ejemplo,
     <''a'' := 3::int, ''b'' := 2> ''a'' = 3
     <''a'' := 3::int, ''b'' := 2> ''b'' = 2
     <''a'' := 3::int, ''b'' := 2> ''c'' = 0
     <a := 3, b := 2> = (<> (a := 3)) (b := 2) 
     <a := 3, b := 2> = ((\<lambda>x. 0) (a := 3)) (b := 2) 
*}
definition null_estado ("<>") where
  "null_estado \<equiv> \<lambda>x. 0"
syntax 
  "_Estado" :: "updbinds => 'a" ("<_>")
translations
  "_Estado ms" == "_Update <> ms"

value "<''a'' := 3::int, ''b'' := 2> ''a''"
  (* da 3 *)
value "<''a'' := 3::int, ''b'' := 2> ''b''"
  (* da 2 *)
value "<''a'' := 3::int, ''b'' := 2> ''c''"
  (* da 0 *)

lemma "\<lbrakk>x \<noteq> ''a''; x \<noteq> ''b''\<rbrakk> \<Longrightarrow> 
       <''a'' := 3::int, ''b'' := 2> x = 0"
  by (simp add: null_estado_def)    

lemma "<a := 3, b := 2> = (<> (a := 3)) (b := 2)" 
  by simp

lemma "<a := 3, b := 2> = ((\<lambda>x. 0) (a := 3)) (b := 2)" 
  by (simp add: null_estado_def)
  
value "valorA (Suma (V ''x'') (N 5)) <''x'' := 7>"
  (* da 12 *)
value "valorA (Suma (V ''x'') (N 5)) <''y'' := 7>"
  (* da 5 *)

section "Propagación de constantes"

text {* (simp_constA e) es la expresión aritmética obtenida aplicando
  propagación de constantes a la expresión e. Por ejemplo, 
     simp_constA (Suma (V ''x'') (Suma (N 3) (N 1))) 
       = Suma (V ''x'') (N 4)
     simp_constA (Suma (N 3) (Suma (V ''x'') (N 1)))
       = Suma (N 3) (Suma (V ''x'') (N 1))    
     simp_constA (Suma (N 3) (Suma (V ''x'') (N 0))) 
       = Suma (N 3) (Suma (V ''x'') (N 0))
*}

fun simp_constA :: "expA \<Rightarrow> expA" where
"simp_constA (N n) = N n" |
"simp_constA (V x) = V x" |
"simp_constA (Suma a\<^sub>1 a\<^sub>2) =
  (case (simp_constA a\<^sub>1, simp_constA a\<^sub>2) of
    (N n\<^sub>1, N n\<^sub>2) \<Rightarrow> N(n\<^sub>1+n\<^sub>2) |
    (b\<^sub>1,b\<^sub>2) \<Rightarrow> Suma b\<^sub>1 b\<^sub>2)"

value "simp_constA (Suma (V ''x'') (Suma (N 3) (N 1)))" 
  (* da "Suma (V ''x'') (N 4)" *)
value "simp_constA (Suma (N 3) (Suma (V ''x'') (N 1)))" 
  (* da "Suma (N 3) (Suma (V ''x'') (N 1))" *)    
value "simp_constA (Suma (N 3) (Suma (V ''x'') (N 0)))" 
  (* da "Suma (N 3) (Suma (V ''x'') (N 0))" *)
  
text {* Prop.: La función simp_constA es correcta; es decir, conserva el
  valor de las expresiones aritméticas. *}

text {* 1\<ordmasculine> intento *}  
theorem valorA_simp_constA1:
  "valorA (simp_constA a) s = valorA a s"
apply (induction a)
apply auto
oops

text {* Se observa que no ha expandido la expresión case. Para que lo
  haga, se añade "split: expA.split" *} 

theorem valorA_simp_constA:
  "valorA (simp_constA a) s = valorA a s"
apply(induction a)
apply (auto split: expA.split)
done

text {* (suma a1 a2) es la suma de las expresiones aritmética con
  propagación de constantes y usando las reglas de simplificación
  + 0 + a = a
  + a + 0 = a
  Por ejemplo, 
     suma (V ''x'') (suma (N 3) (N 1)) 
       = Suma (V ''x'') (N 4)" *)
     suma (N 3) (suma (V ''x'') (N 1)) 
       = Suma (N 3) (Suma (V ''x'') (N 1))    
     suma (N 3) (suma (V ''x'') (N 0)) 
       = Suma (N 3) (V ''x'')
*}
fun suma :: "expA \<Rightarrow> expA \<Rightarrow> expA" where
"suma (N i1) (N i2) = N(i1+i2)" |
"suma (N i) a = (if i=0 then a else Suma (N i) a)" |
"suma a (N i) = (if i=0 then a else Suma a (N i))" |
"suma a1 a2 = Suma a1 a2"

value "suma (V ''x'') (suma (N 3) (N 1))" 
  (* da "Suma (V ''x'') (N 4)" *)
value "suma (N 3) (suma (V ''x'') (N 1))" 
  (* da "Suma (N 3) (Suma (V ''x'') (N 1))" *)    
value "suma (N 3) (suma (V ''x'') (N 0))" 
  (* da "Suma (N 3) (V ''x'')" *)

text {* Prop.: La función suma es correcta; es decir, conserva el
  valor de las expresiones aritméticas. *}
lemma valorA_suma[simp]:
  "valorA (suma a1 a2) s = valorA a1 s + valorA a2 s"
apply (induction a1 a2 rule: suma.induct)
apply simp_all
done

text {* (simpA e) es la expresión aritmética obtenida simplificando e
  con propagación de constantes y las reglas del elemento neutro. Por
  ejemplo, 
     simpA (Suma (V ''x'') (Suma (N 3) (N 1))) 
       = Suma (V ''x'') (N 4)
     simpA (Suma (N 3) (Suma (V ''x'') (N 1))) 
       = Suma (N 3) (Suma (V ''x'') (N 1))    
     simpA (Suma (N 3) (Suma (V ''x'') (N 0))) 
       = Suma (N 3) (V ''x'')
     simpA (Suma (Suma (N 0) (N 0)) (Suma (V ''x'') (N 0)))
       = V ''x''
*}
fun simpA :: "expA \<Rightarrow> expA" where
"simpA (N n)        = N n" |
"simpA (V x)        = V x" |
"simpA (Suma a1 a2) = suma (simpA a1) (simpA a2)"

value "simpA (Suma (V ''x'') (Suma (N 3) (N 1)))" 
  (* da "Suma (V ''x'') (N 4)" *)
value "simpA (Suma (N 3) (Suma (V ''x'') (N 1)))" 
  (* da "Suma (N 3) (Suma (V ''x'') (N 1))" *)    
value "simpA (Suma (N 3) (Suma (V ''x'') (N 0)))" 
  (* da "Suma (N 3) (V ''x'')" *)
value "simpA (Suma (Suma (N 0) (N 0)) (Suma (V ''x'') (N 0)))"
  (* da "V ''x''" *)

text {* Prop.: La función simpA es correcta; es decir, conserva el
  valor de las expresiones aritméticas. *}
theorem valorA_simpA [simp]:
  "valorA (simpA a) s = valorA a s"
apply (induction a)
apply simp_all
done

end
