theory EjT3A
imports "../Temas/Ejemplos/ExpA"
begin 

section "Ejercicio 3.1: La función simp_constA simplifica"

text {*
  ----------------------------------------------------------------------
  Ejercicio 3.1.1. Una expresión aritmética está simplificada si no
  contiene niguna subexpresión que sea una suma de dos números.
  
  Definir la función
     simplificada :: "expA \<Rightarrow> bool" where
  tal que (simplificada a) se verifica si la expresión aritmética a está
  simplificada. Por ejemplo, 
     simplificada (Suma (V ''x'') (N 5))              = True
     simplificada (Suma (V ''x'') (Suma (N 2) (N 5))) = False
     simplificada (Suma (N 2) (Suma (V ''x'') (N 5))) = True
  ------------------------------------------------------------------- *}

fun simplificada :: "expA \<Rightarrow> bool" where
"simplificada (N _) = True" |
"simplificada (V _) = True" |
"simplificada (Suma (N _) (N _)) = False" |
"simplificada (Suma a1 a2) = (simplificada a1 \<and> simplificada a2)"

value "simplificada (Suma (V ''x'') (N 5))"
  (* da True *)
value "simplificada (Suma (V ''x'') (Suma (N 2) (N 5)))"
  (* da False *)
value "simplificada (Suma (N 2) (Suma (V ''x'') (N 5)))"
  (* da True *)

text {*
  ----------------------------------------------------------------------
  Ejercicio 3.1.2. Demostrar que para cualquier expresión aritmética a, 
  
  ------------------------------------------------------------------- *}

lemma "simplificada (simp_constA a)"
apply (induction a rule: simplificada.induct)
apply (auto split: expA.split)
done

text{*
This proof needs the same @{text "split:"} directive as the correctness proof of
@{const simp_constA}. This increases the chance of nontermination
of the simplifier. Therefore @{const simplificada} should be defined purely by
pattern matching on the left-hand side,
without @{text case} expressions on the right-hand side.
\endexercise


\exercise
In this exercise we verify constant folding for @{typ expA}
where we sum up all constants, even if they are not next to each other.
For example, @{term "Plus (N 1) (Plus (V x) (N 2))"} becomes
@{term "Plus (V x) (N 3)"}. This goes beyond @{const asimp}.
Below we follow a particular solution strategy but there are many others.

First, define a function @{text sumN} that returns the sum of all
constants in an expression and a function @{text zeroN} that replaces all
constants in an expression by zeroes (they will be optimized away later):
*}

fun sumN :: "expA \<Rightarrow> int" where
(* your definition/proof here *)

fun zeroN :: "expA \<Rightarrow> expA" where
(* your definition/proof here *)

text {*
Next, define a function @{text sepN} that produces an arithmetic expression
that adds the results of @{const sumN} and @{const zeroN}. Prove that
@{text sepN} preserves the value of an expression.
*}

definition sepN :: "expA \<Rightarrow> expA" where
(* your definition/proof here *)

lemma aval_sepN: "aval (sepN t) s = aval t s"
(* your definition/proof here *)

text {*
Finally, define a function @{text full_asimp} that uses @{const asimp}
to eliminate the zeroes left over by @{const sepN}.
Prove that it preserves the value of an arithmetic expression.
*}

definition full_asimp :: "expA \<Rightarrow> expA" where
(* your definition/proof here *)

lemma aval_full_asimp: "aval (full_asimp t) s = aval t s"
(* your definition/proof here *)



text{*
\endexercise


\exercise\label{exe:subst}
Substitution is the process of replacing a variable
by an expression in an expression. Define a substitution function
*}

fun subst :: "vname \<Rightarrow> expA \<Rightarrow> expA \<Rightarrow> expA" where
(* your definition/proof here *)

text{*
such that @{term "subst x a e"} is the result of replacing
every occurrence of variable @{text x} by @{text a} in @{text e}.
For example:
@{lemma[display] "subst ''x'' (N 3) (Plus (V ''x'') (V ''y'')) = Plus (N 3) (V ''y'')" by simp}

Prove the so-called \concept{substitution lemma} that says that we can either
substitute first and evaluate afterwards or evaluate with an updated state:
*}

lemma subst_lemma: "aval (subst x a e) s = aval e (s(x := aval a s))"
(* your definition/proof here *)

text {*
As a consequence prove that we can substitute equal expressions by equal expressions
and obtain the same result under evaluation:
*}
lemma "aval a1 s = aval a2 s
  \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
(* your definition/proof here *)

text{*
\endexercise

\exercise
Take a copy of theory @{theory AExp} and modify it as follows.
Extend type @{typ expA} with a binary constructor @{text Times} that
represents multiplication. Modify the definition of the functions @{const aval}
and @{const asimp} accordingly. You can remove @{const simp_constA}.
Function @{const asimp} should eliminate 0 and 1 from multiplications
as well as evaluate constant subterms. Update all proofs concerned.
*}

text{*
\endexercise

\exercise
Define a datatype @{text expA2} of extended arithmetic expressions that has,
in addition to the constructors of @{typ expA}, a constructor for
modelling a C-like post-increment operation $x{++}$, where $x$ must be a
variable. Define an evaluation function @{text "aval2 :: expA2 \<Rightarrow> state \<Rightarrow> val \<times> state"}
that returns both the value of the expression and the new state.
The latter is required because post-increment changes the state.

Extend @{text expA2} and @{text aval2} with a division operation. Model partiality of
division by changing the return type of @{text aval2} to
@{typ "(val \<times> state) option"}. In case of division by 0 let @{text aval2}
return @{const None}. Division on @{typ int} is the infix @{text div}.
*}

text{*
\endexercise

\exercise
The following type adds a @{text LET} construct to arithmetic expressions:
*}

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

text{* The @{const LET} constructor introduces a local variable:
the value of @{term "LET x e\<^sub>1 e\<^sub>2"} is the value of @{text e\<^sub>2}
in the state where @{text x} is bound to the value of @{text e\<^sub>1} in the original state.
Define a function @{const lval} @{text"::"} @{typ "lexp \<Rightarrow> state \<Rightarrow> int"}
that evaluates @{typ lexp} expressions. Remember @{term"s(x := i)"}.

Define a conversion @{const inline} @{text"::"} @{typ "lexp \<Rightarrow> expA"}.
The expression \mbox{@{term "LET x e\<^sub>1 e\<^sub>2"}} is inlined by substituting
the converted form of @{text e\<^sub>1} for @{text x} in the converted form of @{text e\<^sub>2}.
See Exercise~\ref{exe:subst} for more on substitution.
Prove that @{const inline} is correct w.r.t.\ evaluation.
\endexercise


\exercise
Show that equality and less-or-equal tests on @{text expA} are definable
*}

definition Le :: "expA \<Rightarrow> expA \<Rightarrow> bexp" where
(* your definition/proof here *)

definition Eq :: "expA \<Rightarrow> expA \<Rightarrow> bexp" where
(* your definition/proof here *)

text{*
and prove that they do what they are supposed to:
*}

lemma bval_Le: "bval (Le a1 a2) s = (aval a1 s \<le> aval a2 s)"
(* your definition/proof here *)

lemma bval_Eq: "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
(* your definition/proof here *)

end
