theory EjT2C
imports Main
begin


text{*
\endexercise


\exercise\label{exe:arbol0}
Define a datatype @{text arbol0} of binary arbol skeletons which do not store
any information, neither in the inner nodes nor in the leaves.
Define a function that counts the number of all nodes (inner nodes and leaves)
in such a arbol:
*}

fun nodes :: "arbol0 \<Rightarrow> nat" where
(* your definition/proof here *)

text {*
Consider the following recursive function:
*}

fun explode :: "nat \<Rightarrow> arbol0 \<Rightarrow> arbol0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Nodo t t)"

text {*
Experiment how @{text explode} influences the size of a binary arbol
and find an equation expressing the size of a arbol after exploding it
(\noquotes{@{term [source] "nodes (explode n t)"}}) as a function
of @{term "nodes t"} and @{text n}. Prove your equation.
You may use the usual arithmetic operations including the exponentiation
operator ``@{text"^"}''. For example, \noquotes{@{prop [source] "2 ^ 2 = 4"}}.

Hint: simplifying with the list of theorems @{thm[source] algebra_simps}
takes care of common algebraic properties of the arithmetic operators.
\endexercise
*}

text{*

\exercise
Define arithmetic expressions in one variable over integers (type @{typ int})
as a data type:
*}

datatype exp = Var | Const int | Add exp exp | Mult exp exp

text{*
Define a function @{text eval} that evaluates an expression at some value:
*}

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
(* your definition/proof here *)

text{*
For example, @{prop"eval (Add (Mult (Const 2) Var) (Const 3)) i = 2*i+3"}.

A polynomial can be represented as a list of coefficients, starting with
the constant. For example, @{term "[4, 2, -1, 3::int]"} represents the
polynomial $4 + 2x - x^2 + 3x^3$.
Define a function @{text evalp} that evaluates a polynomial at a given value:
*}

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
(* your definition/proof here *)

text{*
Define a function @{text coeffs} that transforms an expression into a polynomial.
This will require auxiliary functions.
*}

fun coeffs :: "exp \<Rightarrow> int list" where
(* your definition/proof here *)

text{*
Prove that @{text coeffs} preserves the value of the expression:
*}

theorem evalp_coeffs: "evalp (coeffs e) x = eval e x"
(* your definition/proof here *)

text{*
Hint: consider the hint in Exercise~\ref{exe:arbol0}.
\endexercise
*}

end
