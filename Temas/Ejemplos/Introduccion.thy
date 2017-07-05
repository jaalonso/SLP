theory Introduccion
imports Main
begin

section {* Comentarios *}

text {* Nota. Esto es un comentario. *}

section {* Inferencia de tipo *}

text {* Nota. (term t) muestra el tipo del término t. *}

term "True"          (* da "True" :: "bool" *)
term "False"         (* da "False" :: "bool" *)
term "true"          (* da "true" :: "'a" *)
term "True \<and> False"  (* da "True \<and> False" :: "bool" *)
term "True \<and> false"  (* da "True \<and> false" :: "bool" *)

text {* Nota:
  + Para ver el tipo de un término, poner el curso sobre él y pulsar
    Ctrl.
  + Para ver la definición de un término, poner el curso sobre él, 
    pulsar Ctrl y pulsar el botón izquierdo del ratón. *}

section {* Evaluación de términos *}

text {* Nota. (value t) muestra el valor del término t. *}

value "True \<and> False" (* da "False" :: "bool" *)
value "True \<and> P"     (* da "P" :: "bool" *)

section {* Ejemplos de sobrecarga *}

text {* Los números y las operaciones aritméticas están sobrecargados. *}

term  "2 + 1"         (* da "2 + 1" :: "'a" *)
value "2 + 1"         (* da "1 + 1 + 1" :: "'a *)
term  "2 + (1::nat)"  (* da "2 + 1" :: "nat" *)
value "2 + (1::nat)"  (* da "Suc (Suc (Suc 0))" :: "nat" *)
value "2 + (1::int)"  (* da "3" :: "int" *)
value "2 - (7::int)"  (* da "- 5" :: "int" *)

term "2"              (* da "2" :: "'a" *)
term "op +"           (* da "op +" :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" *)

section {* Ejemplos de errores de tipo *}

text {* 
  Nota. Al evaluar 
     term "True + False"
  da el siguiente mensaje de error
     Type unification failed: No type arity bool :: plus
     
     Type error in application: incompatible operand type
     
     Operator:  op + :: ??'a \<Rightarrow> ??'a \<Rightarrow> ??'a
     Operand:   True :: bool
  
  Nota. Al evaluar
     term "2 + True"
  da el siguiente mensaje de error
     Type unification failed: No type arity bool :: numeral
     
     Type error in application: incompatible operand type
     
     Operator:  op + 2 :: ??'a \<Rightarrow> ??'a
     Operand:   True :: bool
  
  Nota. Al evaluar 
     term "True \<and> 2"
  da el siguiente mensaje de error
     Type unification failed: No type arity bool :: numeral
     
     Type error in application: incompatible operand type
     
     Operator:  op \<and> True :: bool \<Rightarrow> bool
     Operand:   2 :: ??'a
*}

end
