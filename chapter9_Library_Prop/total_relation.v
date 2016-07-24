(* Software Foundations *)
(* Exercice 2 stars, total_relation *)

Inductive total_relation: nat -> nat -> Prop :=
|tr: forall n m, total_relation n m.



