(* Software Foundations *)
(* Exercice 1 star, sillyex1 *)

Require Import Coq.Lists.List.
Import ListNotations.

Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = z :: j -> 
    y :: l = x :: j -> 
    x = y.
Proof.
    intros. inversion H0. reflexivity.
Qed.
