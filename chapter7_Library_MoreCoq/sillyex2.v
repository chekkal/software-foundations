(* Software Foundations *)
(* Exercice 1 star, sillyex2 *)

Require Import Coq.Lists.List.
Import ListNotations.

Theorem sillyex2: forall (X : Type) (x y z : X) (l j : list X),
      x :: y :: l = [] -> y :: l = z :: j -> x = z.
Proof.
    intros. inversion H.
Qed.

