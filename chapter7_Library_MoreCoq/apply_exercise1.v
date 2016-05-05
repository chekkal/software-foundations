(* Software Foundations *)
(* Exercice 3 stars, apply_exercise1 *)

Require Import Coq.Lists.List.
Import ListNotations.

SearchAbout rev.

Theorem rev_exercise1 : forall (l l' : list nat), l = rev l' -> l' = rev l.
Proof.
    intros. rewrite H. symmetry. apply rev_involutive.
Qed.
