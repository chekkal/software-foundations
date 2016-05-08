(* Software Foundations *)
(* Exercice 3 stars, app_length_cons *)

Require Import Coq.Lists.List.
Import ListNotations.

Theorem app_length_cons : forall (X : Type) (l1 l2 : list X) (x : X) (n : nat), 
      length (l1 ++(x :: l2))=n -> S (length (l1 ++ l2)) = n.
Proof.
    intros X l1. induction l1 as [|h1 t1].
    intros. generalize dependent n.
    simpl. intros. apply H.
    simpl. induction n as [|n'].
    intros contra. inversion contra.
    intros H. inversion H. apply IHt1 in H1. rewrite H1. rewrite H. reflexivity.
Qed.
