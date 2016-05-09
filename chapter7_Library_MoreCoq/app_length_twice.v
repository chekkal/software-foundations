(* Software Foundations *)
(* Exercice 4 stars, app_length_twice *)

Require Import Coq.Lists.List.
Import ListNotations.


Lemma length_app_cons: forall (X: Type)(l1 l2: list X) (n: X),
  length(l1 ++ n::l2) = S(length (l1 ++ l2)).
Proof.
intros. generalize dependent n. generalize dependent l2.
induction l1 as [|h1 t1].
simpl. reflexivity.
simpl. intros. rewrite IHt1. reflexivity.
Qed.

Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X), 
  length l =n -> length (l ++ l) = n +n.
Proof.
intros. generalize dependent n.
induction l as [|h t].
simpl. intros. destruct n as [|n'].
  reflexivity.
  inversion H.
intros. simpl. rewrite length_app_cons. simpl in H. destruct n as [|n'].
  inversion H.
  apply eq_add_S in H. apply IHt in H. rewrite H. simpl. apply f_equal. apply plus_n_Sm.
Qed.

