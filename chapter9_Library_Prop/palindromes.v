(* Software Foundations *)
(* Exercice 4 stars, palindromes *)

Require Import Coq.Lists.List.
Import ListNotations.

Inductive pal{X: Type}: (list X) -> Prop :=
|pal_nil: pal []
|pal_singleton: forall x, pal [x]
|pal_sides: forall (l: list X)(x: X), pal l -> pal (x::(l++[x])).

Lemma eq1: forall (X: Type) (x:X) (l1: list X)(l2: list X), l1=l2 -> x::l1 = x::l2.
Proof.
    intros. rewrite H. reflexivity.
Qed.

Lemma simpl_list_op1: forall (X: Type)(l1 l2: list X)(x1 x2: X),
  x1::l1 ++ l2 ++ [x2] = x1::(l1 ++ l2)++[x2].
Proof.
    intros. apply eq1. rewrite app_assoc_reverse. reflexivity.
Qed.


Theorem pal_l_app_rev: forall (X: Type) (l: list X), pal (l ++ rev l).
Proof.
    intros. induction l.
    simpl. apply pal_nil.
    simpl.
    assert (a :: l ++ rev l ++ [a] = a :: (l ++ rev l) ++ [a]) as assConsH.
    apply simpl_list_op1.
    remember (l++rev l) as lrevl.
    rewrite assConsH.
    apply pal_sides. apply IHl.
Qed.

Theorem pal_l_eq_rev: forall (X: Type)(l: list X), pal l -> l = rev l.
Proof.
    intros. induction H.
    reflexivity.
    reflexivity.
    simpl. rewrite rev_app_distr. rewrite <- IHpal. simpl. reflexivity.
Qed.
