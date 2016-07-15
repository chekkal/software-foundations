(* Software Foundations *)
(* Exercice 5 stars, palindrome_converse *)

(***** PROOF NOT COMPLETE ******)

Require Import Coq.Lists.List.
Import ListNotations.

Inductive pal{X: Type}: (list X) -> Prop :=
|pal_nil: pal []
|pal_singleton: forall x, pal [x]
|pal_sides: forall (l: list X)(x: X), pal l -> pal (x::(l++[x])).

Lemma tail_append: forall (X: Type)(l1 l2: list X),
  tail (l1 ++ l2) = tail l1 ++ l2.
Admitted.

Lemma n_inf_succ: forall n: nat, n <= n + 1.
Admitted.

Lemma rev_lemma1: forall (X: Type)(x: X)(l: list X), l = tl (rev l) ++ [x] -> l = rev l.
Admitted.

Lemma rev_lemma2: forall (X: Type)(l: list X), l = rev l -> tl l = rev (tl l).
Admitted.

Lemma palindrome_converse_lemma: forall (X: Type)(n: nat)(l: list X),
    length l <= n -> l = rev l -> pal l.
Proof.
  intros X.
  induction n as [|n'].
  intros. inversion H. apply length_zero_iff_nil in H2. rewrite H2. apply pal_nil.
  induction l as [|h t].
  intros. apply pal_nil.
  intros.
  apply f_equal with (f:=tail(A:=X)) in H0.
  simpl in H0. rewrite tail_append in H0. rewrite H0. apply pal_sides.
  apply IHn'.
  apply f_equal with (f:= length(A:=X)) in H0.
  simpl in H.
  apply Le.le_S_n in H.
  rewrite app_length in H0. simpl in H0. rewrite H0 in H.
  apply PeanoNat.Nat.le_trans with (n:=length (tl (rev t)))(m:=length (tl (rev t)) + 1)(p:=n').
  apply n_inf_succ.
  apply H.
  apply rev_lemma1 in H0. rewrite <- H0. apply rev_lemma2. apply H0.
Qed.


