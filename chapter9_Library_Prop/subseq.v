(* Software Foundations *)
(* Exercice 4 stars, subseq *)

Require Import Coq.Lists.List.
Import ListNotations.

Inductive subseq: (list nat)->(list nat)-> Prop :=
|seq_nil: forall l, subseq [] l
|seq_1: forall n l1 l2, subseq l1 l2 -> subseq l1 (n::l2) 
|seq_2: forall n l1 l2, subseq l1 l2 -> subseq (n::l1) (n::l2).


Theorem subseq_refl: forall l, subseq l l.
Proof.
    intros. induction l as [|h t].
    apply seq_nil.
    apply seq_2. apply IHt.
Qed.

Theorem subseq_append: forall l1 l2 l3, subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
    intros. induction H.
    apply seq_nil.
    simpl. apply seq_1. apply IHsubseq.
    simpl. apply seq_2. apply IHsubseq.
Qed.

Theorem subseq_transitive: forall l1 l2 l3, subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
    intros.
    induction H0. 
    inversion H. apply seq_nil.
    apply seq_1. apply IHsubseq. apply H.
Abort.
