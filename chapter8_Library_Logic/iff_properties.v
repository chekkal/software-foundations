(* Software Foundations *)
(* Exercise: 1 star, iff_properties *)

Inductive and(P Q: Prop): Prop:=
  conj: P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q): type_scope.

Definition iff(P Q: Prop): Prop:= (P -> Q) /\ (Q->P).

Notation "P <-> Q" := (iff P Q)(at level 95, no associativity): type_scope.

Theorem iff_implies : forall P Q : Prop, (P <-> Q) -> P -> Q.
Proof.
    intros. inversion H as [HPQ HQP]. apply HPQ. apply H0.
    (*intros. apply H. apply H0.*)
Qed.

Theorem iff_sym : forall P Q :Prop, (P <-> Q)->(Q <-> P).
Proof.
    intros. inversion H. split. apply H1. apply H0.
Qed.


Theorem iff_refl : forall P : Prop, P <-> P.
Proof.
    intros. split. intros. apply H. intros. apply H.
Qed.

Theorem iff_trans : forall P Q R : Prop, (P <-> Q)->(Q <-> R)->(P <-> R).
Proof.
    intros. inversion H as [HPQ HQP]. inversion H0 as [HQR HRQ].
    split.
    intros HP. apply HQR. apply HPQ. apply HP.
    intros HR. apply HQP. apply HRQ. apply HR.
Qed.

