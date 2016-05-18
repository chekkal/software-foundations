(* Software Foundations *)
(* Exercise: 2 star, and_assoc *)

Inductive and(P Q: Prop): Prop:=
  conj: P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q): type_scope.
Theorem and_assoc : forall P Q R : Prop, P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
    intros P Q R H. inversion H as [HP [HQ HR]].
    split.
    split.
    apply HP.
    apply HQ.
    apply HR.
Qed.
