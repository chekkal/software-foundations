(* Software Foundations *)
(*Exercise: 1 star, optional proj2 *)

Inductive and(P Q: Prop): Prop:=
  conj: P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q): type_scope.
Theorem proj2 : forall P Q : Prop, P /\ Q -> Q.
Proof.
    intros P Q H.
    inversion H.
    apply H1.
Qed.

