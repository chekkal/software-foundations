(* Software Foundations *)
(* Exercise: 2 star, or_distributes_over_and *)

Inductive and(P Q: Prop): Prop:=
  conj: P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q): type_scope.

Definition iff(P Q: Prop): Prop:= (P -> Q) /\ (Q->P).

Notation "P <-> Q" := (iff P Q)(at level 95, no associativity): type_scope.

Inductive or(P Q: Prop): Prop :=
| or_introl: P -> or P Q
| or_intror: Q -> or P Q.

Notation "P \/ Q" := (or P Q): type_scope.

Theorem or_distributes_over_and_1 : forall P Q R : Prop, P\/(Q/\R)->(P\/Q)/\(P\/R).
Admitted. (* Already prooved *)
Theorem or_distributes_over_and_2 : forall P Q R : Prop, (P\/Q)/\(P\/R)->P\/(Q/\R).
Admitted. (* Already prooved *)

Theorem or_distributes_over_and: forall P Q R : Prop,
P \/(Q /\R) <-> (P \/ Q) /\ (P \/ R).
Proof.
    intros. split.
    apply or_distributes_over_and_1.
    apply or_distributes_over_and_2.
Qed.
