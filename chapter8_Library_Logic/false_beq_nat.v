(* Software Foundations *)
(* Exercice 2 stars, false_beq_nat *)

Theorem ex_falso_quodlibet : forall (P:Prop), False -> P.
Proof.
intros. inversion H.
Qed.

Theorem beq_nat_true : forall n m, Nat.eqb n m = true -> n = m.
Admitted. (* see chapter7_Library_MoreCoq/beq_nat_true.v *)

Theorem false_beq_nat : forall n m : nat,
  n <> m -> Nat.eqb n m = false.
Proof.
    unfold not. intros. destruct (Nat.eqb) eqn: Heqb.
    apply ex_falso_quodlibet. apply H.
    apply beq_nat_true in Heqb. apply Heqb.
    reflexivity.
Qed.
