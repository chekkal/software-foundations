(* Software Foundations *)
(* Exercice 2 stars, beq_nat_false *)

Theorem eq_are_beq : forall n m, n = m -> Nat.eqb n m = true.
Proof.
    induction n as [|n']. induction m as [|m'].
    simpl. intros. reflexivity.
    simpl. intros. inversion H.
    intros. 
    destruct m as [|m'].
    inversion H.
    simpl. apply eq_add_S in H. apply IHn' in H. apply H.
Qed.

Theorem beq_nat_false : forall n m : nat,
  Nat.eqb n m = false -> n <> m.
Proof.
    unfold not. intros.
    apply eq_are_beq in H0. rewrite H in H0. inversion H0.
Qed.

