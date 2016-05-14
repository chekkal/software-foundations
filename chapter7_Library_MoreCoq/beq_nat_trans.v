(* Software Foundations *)
(* Exercice 3 stars, beq_nat_trans *)

Lemma nat_eqb_true_are_same: forall n m, Nat.eqb m n = true -> n = m.
Proof.
    induction n as [|n']. induction m as [|m'].
    reflexivity.
    intros. inversion H.
    intros. destruct m as [|m'].
    inversion H.
    simpl in H. apply IHn' in H.
    apply f_equal. apply H.
Qed.

Theorem beq_nat_trans : forall n m p,
Nat.eqb n m = true -> Nat.eqb m p = true -> Nat.eqb n p = true.
Proof.
    intros. generalize dependent n. induction n as [|n'].
    intros. apply nat_eqb_true_are_same in H. rewrite H in H0. apply H0.
    destruct m as [|m'].
    intros. inversion H.
    intros. apply nat_eqb_true_are_same in H0. rewrite <- H0 in H. apply H.
Qed.

