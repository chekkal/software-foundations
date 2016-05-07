(* Software Foundations *)
(* Exercice 2 stars, beq_nat_true *)

Theorem beq_nat_true : forall n m, Nat.eqb n m = true -> n = m.
Proof.
    intros n. induction n as [|n'].
    destruct m as [|m'].
    intros eq. reflexivity.
    intros contra. inversion contra.
    destruct m as [|m'].
    intros contra. inversion contra.
    simpl. intros H. apply f_equal. apply IHn'. apply H.
Qed.
