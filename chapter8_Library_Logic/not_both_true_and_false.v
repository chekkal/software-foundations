(* Software Foundations *)
(* Exercice 1 star, not_both_true_and_false *)

Theorem not_both_true_and_false: forall P: Prop, ~(P /\ ~ P).
Proof.
    intros.
    unfold not.
    intros.
    inversion H.
    apply H1 in H0.
    apply H0.
Qed.
