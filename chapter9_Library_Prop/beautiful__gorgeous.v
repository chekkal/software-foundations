(* Software Foundations *)
(* Exercice 3 stars, beautiful__gorgeous *)

Inductive gorgeous : nat -> Prop :=
g_0: gorgeous 0
|g_3: forall n, gorgeous n -> gorgeous(3 + n)
|g_5: forall n, gorgeous n -> gorgeous(5 + n).

Inductive beautiful: nat -> Prop :=
|b_0: beautiful 0
|b_3: beautiful 3
|b_5: beautiful 5
|b_sum: forall n m, beautiful n -> beautiful m -> beautiful (n +m).

Theorem gorgeous_sum: forall n m, gorgeous n -> gorgeous m -> gorgeous (n + m).
Admitted. (* Prooved in gorgeous_sum.v *)

Theorem beautiful__gorgeous : forall n,  beautiful n -> gorgeous n.
Proof.
    intros. induction H. 
    apply g_0.
    apply g_3. apply g_0.
    apply g_5. apply g_0.
    apply gorgeous_sum. apply IHbeautiful1. apply IHbeautiful2.
Qed.
