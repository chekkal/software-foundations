(* Software Foundations *)
(* Exercice 1 star, gorgeous_plus13 *)

Inductive gorgeous : nat -> Prop :=
    g_0: gorgeous 0
    |g_3: forall n, gorgeous n -> gorgeous(3 + n)
    |g_5: forall n, gorgeous n -> gorgeous(5 + n).

Theorem gorgeous_plus13: forall n, gorgeous n -> gorgeous(13 + n).
Proof.
    intros. apply g_5. apply g_5. apply g_3. apply H.
Qed.
