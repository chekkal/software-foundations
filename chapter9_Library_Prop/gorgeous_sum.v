(* Software Foundations *)
(* Exercice 2 stars, gorgeous_sum *)

Inductive gorgeous : nat -> Prop :=
    g_0: gorgeous 0
    |g_3: forall n, gorgeous n -> gorgeous(3 + n)
    |g_5: forall n, gorgeous n -> gorgeous(5 + n).

Theorem gorgeous_sum: forall n m, gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
    intros. induction H. induction H0.
    simpl. apply g_0.
    simpl. apply g_3. apply H0.
    simpl. apply g_5. apply H0.
    apply g_3 with (n:= n+m). apply IHgorgeous.
    apply g_5 with (n:= n+m). apply IHgorgeous.
Qed.
