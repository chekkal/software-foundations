(* Software Foundations *)
(* Exercice 3 stars, ev_ev__ev *)

Inductive ev: nat -> Prop :=
|ev_0: ev 0
|ev_ss: forall n: nat, ev n -> ev (S (S n)).

Theorem ev_ev__ev : forall n m, ev (n + m) -> ev n -> ev m.
Proof.
    intros.
    induction H0.
    apply H.
    inversion H. apply IHev in H2. apply H2.
Qed.

