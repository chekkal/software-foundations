(* Software Foundations *)
(* Exercice 1 star, SSSSev__even *)

Inductive ev: nat -> Prop :=
|ev_0: ev 0
|ev_ss: forall n: nat, ev n -> ev (S (S n)).


Theorem SSSSev__even : forall n, ev (S (S (S (S n)))) -> ev n.
Proof.
    intros.
    inversion H.
    inversion H1.
    apply H3.
Qed.


