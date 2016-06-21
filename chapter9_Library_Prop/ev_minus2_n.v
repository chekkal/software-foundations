(* Software Foundations *)
(* Exercice 1 star, ev_minus2_n *)

Inductive ev: nat -> Prop :=
|ev_0: ev 0
|ev_ss: forall n: nat, ev n -> ev (S (S n)).


Theorem ev_minus2_n: forall n,
ev n -> ev (pred (pred n)).

Proof.
    intros.
    destruct H.
    simpl. apply ev_0.
    simpl. apply H.
Qed.

