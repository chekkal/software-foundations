(* Software Foundations *)
(* Exercice 2 star, ev_sum *)

Inductive ev: nat -> Prop :=
|ev_0: ev 0
|ev_ss: forall n: nat, ev n -> ev (S (S n)).

Theorem ev_sum: forall n m, ev n -> ev m -> ev (n + m).
    intros n m HEVn HEVm. induction HEVn. induction HEVm.
    simpl. apply ev_0.
    simpl. apply ev_ss.
    apply HEVm.
    simpl. apply ev_ss. apply IHHEVn.
Proof.


