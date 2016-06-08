(* Software Foundations *)
(* Exercice 1 star, double_even *)

Fixpoint double (n: nat): nat :=
match n with
|O => O
|S n' => S(S (double n'))
end.

Inductive ev: nat -> Prop :=
|ev_0: ev 0
|ev_ss: forall n: nat, ev n -> ev (S (S n)).

Theorem double_even: forall n: nat, ev (double n).
Proof.
    induction n as [|n'].
    simpl. apply ev_0.
    simpl. apply ev_ss. apply IHn'.
Qed.


