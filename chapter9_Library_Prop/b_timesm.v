(* Software Foundations *)
(* Exercice 3 stars, b_timesm *)

Inductive beautiful: nat -> Prop :=
|b_0: beautiful 0
|b_3: beautiful 3
|b_5: beautiful 5
|b_sum: forall n m, beautiful n -> beautiful m -> beautiful (n +m).

Theorem b_timesm: forall n m, beautiful n -> beautiful (m * n).
Proof.
    intros. induction m as [|m'].
    simpl. apply b_0.
    simpl. apply b_sum with (n:=n)(m:=m'*n).
    apply H.
    apply IHm'.
Qed.
