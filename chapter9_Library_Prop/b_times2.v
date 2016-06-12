(* Software Foundations *)
(* Exercice 2 stars, b_times2 *)

Inductive beautiful: nat -> Prop :=
|b_0: beautiful 0
|b_3: beautiful 3
|b_5: beautiful 5
|b_sum: forall n m, beautiful n -> beautiful m -> beautiful (n +m).

Theorem b_times2: forall n, beautiful n -> beautiful (2 * n).
Proof.
    intros. unfold "*". rewrite <- plus_n_O. apply b_sum with (n:=n)(m:=n).
    apply H.
    apply H.
Qed.
