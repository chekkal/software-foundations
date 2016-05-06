(* Software Foundations *)
(* Exercice 2 stars, practice *)

Theorem beq_nat_0_l: forall n, Nat.eqb O n = true -> n = O.
Proof.
    intros. destruct n as [|n'].
    reflexivity.
    inversion H.
Qed.

Theorem beq_nat_0_r: forall n, Nat.eqb n O = true -> n = O.
Proof.
    intros. destruct n as [|n'].
    reflexivity.
    inversion H.
Qed.
