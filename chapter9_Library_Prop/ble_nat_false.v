(* Software Foundations *)
(* Exercice 2 stars, ble_nat_false *)

Inductive le: nat -> nat -> Prop :=
|le_n: forall n, le n n
|le_S: forall n m, (le n m) -> (le n (S m)).

Notation " m <= n " := (le m n).

Lemma S_n_le_O_false: forall n, ~ (S n <= 0).
Proof.
intros. unfold not.
intros. inversion H.
Qed.


Theorem Sn_le_Sm_n_le_m: forall n m, S n <= S m -> n <= m.
(* Already prooved in le_exercices *)
Admitted.

Theorem ble_nat_false: forall n m, Nat.leb n m = false -> ~(n <= m).
Proof.
intros. generalize dependent m. induction n as [|n'].
intros. inversion H.
destruct m as [|m'].
intros. apply S_n_le_O_false.
intros. simpl in H. apply IHn' in H.
unfold not. intros. apply Sn_le_Sm_n_le_m in H0. unfold not in H. apply H in H0.
inversion H0.
Qed.