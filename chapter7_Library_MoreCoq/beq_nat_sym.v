(* Software Foundations *)
(* Exercice 3 stars, beq_nat_sym *)

Lemma nat_eqb_succ: forall n m: nat,
  Nat.eqb (S n) (S m) = Nat.eqb n m.
Proof.
    intros. simpl. reflexivity.
Qed.

Theorem beq_nat_sym : forall (n m : nat), Nat.eqb n m=Nat.eqb m n.
Proof.
    induction n as [|n']. induction m as [|m'].
    simpl. reflexivity.
    simpl. reflexivity.
    intros. simpl. destruct m as [|m'].
    simpl. reflexivity. rewrite nat_eqb_succ. apply IHn'.
Qed.
