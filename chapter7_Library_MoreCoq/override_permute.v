(* Software Foundations *)
(* Exerice 3 stars, override_permute *)

Definition override{X: Type}(f: nat -> X) k x:=
  fun k' => if Nat.eqb k k' then x else f k'.

Lemma nat_eqb_true_are_same: forall n m, Nat.eqb m n = true -> n = m.
Admitted. (* Already Proved *)

Lemma nat_eqb_refl: forall n, Nat.eqb n n = true.
Proof.
    intros. induction n as [|n'].
    reflexivity.
    simpl. apply IHn'.
Qed.

Theorem override_permute : forall (X :Type) x1 x2 k1 k2 k3 (f : nat -> X),
Nat.eqb k2 k1 = false -> 
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
    intros. unfold override.
    destruct (Nat.eqb k1 k3) eqn: eqbk1k3.
    destruct (Nat.eqb k2 k3) eqn: eqbk2k3.
    apply nat_eqb_true_are_same in eqbk1k3.
    apply nat_eqb_true_are_same in eqbk2k3.
    rewrite eqbk1k3 in eqbk2k3.
    rewrite eqbk2k3 in H. rewrite nat_eqb_refl in H.
    inversion H.
    reflexivity.
    destruct (Nat.eqb k2 k3) eqn: eqbk2k3.
    reflexivity.
    reflexivity.
Qed.
