(* Software Foundations *)
(* Exercice 2 stars, override_same *)

Definition override {X: Type}(f: nat -> X) k v:=
  fun k' => if Nat.eqb k k' then v else f k'.

Lemma beq_nat_true: forall n m: nat, Nat.eqb n m = true -> n = m.
Admitted.

Theorem override_same : forall (X: Type) x1 k1 k2 (f: nat -> X ), 
  f k1 = x1 -> (override f k1 x1) k2 = f k2.
Proof.
    intros. unfold override.
    destruct (Nat.eqb k1 k2) eqn: eqek1k2.
    apply beq_nat_true in eqek1k2. rewrite <- eqek1k2. rewrite H. reflexivity.
    reflexivity.
Qed.
