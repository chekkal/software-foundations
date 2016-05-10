(* Software Foundations *)
(* Exercice 1 star, override_shadow *)

Definition override{X: Type}(f: nat -> X) k v :=
      fun (k': nat) => if Nat.eqb k k' then  v else f k'.

Theorem override_shadow : forall (X :Type) x1 x2 k1 k2 (f : nat -> X),
    (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
    intros. unfold override.
    destruct Nat.eqb.
    reflexivity.
    reflexivity.
Qed.

