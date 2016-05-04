(* Software Foundations *)
(* Exercice 2 stars, override_neq *)

Definition constfun{X:Type}(v: X): nat -> X:= fun (n: nat) => v.

Definition override{X :Type}(f: nat -> X)(k: nat)(x: X) :=
      fun k' => if (Nat.eqb k k') then x else f k'.


Theorem override_neq: forall (X: Type) x1 x2 k1  k2 (f: nat -> X),
      f k1 = x1 -> Nat.eqb k2 k1 = false -> (override f k2 x2) k1 = x1.

Proof.
    intros.
    unfold override.
    rewrite H0.
    rewrite H.
    reflexivity.
Qed.
