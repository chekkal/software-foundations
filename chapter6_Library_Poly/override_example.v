(* Software Foundations *)
(* Exercice 1 star, override_example *)

Definition constfun{X:Type}(v: X): nat -> X:= fun (n: nat) => v.

Definition override{X :Type}(f: nat -> X)(k: nat)(x: X) :=
      fun k' => if (Nat.eqb k k') then x else f k'.

Theorem override_example: forall b: bool,
      (override (constfun b) 3 true) 2 = b.
Proof.
    intros. compute. reflexivity.
Qed.

