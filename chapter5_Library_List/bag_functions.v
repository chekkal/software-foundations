(* Software Foundations *)
(* Exercice 3 stars, bag_functions *)
Inductive natlist: Type:=
|nil: natlist
|cons: nat -> natlist -> natlist.

Notation "[]" := nil.
Notation " x :: l" := (cons x l).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition bag := natlist.

Fixpoint count (v: nat) (s: bag) : nat :=
match s with
|nil     => O
|h :: t => if (Nat.eqb v h) then S(count v t) else count v t
end.

Example test_count1 : count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.

Example test_count2 : count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Fixpoint append(l1 l2: natlist): natlist :=
match l1 with
|nil        => l2
|cons h1 t1 => h1 :: (append t1 l2)
end.

Definition sum : bag -> bag -> bag := append.

Example test_sum1 : count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := v :: s.

Example test_add1 : count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.

Example test_add2 : count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.
Definition member (v:nat) (s:bag) : bool := 
match (count v s) with 
|O => false 
| _ => true 
end.

Example test_member1 : member 1 [1;4;1] = true. 
Proof. reflexivity. Qed.

Example test_member2 : member 2 [1;4;1] = false. 
Proof. reflexivity. Qed.

