(* Software Foundations *)
(* Exercice 3 stars, bag_more_functions *)

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

Definition member (v:nat) (s:bag) : bool := 
match (count v s) with 
|O => false 
| _ => true 
end.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
match s with 
|nil => nil
|h::t => if (Nat.eqb h v) then t else h::(remove_one v t)
end.

Example test_remove_one1 : count 5 (remove_one 5 [2;1;5;4;1]) = 0. Proof. reflexivity. Qed.
Example test_remove_one2 : count 5 (remove_one 5 [2;1;4;1]) = 0. Proof. reflexivity. Qed.
Example test_remove_one3 : count 4 (remove_one 5 [2;1;4;5;1;4]) = 2. Proof. reflexivity. Qed.
Example test_remove_one4 : count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1. Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag := 
match s with 
|nil => nil
|h::t => if (Nat.eqb h v) then remove_all v t else h::(remove_all v t)
end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0. Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0. Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2. Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0. Proof. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool := 
match s1 with
|nil  => true
|h::t => if (member h s2) then subset t (remove_one h s2) else false
end.
Example test_subset1 : subset [1;2] [2;1;4;1] = true. Proof. reflexivity. Qed.
Example test_subset2 : subset [1;2;2] [2;1;4;1] = false. Proof. reflexivity. Qed.
