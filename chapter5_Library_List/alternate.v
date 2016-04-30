(* Software Foundations *)
(* Exercice 3 stars, alternate *)

Inductive natlist: Type:=
|nil: natlist
|cons: nat -> natlist -> natlist.

Notation "[]" := nil.
Notation " x :: l" := (cons x l).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint alternate (l1 l2 : natlist) : natlist :=
match l1, l2 with
|nil , _ => l2
|_ , nil => l1
|cons h1 t1, cons h2 t2 => h1::h2::(alternate t1 t2)
end.

Example test_alternate1 : alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6]. 
Proof. reflexivity. Qed.

Example test_alternate2 : alternate [1] [4;5;6] = [1;4;5;6]. 
Proof. reflexivity. Qed.

Example test_alternate3 : alternate [1;2;3] [4] = [1;4;2;3]. 
Proof. reflexivity. Qed.

Example test_alternate4 : alternate [] [20;30] = [20;30]. 
Proof. reflexivity. Qed.

