(* Software Foundations *)
(* Exercice 2 stars, filter_even_gt7 *)

Inductive list(X: Type): Type :=
|nil: list X
|cons: X -> list X -> list X.

Arguments nil {X}.
Arguments cons {X} _ _.

Notation "[]" := nil.
Notation "x :: y" := (cons x y)(at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint filter{X:Type}(f: X -> bool)(l: list X): list X:=
    match l with
    |[]   => []
    |h::t => if f h then h::(filter f t) else (filter f t)
    end.


Definition filter_even_gt7(l: list nat): list nat :=
      filter (fun n => andb (Nat.even n) (Nat.ltb 7 n)) l.

Example test_filter_even_gt7_1: filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2: filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.
