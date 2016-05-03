(* Software Foundations *)
(* Exercice 2 stars, flat_map *)

Inductive list(X: Type): Type :=
|nil: list X
|cons: X -> list X -> list X.

Arguments nil {X}.
Arguments cons {X} _ _.

Notation "[]" := nil.
Notation "x :: y" := (cons x y)(at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint app{X: Type}(l1 l2: list X): list X:=
    match l1 with
    |[] => l2
    |h::t => h::(app t l2)
    end.

Fixpoint flat_map{X Y: Type}(f: X -> list Y)(l: list X): list Y :=
    match l with
    |[]   => []
    |h::t => app (f h) (flat_map f t)
    end.

Example test_flat_map1: flat_map (fun n => [n;n;n]) [1;5;4] = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

