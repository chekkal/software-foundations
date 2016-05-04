(* Software Foundations *)
(* Exercice 1 star, advanced fold_types_different *)

(* Observe that the type of fold is parameterized by two type variables, X and Y, and the parameter f is a binary operator that takes an X and a Y and returns a Y. Can you think of a situation where it would be useful for X and Y to be different? *)

Notation "[]" := nil.
Notation "x :: y" := (cons x y)(at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint fold{X Y: Type}(f: X -> Y -> Y)(l: list X)(v: Y): Y :=
    match l with 
    |[]   => v
    |h::t => f h (fold f t v)
    end.

(* We can use fold to implement partition instead of using filter, wich ensure that we do traverse the list once, instead of twice using filter. See partition.v *)
Definition partition{X: Type}(f: X -> bool)(l: list X): list X * list X:=
      fold (fun x p => if f x then (x::fst p, snd p) else (fst p, x::snd p)) l ([],[]).


Example test_partition1: partition Nat.odd [1;2;3;4;5] = ([1;3;5],[2;4]).
Proof. reflexivity. Qed.
