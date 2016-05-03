(* Software Foundations *)
(* Exercice 2 stars, optional implicit_args *)

Inductive list(X: Type): Type :=
|nil: list X
|cons: X -> list X -> list X.

Arguments nil {X}.
Arguments cons {X} _ _.

Notation "[]" := nil.
Notation "x :: y" := (cons x y)(at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint filter(X:Type)(f: X -> bool)(l: list X): list X:=
    match l with
    |[]   => []
    |h::t => if f h then h::(filter _ f t) else (filter _ f t)
    end.

Check filter.

Fixpoint map(X Y: Type)(f: X -> Y)(l: list X): list Y:=
    match l with
    |nil  => nil
    |h::t => (f h)::(map _ _ f t)
    end.

Check map.

