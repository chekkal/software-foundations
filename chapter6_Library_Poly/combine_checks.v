(* Software Foundations *)
(* Exercie 1 star, combine_checks *) 
Inductive list(X: Type): Type :=
|nil: list X
|cons: X -> list X -> list X.

Arguments nil {X}.
Arguments cons {X} _ _.

Notation "[]" := nil.
Notation "h :: t" := (cons h t)(at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..)(at level 60, right associativity).

Inductive prod(X Y: Type): Type:=
|pair: X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y ) " := (pair x y).
Notation "X * Y" := (prod X Y): type_scope.

Fixpoint combine{X Y: Type}(l1: list X)(l2: list Y): list (X*Y):=
    match l1, l2 with
    |[],_ => []
    |_,[] => []
    |(h1::t1),(h2::t2) => (h1,h2)::(combine t1 t2)
    end.


Check combine.
Check @combine.

Check [1;2].
Check [true;false].
Check (combine (cons 1 (cons  2 nil)) (cons false (cons false (cons true (cons true nil))))).
Eval compute in (combine ([1;2]) ([false;false;true;true])).
