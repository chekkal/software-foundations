(* Software Foundations *)
(* Exercice 3 stars, partition *)

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

Inductive prod(X Y: Type): Type :=
|pair: X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y): type_scope.

Definition fst{X Y: Type}(p: X*Y):= match p with (x,_) => x end.
Definition snd{X Y: Type}(p: X*Y):= match p with (_,y) => y end.

Definition notb(b: bool): bool:=
    match b with
    |true  => false
    |false => true
    end.

Definition partition{X: Type}(test: X -> bool)(l: list X): list X * list X :=
    (filter test l, filter (fun x => notb (test x)) l).

Example test_partition1: partition Nat.odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.
