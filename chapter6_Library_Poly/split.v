(* Software Foundations *)
(* Exercie 2 star, split *) 
Inductive list(X: Type): Type :=
|nil: list X
|cons: X -> list X -> list X.

Arguments nil {X}.
Arguments cons {X} _ _.

Notation "[]" := nil.
Notation "h :: t" := (cons h t)(at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Inductive prod(X Y: Type): Type:=
|pair: X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y ) " := (pair x y).
Notation "X * Y" := (prod X Y): type_scope.

Definition fuse{X Y: Type}(e: (X*Y))(p: (list X)*(list Y)): (list X)*(list Y):=
    match e,p with (x,y), (px, py) => (x::px, y::py) end.

Fixpoint split{X Y: Type}(l: list (X*Y)): (list X)*(list Y) :=
    match l with 
    |[]       => ([],[])
    |(x,y)::t => fuse (x,y) (split t)
    end.

Example test_split: split ([(1,false);(2,false)]) = ([1;2],[false;false]).
Proof.
    reflexivity.
Qed.
