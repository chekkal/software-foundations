(* Software Foundations *)
(* Exercice 3 stars, map_rev *)

Inductive list(X: Type): Type :=
|nil: list X
|cons: X -> list X -> list X.

Arguments nil {X}.
Arguments cons {X} _ _.

Notation "[]" := nil.
Notation "x :: y" := (cons x y)(at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint map{X Y: Type}(f: X -> Y)(l: list X): list Y:=
    match l with 
    |nil  => nil
    |h::t => (f h)::(map f t)
    end.

Fixpoint snoc{X: Type}(l: list X)(v: X): list X:=
    match l with
    |[]   => [v]
    |h::t => h::(snoc t v)
    end.

Fixpoint rev{X: Type}(l: list X): list X:=
    match l with
    |[]   => []
    |h::t => snoc (rev t) h
    end.

Lemma map_snoc: forall (X Y: Type)(f: X -> Y)(l: list X)(v: X),
      map f (snoc l v) = snoc (map f l) (f v).
Proof.
    intros. induction l as [|h t].
    simpl. reflexivity.
    simpl. rewrite IHt. reflexivity.
Qed.

Theorem map_rev: forall (X Y: Type)(f: X -> Y)(l: list X),
      map f (rev l) = rev (map f l).
Proof.
    intros. induction l as [|h t].
    simpl. reflexivity.
    simpl. rewrite map_snoc. rewrite IHt. reflexivity.
Qed.
