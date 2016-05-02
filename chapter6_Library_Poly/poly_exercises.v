(* Software Foundations *)
(* Exercice 2 stars, poly_exercises *)

Inductive list(X: Type): Type:=
|nil: list X
|cons: X -> list X -> list X.

Arguments nil {X}.
Arguments cons {X} _ _.

Notation "[]":= nil.
Notation "h :: t":= (cons h t) (at level 60, right associativity).
Notation "[ x ; .. ; y ]" :=(cons x .. (cons y nil) ..) (at level 60, right associativity).

Fixpoint repeat{X: Type}(n: X)(count: nat): list X:=
    match count with
    |O        => []
    |S count' => n::(repeat n count')
    end.

Example test_repeat1: repeat true 2 = [true; true].
Proof. reflexivity. Qed.

Fixpoint app {X:Type}(l1 l2: list X): list X :=
    match l1 with
    |[]     => l2
    |h1::t1 => h1::(app t1 l2)
    end.

Theorem nil_app: forall (X: Type)(l: list X), app [] l = l.
Proof.
    reflexivity.
Qed.

Fixpoint snoc{X: Type}(s: list X)(v: X) :=
    match s with 
    |[]   => [v]
    |h::t => h::(snoc t v)
    end.

Fixpoint rev{X: Type}(l: list X): list X :=
    match l with
    |[]   => []
    |h::t => snoc (rev t) h
    end.

Theorem rev_snoc: forall (X: Type)(v: X)(s: list X),
      rev (snoc s v) = v :: (rev s).
Proof.
    intros. induction s as [|s'].
    reflexivity.
    simpl. rewrite IHs. simpl. reflexivity.
Qed.

Theorem rev_involutive: forall (X: Type)(l: list X),
      rev (rev l) = l.
Proof.
    intros. induction l as [|h t].
    reflexivity.
    simpl. rewrite rev_snoc. rewrite IHt. reflexivity.
Qed.

Notation "l1 ++ l2" := (app l1 l2).

Theorem snoc_with_append: forall (X: Type)(l1 l2: list X)(v: X),
      snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
    intros. induction l1 as [|h1 t1].
    simpl. reflexivity.
    simpl. rewrite IHt1. reflexivity.
Qed.
