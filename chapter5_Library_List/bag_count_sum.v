(* Software Foundation *)
(* Exercice 3 stars, bag_count_sum *)

Inductive natlist: Type:=
|nil: natlist
|cons: nat -> natlist -> natlist.

Notation "[]" := nil.
Notation " x :: l" := (cons x l).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition bag := natlist.

Fixpoint count (v: nat) (s: bag) : nat :=
    match s with
    |nil     => O
    |h :: t => if (Nat.eqb v h) then S(count v t) else count v t
    end.

Fixpoint append(l1 l2: natlist): natlist :=
    match l1 with
    |nil        => l2
    |cons h1 t1 => h1 :: (append t1 l2)
    end.

Definition sum : bag -> bag -> bag := append.

Lemma if_lemma: forall (b: bool)(n m p: nat),
      (if b then n + p else m + p) = (if b then n else m) + p.
Proof.
    intros. destruct b.
    reflexivity.
    reflexivity.
Qed.

Lemma plus_succ: forall n m: nat, S(n+m) = S n + m.
Proof.
    intros. induction n as [|n'].
    reflexivity.
    simpl. rewrite IHn'. reflexivity.
Qed.

Theorem bag_count_sum: forall (l1 l2: natlist)(v: nat),
      count v (sum l1 l2) = (count v l1) + (count v l2).
Proof.
    intros. induction l1 as [|h1 t1].
    simpl. reflexivity.
    simpl. rewrite IHt1. rewrite plus_succ. rewrite if_lemma. reflexivity.
Qed.

