(* Software Foundations *)
(* Exercice 3 stars, bag_theorem *)

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

Definition add (v:nat) (s:bag) : bag := v :: s.

Lemma self_eq: forall n: nat, Nat.eqb n n = true.
Proof.
    intros. induction n as [|n'].
    reflexivity.
    simpl. rewrite IHn'. reflexivity.
Qed.

Theorem bag_theorem: forall (s: bag) (n: nat), count n (add n s) = S(count n s).
Proof.
    intros. destruct s.
    simpl. rewrite self_eq. reflexivity.
    simpl. rewrite self_eq. reflexivity.
Qed.
