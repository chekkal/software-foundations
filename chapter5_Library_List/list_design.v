(* Software Foundations *)
(* Exercice 2 stars, list_design *)

Inductive natlist: Type:=
|nil: natlist
|cons: nat -> natlist -> natlist.

Notation "[]" := nil.
Notation " x :: l" := (cons x l).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint append(l1 l2: natlist): natlist :=
match l1 with
|nil        => l2
|cons h1 t1 => h1 :: (append t1 l2)
end.

Notation "l1 ++ l2" := (append l1 l2).

Fixpoint snoc(l: natlist)(v:nat): natlist :=
match l with
|nil  => [v]
|h::t => h::(snoc t v)
end.

(* Write down a non-trivial theorem involving cons (::), snoc, and app (++).
Prove it *)

Theorem list_design: forall (l1 l2: natlist)(v: nat),
  l1 ++ (cons v l2) = (snoc l1 v) ++ l2.
Proof.
    intros. induction l1 as [|h1 t1].
    simpl. reflexivity.
    simpl. rewrite IHt1. reflexivity.
Qed.
