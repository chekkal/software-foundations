(* Software Foundations *)
(* Exercice 4 stars, rev_injective *)

Inductive natlist: Type:=
|nil: natlist
|cons: nat -> natlist -> natlist.

Notation "[]" := nil.
Notation " x :: l" := (cons x l).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint snoc(l: natlist)(v:nat): natlist :=
    match l with
    |nil  => [v]
    |h::t => h::(snoc t v)
    end.

Fixpoint rev(l: natlist): natlist :=
    match l with
    |nil  => nil
    |h::t => snoc (rev t) h
    end.

Lemma rev_snoc: forall (l: natlist)(v: nat),
      rev (snoc l v) = v:: (rev l).
Proof.
    intros. induction l as [|h t].
    reflexivity.
    simpl. rewrite IHt. simpl. reflexivity.
Qed.

Lemma rev_involutive: forall l: natlist, rev (rev l) = l.
Proof.
    intros. induction l as [|h t].
    simpl. reflexivity.
    simpl. rewrite rev_snoc. rewrite IHt. reflexivity.
Qed.

Theorem rev_injective: forall l1 l2: natlist,
      rev l1 = rev l2 -> l1 = l2.
Proof.
    intros. rewrite <- rev_involutive. rewrite <- H. rewrite rev_involutive. reflexivity.
Qed.
