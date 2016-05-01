(* Software Foundations *)
(* Excercice 3 stars, list_exercises *)

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

Theorem app_nil_end: forall l: natlist, l ++ [] = l.
Proof.
    intros. induction l as [|h t].
    reflexivity.
    simpl. rewrite IHt. reflexivity.
Qed.

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

Lemma rev_snoc: forall (l:natlist)(v: nat), rev (snoc l v) = v::rev(l).
Proof.
    intros. induction l as [|h t].
    reflexivity.
    simpl. rewrite IHt. simpl. reflexivity.
Qed.

Theorem rev_involutive: forall l: natlist, rev(rev l) = l.
Proof.
    intros. induction l as [|h t].
    reflexivity.
    simpl. rewrite rev_snoc. rewrite IHt. reflexivity.
Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist, (l1 ++l2)++l3 =l1 ++(l2 ++l3).
Proof.
    intros. induction l1 as [|h t].
    reflexivity.
    simpl. rewrite IHt. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++(l2 ++(l3 ++l4))=((l1 ++l2)++l3)++l4.
Proof.
    intros.
    rewrite app_assoc. induction l1 as [|h t].
    reflexivity.
    simpl. rewrite IHt. reflexivity.
Qed.

Theorem snoc_append: forall (l: natlist)(v: nat), snoc l v = l ++ [v].
Proof.
    intros. induction l as [|h t].
    reflexivity.
    simpl. rewrite IHt. reflexivity.
Qed.

Lemma snoc_app_two_list: forall (l1 l2: natlist)(v: nat), snoc(l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
    intros. induction l1 as [|h1 t1].
    reflexivity.
    simpl. rewrite IHt1. reflexivity.
Qed.

Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
    intros. induction l1 as [|h1 t1].
    simpl. rewrite app_nil_end. reflexivity.
    simpl. rewrite IHt1. rewrite snoc_app_two_list. reflexivity.
Qed.

Fixpoint nonzeros(l: natlist): natlist :=
match l with
|nil  => nil
|0::t => nonzeros t
|h::t =>h::(nonzeros t)
end.

Lemma nonzeros_app: forall l1 l2: natlist, nonzeros(l1++l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
    intros. induction l1 as [|h t].
    reflexivity.
    destruct h as [|h'].
    simpl. rewrite IHt. reflexivity.
    simpl. rewrite IHt. reflexivity.
Qed.
