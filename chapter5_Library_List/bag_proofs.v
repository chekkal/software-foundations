(* Software Foundations *)
(* Exercice 3 stars, bag_proofs *)

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

Theorem count_member_nonzero: forall (s: bag),
  Nat.leb 1 (count 1 (1::s)) = true.
Proof.
    intros. induction s as[|s'].
    reflexivity.
    simpl. reflexivity.
Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
    match s with
    |nil => nil
    |h::t => if (Nat.eqb h v) then t else h::(remove_one v t)
    end.

Lemma ble_n_Sn: forall n: nat, Nat.leb n (S n) = true.
Proof.
    intros. induction n as [|n'].
    reflexivity.
simpl. rewrite IHn'. reflexivity.
Qed.

Theorem remove_decreases_count: forall (s: bag),
      Nat.leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
    intros. induction s as [|h t].
    reflexivity.
    destruct h as [|h'].
    simpl. rewrite ble_n_Sn. reflexivity.
    simpl. rewrite IHt. reflexivity.
Qed.
