(* Software Foundations *)
(* Exercice 2 stars, beq_natlist *)

Inductive natlist: Type:=
|nil: natlist
|cons: nat -> natlist -> natlist.

Notation "[]" := nil.
Notation " x :: l" := (cons x l).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
match l1,l2 with
|nil, nil => true
|nil, _   => false
|_, nil   => false
|h1::t1, h2::t2 => if (Nat.eqb h1 h2) then beq_natlist t1 t2 else false
end.

Example test_beq_natlist1 : (beq_natlist nil nil = true). Proof. reflexivity. Qed.
Example test_beq_natlist2 : beq_natlist [1;2;3] [1;2;3] = true. Proof. reflexivity. Qed.
Example test_beq_natlist3 : beq_natlist [1;2;3] [1;2;4] = false. Proof. reflexivity. Qed.

Lemma nat_eql_self: forall n: nat, Nat.eqb n n = true.
Proof.
    intros. induction n as [|n'].
    reflexivity.
    simpl. rewrite IHn'. reflexivity.
Qed.

Theorem beq_natlist_refl: forall l: natlist, beq_natlist l l = true.
Proof.
    intros. induction l as [|h t].
    reflexivity.
    simpl. rewrite nat_eql_self. rewrite IHt. reflexivity.
Qed.
