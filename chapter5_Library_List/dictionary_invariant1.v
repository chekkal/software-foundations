(* Software Foundations *)
(* Exercice 1 star, dictionary_invariant1 *)

Module Dictionary.
Inductive natoption: Type :=
|Some: nat -> natoption
|None: natoption.

Inductive dictionary: Type :=
|empty: dictionary
|record: nat -> nat -> dictionary -> dictionary.

Definition insert(k v: nat)(d: dictionary): dictionary :=
  (record k v d).


Fixpoint find(key: nat)(d: dictionary): natoption :=
match d with
|empty         => None
|record k v d' => if (Nat.eqb key k) then Some v else find key d'
end.

Lemma nat_eq_self: forall n: nat, Nat.eqb n n = true.
Proof.
    intros. induction n as [|n'].
    reflexivity.
    simpl. rewrite IHn'. reflexivity.
Qed.

Theorem dictionary_invariant1: forall (d: dictionary)(k v: nat),
  find k (insert k v d) = Some v.
Proof.
    intros. induction d as [|k' v' d'].
    simpl. rewrite nat_eq_self. reflexivity.
    simpl. rewrite nat_eq_self. reflexivity.
Qed.

End Dictionary.
