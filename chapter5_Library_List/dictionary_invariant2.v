(* Software Foundations *)
(* Exercice 1 star, dictionary_invariant2 *)

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

Theorem dictionary_invariant2: forall (d: dictionary)(m n o: nat),
      Nat.eqb m n = false -> find m d = find m (insert n o d).
Proof.
    intros. induction d as [|k' v' d'].
    simpl. rewrite H. reflexivity.
    simpl.  rewrite H. reflexivity.
Qed.

End Dictionary.
