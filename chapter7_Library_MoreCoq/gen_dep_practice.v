(* Software Foundations *)
(* Exercice 3 stars, gen_dep_practice *)
Fixpoint index{X: Type}(n: nat)(l: list X):=
    match l with
    |nil      => None
    |cons h t => if Nat.eqb n 0 then Some h else index (pred n) t
    end.

Theorem index_after_last: forall (n : nat) (X : Type) (l : list X ),
    length l =n  ->index n l = None.
Proof.
    intros.
    generalize dependent n.
    induction l as [|l'].
    intros. simpl. reflexivity.
    intros. simpl. destruct n as [|n'].
    simpl. inversion H.
    simpl. apply IHl. simpl in H. inversion H. reflexivity.
Qed.
