(* Software Foundations *)
(* Exercice 3 stars, apply_with_exercise *)

Theorem transitive_eq: forall(X:Type) (n m p: X), n=m -> m=p -> n=p.
Proof.
    intros. rewrite H. rewrite H0. reflexivity.
Qed.

Definition minustwo := fun n => n - 2.

Example trans_eq_exercice: forall (n m o p: nat),
      m = (minustwo o) -> (n+p) = m -> (n+p)=(minustwo o).
Proof.
    intros. apply transitive_eq with m. apply H0. apply H.
Qed.
