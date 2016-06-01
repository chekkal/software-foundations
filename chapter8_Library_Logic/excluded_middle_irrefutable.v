(* Software Foundations *)
(* Exercice 3 stars, excluded_middle_irrefutable *)

Axiom excluded_middle: forall  P:Prop, P \/ ~P.

Theorem excluded_middle_irrefutable: forall (P:Prop), ~~(P \/ ~ P).
Proof.
    compute. intros. apply H. destruct H. apply excluded_middle.
Qed.
