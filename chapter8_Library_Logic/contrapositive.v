(* Software Foundations *)
(* Exercice 2 stars, contrapositive *)

Lemma implies_trans: forall P Q R: Prop,
  (P->Q)->(Q->R)->(P->R).
Proof.
    intros.
    apply H in H1.
    apply H0 in H1.
    apply H1.
Qed.

Theorem contrapositive: forall P Q: Prop, 
  (P -> Q) -> (~Q -> ~ P).
Proof.
    intros.
    unfold not in H0.
    unfold not.
    apply implies_trans with Q.
    apply H.
    apply H0.
Qed.
