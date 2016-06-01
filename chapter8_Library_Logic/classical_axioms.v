(* Software Foundations *)
(* Exercice 5 stars, classical_axioms *)

Definition peirce  := forall P Q: Prop, ((P -> Q ) -> P) -> P.
Definition classic := forall P:Prop, ~~ P -> P.
Definition excluded_middle := forall  P:Prop, P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop, ~(~P /\ ~Q) -> P \/ Q.
Definition implies_to_or := forall P Q:Prop, (P -> Q) -> (~P \/ Q).

Theorem peirce_imp_classic: peirce -> classic.
Proof.
    compute. (* we can also use: unfold peirce. unfold classic. unfold not. *)
intros. apply H with False. intros. apply H0 in H1. inversion H1.
Qed.

Theorem classic_imp_excluded_middle: classic -> excluded_middle.

Proof.
    compute. intros. apply H. intros. apply H0. right. intros. 
    apply H0. left. apply H1.
Qed.

Theorem excluded_middle_imp_de_morgan_not_and_not: excluded_middle -> de_morgan_not_and_not.
Proof.
    unfold excluded_middle. unfold de_morgan_not_and_not.
intros.
destruct (H P). left. apply H1.
destruct (H Q). right. apply H2.
destruct H0. split. apply H1. apply H2.
Qed.

Theorem de_morgan_not_and_not_imp_implies_to_or: de_morgan_not_and_not -> implies_to_or.
Proof.
    compute. intros. 
    apply H. intros. destruct H1. apply H1. intros. apply H2. apply H0. apply H3. 
Qed.

Theorem implies_to_or_imp_peirce: implies_to_or -> peirce.
Proof.
    Abort. (* Couldn't complet the cycle *)

(* not required just wanted to keep the proof *)
Theorem pierce_eq_classic: peirce <-> classic.
Proof.
    unfold peirce, classic.
    unfold not.
    split.
    (* peirce -> classic *)
    intros. apply H with False.
    intros.
    apply H0 in H1. inversion H1.
    (* peirce <- classic *)
    intros. apply H. intros. apply H1. apply H0. intros. apply H1 in H2. inversion H2. 
Qed.
