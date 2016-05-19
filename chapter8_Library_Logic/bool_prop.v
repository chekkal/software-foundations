(* Software Foundations *)
(* Exercise: 2 star, bool_prop *)

Inductive and(P Q: Prop): Prop:=
  conj: P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q): type_scope.

Definition iff(P Q: Prop): Prop:= (P -> Q) /\ (Q->P).

Notation "P <-> Q" := (iff P Q)(at level 95, no associativity): type_scope.

Inductive or(P Q: Prop): Prop :=
| or_introl: P -> or P Q
| or_intror: Q -> or P Q.

Notation "P \/ Q" := (or P Q): type_scope.

Theorem andb_prop: forall p q,
  andb p q = true -> (p = true) /\ (q = true).
Proof.
    intros. split. destruct p.
    reflexivity.
    simpl in H. inversion H.
    destruct q.
    reflexivity.
    compute in H. destruct p. inversion H. inversion H.
Qed.

Theorem andb_true_intro : forall b c, b = true /\ c = true -> andb b c = true.
Proof.
    intros. inversion H as [Hb Hc].
    rewrite Hb. rewrite Hc. reflexivity.
Qed.

Theorem andb_false : forall b c, andb b c = false -> b = false \/ c = false.
Proof.
    intros. destruct b. destruct c.
    simpl in H. inversion H.
    apply or_intror. reflexivity.
    apply or_introl. reflexivity.
Qed.

Theorem orb_prop : forall b c, orb b c = true -> b = true \/ c = true.
Proof.
    intros. destruct b. destruct c.
    apply or_introl. reflexivity.
    apply or_introl. reflexivity.
    destruct c.
    apply or_intror. reflexivity.
    simpl in H. inversion H.
Qed.

Theorem orb_false_elim : forall b c, orb b c = false -> b = false /\ c = false.
Proof.
    intros. destruct b. destruct c.
    simpl in H. inversion H.
    simpl in H. inversion H.
    destruct c.
    simpl in H. inversion H.
    split. reflexivity. reflexivity.
Qed.

