(* Software Foundations *)
(* Exercice 2 stars, le_exercises *)

Inductive le: nat -> nat -> Prop :=
|le_n: forall n, le n n
|le_S: forall n m, (le n m) -> (le n (S m)).

Notation " m <= n " := (le m n).

Definition lt (n m: nat):= le (S n) m.

Notation " m < n " := (lt m n).

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
intros. induction H0.
apply H.
apply le_S. apply IHle. apply H.
Qed.

Theorem O_le_n : forall n, 0 <= n.
Proof.
intros. induction n as [|n'].
apply le_n.
apply le_S. apply IHn'.
Qed.

Theorem n_le_m_Sn_le_Sm: forall n m, n <= m -> S n <= S m.
Proof.
intros. induction H.
apply le_n.
apply le_S. apply IHle.
Qed.


Theorem Sn_le_Sm_n_le_m: forall n m, S n <= S m -> n <= m.
Proof.
intros. inversion H.
apply le_n.
apply le_trans with (m:=n)(n:=S n)(o:= m).
apply le_S. apply le_n.
apply H2.
Qed.


Theorem le_plus_l : forall a b, a <= a + b.
Proof.
intros. induction b as [|b'].
rewrite <- plus_n_O. apply le_n.
rewrite <- plus_n_Sm. apply le_S. apply IHb'.
Qed.

Lemma plus_comm: forall n m: nat, n + m = m + n.
Proof.
(* already solved see plus_swap.v *)
Admitted.


Theorem plus_lt : forall n1 n2 m, n1 + n2 < m -> n1 < m /\ n2 < m.Proof.
unfold lt.
intros. split.
(* case S n1 <= m *)
apply le_trans with (m:=S n1)(n:=S(n1+n2))(o:=m).
apply n_le_m_Sn_le_Sm. apply le_plus_l.
apply H.
(* case S n2 <= m *)
apply le_trans with (m:=S n2)(n:=S(n1+n2))(o:=m).
apply n_le_m_Sn_le_Sm. rewrite <- plus_comm. apply le_plus_l.
apply H.
Qed.

Theorem lt_S :forall n m, n < m -> n < S m.Proof.
unfold lt.
intros.
apply le_trans with (m:=S n)(n:=m)(o:=S m).
apply H.
apply le_S. apply le_n.
Qed.

Theorem ble_nat_true : forall n m,
  Nat.leb n m = true -> n <= m.
Proof.
intros. generalize dependent m. induction n as [|n'].
intros.
apply O_le_n.
intros.
destruct m as [|m'].
inversion H.
simpl in H.
apply IHn' in H.
apply n_le_m_Sn_le_Sm.
apply H.
Qed.

Lemma n_ble_nat: forall n, Nat.leb n n = true.
Proof.
intros. induction n as [|n'].
reflexivity.
simpl. apply IHn'.
Qed.

Lemma S_n_ble_m_impl_n_ble_m: forall n m, Nat.leb (S n) m = true -> Nat.leb n m = true.
Proof.
intros. generalize dependent n. induction m as [|m'].
intros.
inversion H.
intros.
simpl in H.
destruct n as [|n'].
reflexivity.
simpl. apply IHm' in H. apply H.
Qed.

Lemma n_ble_m_impl_n_ble_S_m: forall n m, Nat.leb n m = true -> Nat.leb n (S m) = true.
Proof.
intros. induction n as [|n'].
reflexivity.
simpl. apply S_n_ble_m_impl_n_ble_m. apply H.
Qed.

Theorem le_ble_nat : forall n m,
  n <= m -> Nat.leb n m = true.
Proof.
intros. induction H.
apply n_ble_nat. apply n_ble_m_impl_n_ble_S_m. apply IHle.
Qed.


Theorem ble_nat_true_trans: forall n m o,   Nat.leb n m=true -> Nat.leb m o=true -> Nat.leb n o=true.
Proof.
intros.
apply ble_nat_true in H.
apply ble_nat_true in H0.
apply le_ble_nat.
apply le_trans with (m:=n)(n:=m)(o:=o).
apply H.
apply H0.
Qed.






