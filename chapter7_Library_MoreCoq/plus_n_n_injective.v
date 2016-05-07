(* Software Foundations *)
(* Exercice 3 stars, plus_n_n_injective *)
(* SearchAbout "S".

Require Import Logic.

Definition eq_S := f_equal S.*)

Theorem plus_n_n_injective: forall n m, n+n=m+m -> n = m.
Proof.
intros n. induction n as [|n'].
destruct m as [|m'].
  reflexivity.
  intros H. inversion H.
destruct m as [|m'].
  intros H. simpl in H. inversion H.
  intros H. apply eq_S. apply IHn'. simpl in H. apply eq_add_S in H. rewrite <- plus_n_Sm in H. rewrite <- plus_n_Sm in H. apply eq_add_S in H. apply H.
Qed.

Theorem plus_n_n_injective': forall n m, n+n=m+m -> n = m.
Proof.
intros n. induction n as [|n'].
destruct m as [|m'].
  simpl. reflexivity.
  simpl. intros contra. inversion contra.
destruct m as [|m'].
  simpl. intros contra. inversion contra.
  intros H. apply eq_S. apply IHn'. rewrite plus_Sn_m in H. rewrite plus_Sn_m in H.
  apply eq_add_S in H. rewrite <- plus_n_Sm in H. rewrite <- plus_n_Sm in H. apply eq_add_S in H. apply H.
Qed.
