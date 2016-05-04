Require Import Coq.Lists.List.
Import ListNotations.

Theorem silly1_using_apply : forall (n m o p : nat), n=m -> [n;o] = [n;p] -> [n;o] = [m;p].
Proof.
    intros.
    rewrite <- H.
    apply H0.
Qed.

Theorem silly1_using_rewrite : forall (n m o p : nat), n=m -> [n;o] = [n;p] -> [n;o] = [m;p].
Proof.
    intros.
    rewrite <- H.
    rewrite H0. reflexivity.
Qed.
