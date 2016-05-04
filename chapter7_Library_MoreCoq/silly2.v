Require Import Coq.Lists.List.
Import ListNotations.

Theorem silly2_using_apply : forall (n m o p : nat), n=m ->
    (forall (q r : nat),q =r -> [q;o]=[r;p])-> [n;o] = [m;p].
Proof.
    intros. apply H0. apply H.
Qed.

Theorem silly2_using_rewrite : forall (n m o p : nat), n=m ->
    (forall (q r : nat),q =r -> [q;o]=[r;p])-> [n;o] = [m;p].
Proof.
    intros. rewrite H. rewrite (H0 m m). reflexivity. reflexivity.
Qed.
