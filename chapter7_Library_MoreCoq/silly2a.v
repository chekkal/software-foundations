Require Import Coq.Lists.List.
Import ListNotations.

Theorem silly2a_using_apply : forall (n m : nat), (n,n) = (m,m)->
    (forall (q r : nat),(q,q)=(r,r) -> [q]=[r]) -> [n] = [m].
Proof.
    intros. apply H0. apply H.
Qed.

Theorem silly2a_using_rewrite : forall (n m : nat), (n,n) = (m,m)->
    (forall (q r : nat),(q,q)=(r,r) -> [q]=[r]) -> [n] = [m].
Proof.
    intros. rewrite (H0 n m). reflexivity. rewrite H. reflexivity.
Qed.
