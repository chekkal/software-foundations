(* Software Foundations *)
(* Exercice 3 stars, filter_exercise *)

Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint filter{X: Type}(f: X -> bool)(l: list X):=
match l with
|[]   => []
|h::t => if (f h) then h::(filter f t) else (filter f t)
end.

Theorem filter_exercise : forall (X : Type)(test : X -> bool)(x : X)(l lf : list X),
filter test l = x :: lf -> test x = true.
Proof.
    intros. generalize dependent l. induction l as [|h t].
    simpl. intros. inversion H.
    intros. simpl in H. destruct (test h) eqn: th.
    inversion H. rewrite H1 in th. apply th.
    apply IHt in H. apply H.
Qed.
