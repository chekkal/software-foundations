(* Software Foundations *)
(* Exercice 3 stars, gen_dep_practice_more *) 

Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint snoc{X: Type}(l: list X)(v: X):=
    match l with
    |nil  => [v]
    |h::t => h::(snoc t v)
    end.

Theorem length_snoc''': forall (n : nat) (X : Type)(v : X) (l : list X),
    length l = n -> length (snoc l v) = S n.
Proof.
    intros.
    generalize dependent n.
    induction l as [|h t].
    destruct n as [|n'].
    intros. simpl. reflexivity.
    intros contra. simpl in contra. inversion contra.
    simpl. intros. apply f_equal. 
    induction n as [|n'].
    inversion H.
    inversion H. apply IHt in H1. rewrite <- H in H1. apply H1.
Qed.
