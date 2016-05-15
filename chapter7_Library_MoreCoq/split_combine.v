(* Software Foundations *)
(* Exercice 3 stars, split_combine *)

Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint comibine{X Y: Type}(l1: list X) (l2: list Y): list (X*Y):= 
match l1,l2 with
|[],_             => []
|_,[]             => []
|(h1::t1),(h2::t2) => (h1,h2)::(combine t1 t2)
end.

Fixpoint split{X Y: Type}(l: list (X*Y)): (list X) *(list Y) :=
match l with
|[]       => ([],[])
|(x,y)::t => let r := (split t) in (x::(fst r), y::(snd r))
end.


Definition split_combine_statement : Prop := forall (X Y: Type) (l1: list X) (l2: list Y),
  length l1 = length l2 -> split (combine l1 l2) = (l1,l2).

Theorem split_combine : split_combine_statement.
Proof.
    unfold split_combine_statement.
    induction l1 as [|h1 t1]. induction l2 as [|h2 t2].
    reflexivity.
    intros. simpl in H. inversion H.
    intros.
    destruct l2.
    simpl in H. inversion H.
    simpl. inversion H. apply IHt1 in H1.
    rewrite H1. simpl. reflexivity.
Qed.
