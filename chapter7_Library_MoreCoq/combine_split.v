(* Software Foundations *)
(* Exercice 3 stars, combine_split *)

Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint combine {X Y : Type} (l1 : list X) (l2 : list Y) : list (X * Y) :=
  match (l1, l2) with
    | ([], _) => []
    | (_, []) => []
    | (h1 :: t1, h2 :: t2) => (h1, h2) :: (combine t1 t2)
  end.

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
    | [] => ([], [])
    | (x, y)::t =>  let t' := split t in (x::(fst t'), (y::(snd t')))
  end.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) -> combine l1 l2 = l.
Proof.
    intros. generalize dependent l2. generalize dependent l1.  generalize dependent l.
    induction l as [|[h t]].
    intros. inversion H. simpl. reflexivity.
    intros. simpl in H. inversion H. simpl. apply f_equal. apply IHl. apply surjective_pairing.
Qed.

