(* Software Foundations *)
(* Exercice 1 star, fst_swap_is_snd *)
Inductive natprod: Type:=
|pair: nat -> nat -> natprod.

Notation "( x , y )" := (pair x y).

Definition fst(p: natprod): nat :=
match p with
|(f,_) => f
end.

Definition snd(p: natprod): nat:=
match p with
|(_,s) => s
end.

Definition swap_pair(p: natprod): natprod :=
match p with 
|(x,y) => (y,x)
end.


Theorem fst_swap_is_snd: forall p: natprod, fst (swap_pair p) = snd p.
Proof.
    destruct p as [n m]. reflexivity.
Qed.

