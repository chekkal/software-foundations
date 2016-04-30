(* Software Foundations *)
(*Exercice 1 star snd_fst_is_swap *)
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


Theorem snd_fst_is_swap: forall p: natprod, (snd p, fst p) = swap_pair p.
Proof.
    destruct p as [n m]. reflexivity.
Qed.
