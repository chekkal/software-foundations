(* Software Foundations *)
(* Exercice 1 star, option_elim_hd *)

Inductive natlist: Type:=
|nil: natlist
|cons: nat -> natlist -> natlist.

Notation "[]" := nil.
Notation " x :: l" := (cons x l).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Inductive natoption: Type :=
|Some: nat -> natoption
|None: natoption.

Definition option_elim (default: nat)(o: natoption): nat :=
match o with
|None   => default
|Some v => v
end.

Definition hd (default: nat) (l: natlist): nat :=
match l with
|nil  => default
|h::_ => h
end.

Definition hd_opt(l: natlist): natoption :=
match l with
|nil  => None
|h::_ => Some h
end.

Theorem option_elim_hd: forall (l: natlist)(default: nat),
  hd default l = option_elim default (hd_opt l).
Proof.
intros. destruct l as [|h t].
reflexivity.
reflexivity.
Qed.
