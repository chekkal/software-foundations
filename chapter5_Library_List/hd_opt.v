(* Software Foundations *)
(* Exercice 2 stars, hd_opt *)

Inductive natlist: Type:=
|nil: natlist
|cons: nat -> natlist -> natlist.

Notation "[]" := nil.
Notation " x :: l" := (cons x l).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Inductive natoption: Type :=
|Some: nat -> natoption
|None: natoption.

Definition hd_opt(l: natlist): natoption :=
match l with
|nil  => None
|h::_ => Some h
end.

Example test_hd_opt1: hd_opt [] = None.
Proof. reflexivity. Qed.
Example test_hd_opt2: hd_opt [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_opt3: hd_opt [5;6] = Some 5.
Proof. reflexivity. Qed.
