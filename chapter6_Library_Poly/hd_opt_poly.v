(* Software Foundations *)
(* Exercice 1 star, hd_opt_poly *)

Inductive list(X: Type): Type :=
|nil: list X
|cons: X -> list X -> list X.

Arguments nil {X}.
Arguments cons {X} _ _.

Notation "[]" := nil.
Notation "h :: t" := (cons h t)(at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Inductive option(X: Type): Type:=
|Some: X -> option X
|None: option X.

Arguments Some {X} _.
Arguments None {X}.

Definition hd_opt{X: Type}(l: list X): option X:=
    match l with
    |[]   => None
    |h::_ => Some h
    end.

Check @hd_opt.

Example test_hd_opt1: hd_opt ([1;2]) = Some 1. Proof. reflexivity. Qed.
Example test_hd_opt2: hd_opt ([[1];[2]]) = Some ([1]). Proof. reflexivity. Qed.
