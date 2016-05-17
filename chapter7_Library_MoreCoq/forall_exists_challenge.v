(* Software Foundations *)
(* Exercise: 4 stars, advanced forall_exists_challenge *)

Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint forallb{X: Type}(p: X -> bool)(l: list X): bool :=
match l with
|[]   => true
|h::t => if (p h) then forallb p t else false
end.

Example forallb_test1: forallb Nat.odd [1;3;5;7;9] = true. Proof. reflexivity. Qed.
Example forallb_test2: forallb negb [false;false] = true. Proof. reflexivity. Qed.
Example forallb_test3: forallb Nat.even [0;2;4;5] = false. Proof. reflexivity. Qed.
Example forallb_test4: forallb (Nat.eqb 5) []= true. Proof. reflexivity. Qed.

Fixpoint existsb{X: Type}(p: X -> bool)(l: list X): bool :=
match l with
|[] => false
|h::t => if p h then true else existsb p t
end.

Example existsb_test1: existsb (Nat.eqb 5) [0;2;3;6] = false. Proof. reflexivity. Qed.
Example existsb_test2: existsb (andb true) [true;true;false] = true. Proof. reflexivity. Qed.
Example existsb_test3: existsb Nat.odd [1;0;0;0;0;3] = true. Proof. reflexivity. Qed.
Example existsb_test4: existsb Nat.even [] = false. Proof. reflexivity. Qed.

Definition existsb'{X: Type}(p: X -> bool)(l: list X): bool := negb (forallb (fun b => negb (p b)) l).

Theorem both_definitions_existsb_same: forall (X: Type)(p: X-> bool)(l: list X),
  existsb p l = existsb' p l.
Proof.
    intros. generalize dependent l. induction l as [|h t].
    compute. reflexivity.
    unfold existsb'. simpl. destruct (p h) eqn: phv.
    simpl. reflexivity.
    simpl. unfold existsb' in IHt. apply IHt.
Qed.
