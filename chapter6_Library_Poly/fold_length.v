(* Software Foundations *)
(* Exercice 2 stars, fold_length *)

Notation "[]" := nil.
Notation "x :: y" := (cons x y)(at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint fold{X Y: Type}(f: X -> Y -> Y)(l: list X)(v: Y): Y :=
    match l with 
    |[]   => v
    |h::t => f h (fold f t v)
    end.

Definition fold_length{X: Type}(l: list X): nat :=
      fold (fun _ n => S n) l O.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct: forall X (l: list X),
      fold_length l = length l.
Proof.
    intros. unfold fold_length.
    induction l as [|h t].
    simpl. reflexivity.
    simpl. rewrite IHt. reflexivity.
Qed.
