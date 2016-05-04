(* Software Foundations *)
(* Exercice 3 stars, fold_map *)

Notation "[]" := nil.
Notation "x :: y" := (cons x y)(at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint fold{X Y: Type}(f: X -> Y -> Y)(l: list X)(v: Y): Y :=
    match l with 
    |[]   => v
    |h::t => f h (fold f t v)
    end.

Fixpoint map{X Y: Type}(f: X -> Y)(l: list X): list Y:=
    match l with
    |[]   => []
    |h::t => (f h)::(map f t)
    end.

Definition fold_map{X Y: Type}(f: X -> Y)(l: list X): list Y :=
      fold (fun e acc => (f e)::acc) l [].

Theorem fold_map_correct: forall X Y (l: list X)(f: X -> Y),
      fold_map f l = map f l.
Proof.
    intros. unfold fold_map.
    induction l as [|h t].
    simpl. reflexivity.
    simpl. rewrite IHt. reflexivity.
Qed.
