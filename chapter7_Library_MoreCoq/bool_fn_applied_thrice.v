(* Software Foundations *)
(* Exercice 2 stars, bool_fn_applied_thrice *)

Theorem bool_fn_applied_thrice : 
  forall(f :bool->bool)(b:bool), f (f (f b)) = f b.
Proof.
    intros. destruct b.
    destruct (f true) eqn: fth.
    rewrite fth. rewrite fth. reflexivity.
    destruct (f false) eqn: ffh.
    rewrite fth. reflexivity.
    rewrite ffh. reflexivity.
    destruct (f false) eqn: ffh.
    destruct (f true) eqn: fth.
    rewrite fth. reflexivity.
    rewrite ffh. reflexivity.
    rewrite ffh. rewrite ffh. reflexivity.
Qed.
