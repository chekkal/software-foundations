(* Software Foundations *)
(* Exercice 3 stars binary_commute *)
Inductive bin: Type :=
|zero: bin
|twice: bin -> bin
|one_more_twice: bin -> bin.

Fixpoint increment (b: bin): bin :=
    match b with
    |zero             => one_more_twice zero
    |twice n          => one_more_twice n
    |one_more_twice n => twice (increment n)
    end.

Fixpoint binary_to_unary(b: bin): nat :=
    match b with
    |zero             => 0
    |twice n          => 2*(binary_to_unary n)
    |one_more_twice n => 2*(binary_to_unary n) + 1
    end.

Lemma plus_0_r: forall n: nat, n + 0 = n.
Proof.
(* already solved see mult_comm.v *)
Admitted.

Lemma plus_swap: forall n m p: nat, n + (m+p) = m + (n +p).
Proof.
    (*already solved see plus_swap.v file *)
Admitted.

Lemma plus_succ: forall n m: nat, n + S m = S(n+m).
Proof.
(* already solved see plus_swap.v *)
Admitted.

Lemma plus_comm: forall n m: nat, n + m = m + n.
Proof.
(* already solved see mult_comm.v *)
Admitted.

Theorem binary_commute: forall (b: bin), 
      binary_to_unary(increment(b))= binary_to_unary(b)+1.

Proof.
    intros. induction b as [|b1|b2].
    (*case 1*)
    simpl. reflexivity.
    (*case 2*)
    simpl. reflexivity.
    (*case 3*)
    simpl. rewrite IHb2. 
    remember (binary_to_unary b2) as m. rewrite plus_0_r. rewrite plus_0_r.
    rewrite plus_succ. rewrite plus_succ. rewrite plus_succ. rewrite plus_succ.
    rewrite plus_0_r. rewrite plus_0_r. rewrite plus_0_r. rewrite plus_comm.
    rewrite plus_succ. reflexivity.
Qed.
