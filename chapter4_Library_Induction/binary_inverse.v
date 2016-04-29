(* Software Foundations *)
(*Exercice 5 stars, advanced binary inverse*)
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

Lemma plus_comm: forall n m: nat, n + m = m + n.
Proof. (* already solved see mult_comm.v *) Admitted.

Theorem binary_commute: forall (b: bin),
      binary_to_unary(increment(b))= binary_to_unary(b)+1.
Proof. (* already solved see binary_commute.v *) Admitted.

(* First, write a function to convert natural numbers to binary numbers.  Then prove that starting with any natural number, converting to binary, then converting back yields the same natural number you started with.*)

Fixpoint unary_to_binary (n: nat): bin :=
match n with
|O    => zero
|S n' => increment(unary_to_binary  n')
end.

Theorem unary_inverse: forall n: nat, binary_to_unary(unary_to_binary n)=n.
Proof.
intros. induction n as [|n'].
simpl. reflexivity.
simpl. rewrite binary_commute. rewrite IHn'. rewrite plus_comm. simpl. reflexivity.
Qed.

Lemma plus_0_r: forall n: nat, n + 0 = n.
Proof. (* already solved see mult_comm.v *) Admitted.

(* Define a function normalize from binary numbers to binary numbers such that for any binary number b, converting to a natural and then back to binary yields (normalize b). Prove it.*)
Definition normalize(b: bin): bin := unary_to_binary(binary_to_unary b).

Theorem binary_inverse: forall b: bin, unary_to_binary(binary_to_unary b) = normalize b.
Proof.
intros. induction b as [|b1|b2].
simpl. reflexivity.
(*case: unary_to_binary (binary_to_unary (twice b1)) = normalize (twice b1) *)
(* we can simply use unfold normalize. reflexivity. but we haven't seen unfold tactic yet. We have to do it the hard way *)
destruct normalize.
  reflexivity.
  reflexivity.
  reflexivity.
(*case: unary_to_binary (binary_to_unary (one_more_twice b2)) = normalize (one_more_twice b2) *)
(* we can simply use unfold normalize. reflexivity. but we haven't seen unfold tactic yet. We have to do it the hard way *)
destruct normalize.
  reflexivity.
  reflexivity.
  reflexivity.
Qed.
