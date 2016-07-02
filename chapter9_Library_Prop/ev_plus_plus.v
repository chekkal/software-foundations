(* Software Foundations *)
(* Excercice 3 stars, ev_plus_plus *)

Inductive ev: nat -> Prop :=
|ev_0: ev 0
|ev_ss: forall n: nat, ev n -> ev (S (S n)).

Fixpoint double (n: nat): nat :=
match n with
|O => O
|S n' => S(S (double n'))
end.

Theorem double_even: forall n: nat, ev (double n).
Admitted.

Theorem ev_sum: forall n m, ev n -> ev m -> ev (n + m).
Admitted.

Theorem ev_ev__ev : forall n m, ev (n + m) -> ev n -> ev m.
Admitted.

Lemma simpl_sum: forall n m p, n + m + (n + p) = double n + (m + p).
Admitted.

Theorem ev_plus_plus : forall n m p, ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
    intros. 
    apply ev_sum with (n:=n+m)(m:=n+p) in H. rewrite simpl_sum in H. apply ev_ev__ev with (n:= double n).
    apply H.
    apply  double_even.
    apply H0.
Qed.
