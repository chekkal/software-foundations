(* Software Foundations *)
(* Exercice 3 stars, g_times2 *)

Inductive gorgeous : nat -> Prop :=
g_0: gorgeous 0
|g_3: forall n, gorgeous n -> gorgeous(3 + n)
|g_5: forall n, gorgeous n -> gorgeous(5 + n).


Lemma helper_g_times2 : forall x y z,x +(z +y)=z +x +y.
Proof.
    intros. induction x.
    simpl. rewrite <- plus_n_O. reflexivity.
    simpl. rewrite IHx. rewrite <- plus_n_Sm. rewrite plus_Sn_m. reflexivity.
Qed.

Theorem g_times2: forall n, gorgeous n -> gorgeous (2*n).
Proof.
    intros n H. simpl.
    induction H.
    apply g_0.
    rewrite <- plus_n_O in IHgorgeous.
    apply g_3 with (n:=n+(3 + n + 0)). rewrite <- plus_n_O. rewrite helper_g_times2.
    apply g_3 with (n:=n+n). apply IHgorgeous.
    rewrite <- plus_n_O in IHgorgeous.
    apply g_5 with (n:=n+(5 + n + 0)). rewrite <- plus_n_O. rewrite helper_g_times2.
    apply g_5 with (n:=n+n). apply IHgorgeous.
Qed.
