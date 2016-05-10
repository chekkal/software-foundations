(* Software Foundations *)
(* Exercice 3 stars, double_induction *)

Theorem double_induction: forall (P: nat -> nat -> Prop),
P 0 0 -> (forall m, P m 0 -> P (S m) 0) 
-> (forall n, P 0 n -> P 0 (S n))
-> (forall m n, P m n -> P (S m) (S n))
-> forall m n, P m n.
Proof.
intros h1 h2 h3 h4 h5. 
induction m as [|m']. induction n as [|n'].
    apply h2. 
    apply h4. apply IHn'.
  induction n as [|n'].
    apply h3. apply IHm'.
    apply h5. apply IHm'.
Qed.

