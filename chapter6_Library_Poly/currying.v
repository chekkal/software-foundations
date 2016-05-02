(* Software Foundations *)
(* Exercice 2 stars, advanced currying *)

Definition prod_curry{X Y Z: Type}
      (f: X*Y -> Z)(x: X)(y: Y): Z := f(x,y).

Definition prod_uncurry{X Y Z: Type}
      (f: X -> Y -> Z)(p: X*Y): Z := match p with (x,y) => f x y end.

Definition prod_uncurry'{X Y Z: Type}
      (f: X -> Y -> Z)(p: X*Y): Z := f (fst p) (snd p).

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry: forall (X Y Z: Type)(f: X -> Y -> Z)(x: X)(y: Y),
      prod_curry (prod_uncurry f) x y = f x y.
Proof.
    intros. compute. reflexivity.
Qed.

Theorem curry_uncurry: forall (X Y Z: Type)(f: X*Y -> Z)(p: X*Y),
      prod_uncurry (prod_curry f) p = f p.
Proof.
    intros. compute. destruct p. reflexivity.
Qed.
