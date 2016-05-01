(* Software Foundations *)
(* Exercice 2 stars,mumble_grumble *)

Inductive mumble: Type :=
|a: mumble
|b: mumble -> nat -> mumble
|c: mumble.

Inductive grumble(X: Type): Type :=
|d: mumble -> grumble X
|e: X -> grumble X.

Check (d _ (b a 5)).
Check (d mumble (b a 5)).
Check (d bool (b a 5)).
Check (e bool true).
Check (e mumble (b c 0)).
Check c.
Check (e bool (b c 0)).
