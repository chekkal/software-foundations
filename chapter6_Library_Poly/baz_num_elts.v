(* Software Foundations *)
(* Exerice 2 stars, baz_num_elts *)

Inductive baz : Type := 
|x : baz -> baz
|y : baz -> bool ->baz.

(* The inductive type baz has twi constructors, the catch is that those constructors needs an element of type baz as the 
first argument in order to create an element of type baz, so we can't bootstrap an instanciation of type baz. *)
