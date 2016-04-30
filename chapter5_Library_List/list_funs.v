(* Software Foundations *)
(* Exerice 2 stars, list_funs *)

Inductive natlist: Type:=
|nil: natlist
|cons: nat -> natlist -> natlist.

Notation "[]" := nil.
Notation " x :: l" := (cons x l).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint nonzeros (l:natlist) : natlist :=
match l with 
|nil       => nil
|cons 0 l' => nonzeros l'
|cons x l' => x :: (nonzeros l')
end.

Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity.  Qed.

Fixpoint oddmembers (l:natlist) : natlist := 
match l with 
|nil => nil
|cons n l' => if (Nat.even n) then oddmembers l' else n :: oddmembers l'
end.

Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Fixpoint countoddmembers (l:natlist) : nat := 
match l with
|nil => O
|cons n l' => if (Nat.even n) then countoddmembers l' else S(countoddmembers l')
end.

Example test_countoddmembers1 : countoddmembers [1;0;3;1;4;5] = 4. 
Proof. reflexivity. Qed.

Example test_countoddmembers2 : countoddmembers [0;2;4] = 0. 
Proof. reflexivity. Qed.

Example test_countoddmembers3 : countoddmembers nil = 0. 
Proof. reflexivity. Qed.

