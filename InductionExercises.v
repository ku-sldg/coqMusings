Require Import Bool Arith Omega List.

Fixpoint sum(l:list nat) : nat :=
  match l with
  | nil => 0
  | x :: xs => x + sum xs
  end.

Eval compute in sum nil.
Eval compute in sum (2 :: 1 :: nil).

Fixpoint sum_tail' (l:list nat) (acc:nat) : nat :=
  match l with
  | nil => 0
  | x :: xs => sum_tail' xs (x + acc)
  end.

Definition sum_tail (l:list nat) : nat :=
  sum_tail' l 0.

Theorem sum_tail_correct :
  forall l, sum_tail l = sum l.
Proof.
  * induction l.
  + unfold sum_tail. reflexivity.
  + unfold sum_tail.
    unfold sum_tail'.
  
