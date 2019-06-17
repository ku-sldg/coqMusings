Require Import Bool Arith Omega List.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint sum(l:list nat) : nat :=
  match l with
  | nil => 0
  | x :: xs => x + sum xs
  end.

Eval compute in sum [ ].
Eval compute in sum [2 ; 1].

Fixpoint sum_tail' (l:list nat) (acc:nat) : nat :=
  match l with
  | nil => acc
  | x :: xs => sum_tail' xs (x + acc)
  end.

Definition sum_tail (l:list nat) : nat :=
  sum_tail' l 0.

Lemma helper: forall l a, sum_tail' l a = a + sum_tail' l 0.
Proof.
  induction l.
  + intros. simpl. omega.
  + intros. simpl. rewrite <- plus_n_O. symmetry. rewrite IHl. rewrite (IHl (a + a0)). omega.
Qed.

Theorem sum_tail_correct : forall l, sum_tail l = sum l.
Proof.
  unfold sum_tail.
  induction l.
  + reflexivity.
  + unfold sum. simpl.
    fold sum.
    rewrite <- plus_n_O.
    rewrite <- IHl.
    apply helper.
Qed.

Lemma helper': forall l a, sum_tail' l a = a + sum l.
Proof.
  intros. induction l.
  + simpl. omega.
  + simpl. rewrite plus_assoc.
    assert (a + a0 + sum l = a0 + a + sum l). omega.
    rewrite H. rewrite plus_assoc_reverse.
    rewrite <- IHl.
    rewrite helper.
    symmetry.
    rewrite helper.
    omega.
Qed.

SearchAbout plus.

Theorem sum_tail_correct' : forall l, sum_tail l = sum l.
Proof.
  intros.
  rewrite <- plus_O_n.
  unfold sum_tail.
  apply helper'.
Qed.

Fixpoint sum_cont' {A} (l : list nat) (k : nat -> A) : A :=
  match l with
  | [] => k 0
  | x :: xs => sum_cont' xs (fun ans => k (x + ans))
  end.

Definition sum_cont (l : list nat) : nat :=
  sum_cont' l (fun x => x).

Theorem sum_cont_correct:
  forall l, sum_cont l = sum l.
Proof.
  induction l.
  + reflexivity.
  + simpl.
    unfold sum_cont.
    simpl.
    rewrite <- IHl.
    unfold sum_cont.
    unfold sum_cont'.
Abort.

SearchAbout plus.

Lemma helper_cont': forall a l, sum_cont' l (fun ans : nat => a + ans) = a + sum l.
Proof.
  intros a l.
  induction l.
  + reflexivity.
  + simpl.
    rewrite plus_assoc.
    rewrite (Nat.add_comm a a0).
    rewrite plus_assoc_reverse.
    rewrite <- IHl.
    simpl.
    (* Induction on [a0] here does not help.  Base case is trivial.
     inductive case is roughly the same complexity or harder. *)
    assert (forall y, sum_cont' l (fun x : nat => y+x) = y+sum_cont' l (fun x : nat => x)).
    { intros.
      unfold sum_cont'.