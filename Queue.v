Require Import Lists.List.
Require Import Lists.ListDec.
Import ListNotations.
  
Module Type Queue.
  Parameter queueT:Type.
  Parameter emptyT:queueT.
  Parameter addT: nat -> queueT -> queueT.

  Parameter first:queueT -> nat.
  Parameter rest:queueT -> queueT.

  Axiom empty_neq_empty: emptyT <> emptyT -> False.

  Axiom add_neq_empty: forall x q, addT x q <> emptyT.

End Queue.


Module QueueAsInductive <: Queue.
  
  Inductive queue:Type :=
  | empty : queue
  | add : nat -> queue -> queue.

  Definition queueT := queue.
  Definition emptyT := empty.
  Definition addT := add.
  
  Lemma empty_neq_empty: empty <> empty -> False.
  Proof.
    intros.
    contradiction.
  Qed.

  Theorem add_neq_empty: forall x q, add x q <> empty.
  Proof.
    intros x q.
    discriminate.
  Qed.

  Fixpoint first(q:queue):nat :=
    match q with
    | empty => 42
    | add n q' => match q' with
                 | empty => n
                 | add _ _ => first q'
                 end
    end.

  Compute first empty.
  Compute first (add 3 empty).
  Compute first (add 2 (add 3 empty)).
  Compute first (add 1 (add 2 (add 3 empty))).

  Fixpoint rest(q:queue):queue :=
    match q with
    | empty => empty
    | add n q' => match q' with
                 | empty => empty
                 | add _ _ => add n (rest q')
                 end
    end.

  Compute rest empty.
  Compute rest (add 1 empty).
  Compute rest (add 1 (add 2 empty)).
  Compute rest (add 1 (add 2 (add 3 empty))).

  Theorem rest_add: forall x q, q=empty -> rest (add x q) = q.
  Proof.
    intros n q.
    intros H.
    subst.
    reflexivity.
  Qed.

  Definition firstD(q:queue):q<>empty -> nat :=
    match q with
    | empty => fun pf => match empty_neq_empty pf with end
    | add n q' => fun _ => first (add n q')
    end.
  
  Compute firstD (add 2 empty) (add_neq_empty 2 empty).
  Compute firstD empty.

  Definition firstS(q:{q':queue | q'<>empty}) : nat :=
    match q with
    | exist _ empty pf => match empty_neq_empty pf with end
    | exist _ (add x' q') _ => first (add x' q')
    end.

  Compute firstS (exist _ (add 2 empty) (add_neq_empty 2 empty)).
  Compute firstS (exist _ empty _).
  
End QueueAsInductive.

Module QueueAsList <: Queue.

  Definition queue: Type := list nat.
  Definition empty: queue := nil.
  Definition add(n:nat)(q:queue):queue := (app q (cons n q)).
  Definition first(q:queue):nat := match q with
                                 | nil => 42
                                 | (cons n _) => n
                                 end.
  Definition rest(q:queue):queue := match q with
                                    | nil => nil
                                    | (cons _ q') => q'
                                    end.
  
  Lemma empty_neq_empty: empty<>empty -> False.
  Proof.
    contradiction.
  Qed.

  Lemma add_neq_empty: forall x q, add x q <> empty.
  Proof.
    intros q x.
    unfold add in *; unfold empty in *.
    unfold not. intros.
    symmetry in H.
    generalize H.
    apply app_cons_not_nil.
  Qed.
           
  Definition queueT := queue.
  Definition emptyT := empty.
  Definition addT := add.

End QueueAsList.
