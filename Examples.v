Require Import Arith.
Require Import Omega.

Inductive unit : Set :=
  | tt.

Check unit.

Check tt.

Theorem unit_singleton : forall (x:unit), x = tt.
Proof.
  intros.
  destruct x.
  reflexivity.
Qed.

Check unit_ind.

Inductive empty_set : Set :=.

Theorem  bad: forall x : empty_set, 2+2=5.
Proof.
  intros.
  destruct x.
Qed.

Definition e2u(x : empty_set) : unit := match x with end.

Check e2u.

Theorem negb_inverse : forall (b:bool), negb (negb b) = b.
Proof.
  intros.
  destruct b ; reflexivity.
Qed.

Theorem negb_neq: forall b:bool, negb b <> b.
Proof.
  intros.
  destruct b; discriminate.
Qed.

Theorem S_inj: forall n m:nat, S n = S m -> n = m.
Proof.
  intros n m.
  injection 1.
  trivial.
Qed.

Theorem S_inj': forall n m:nat, S n = S m -> n = m.
Proof.
  intros n m.
  intros H.
  inversion H.
  reflexivity.
Qed.

Theorem S_inj'': forall n m:nat, S n = S m -> n = m.
Proof.
  congruence.
Qed.

Inductive even : nat -> Prop :=
| EvenO : even O
| EvenSS : forall n, even n -> even (S (S n)).

Theorem even_0 : even 0.
Proof.
  constructor.
Qed.

Theorem even_4' : even 4.
Proof.
  apply EvenSS. apply EvenSS. apply EvenO.
Qed.                    

Theorem even_4 : even 4.
Proof.
  constructor. constructor. constructor.
Qed.

Hint Constructors even.

Theorem even_4'' : even 4.
  auto.
Qed.

Theorem even_1_contra : even 1 -> False.
Proof.
  intros.
  inversion H.
Qed.

Theorem even_3_contra : even 3 -> False.
Proof.
  intros.
  inversion H.
  inversion H1.
Qed.

Inductive nat_list : Set :=
| NNil : nat_list
| NCons : nat -> nat_list -> nat_list.

Fixpoint nlength(ls:nat_list) : nat :=
  match ls with
    | NNil => 0
    | NCons _ ls' => S (nlength ls')
  end.

Fixpoint napp (ls1 ls2 : nat_list): nat_list :=
  match ls1 with
    | NNil => ls2
    | NCons n ls1' => NCons n (napp ls1' ls2)
  end.

Theorem nlength_napp : forall ls1 ls2,
                         nlength (napp ls1 ls2) = (nlength ls1) + (nlength ls2).
Proof.
  intros.
  induction ls1.
  simpl.
  trivial.
  simpl. rewrite IHls1. trivial.
Qed.

Inductive nat_btree : Type :=
| NLeaf : nat_btree
| NNode : nat_btree -> nat -> nat_btree -> nat_btree.

Fixpoint nsize (tr : nat_btree) : nat :=
  match tr with
    | NLeaf => 1
    | NNode tr1 _ tr2 => (nsize tr1) + (nsize tr2)
  end.

Fixpoint nsplice (tr1 tr2 : nat_btree) : nat_btree :=
  match tr1 with
    | NLeaf => NNode tr2 O NLeaf
    | NNode tr1' n tr2' => NNode (nsplice tr1' tr2) n tr2'
  end.

Theorem plus_assoc : forall n1 n2 n3 : nat,
                       plus (plus n1 n2) n3 = plus n1 (plus n2 n3).
Proof.
  intros.
  induction n1. destruct n2. destruct n3.
  trivial.
  trivial.
  trivial.
  simpl. rewrite IHn1. reflexivity.
Qed.

Section list.

  Variable T : Type.

  Inductive list : Type :=
  | Nil : list
  | Cons : T -> list -> list.

  Fixpoint length (ls : list) : nat :=
    match ls with
      | Nil => O
      | Cons _ ls' => S (length ls')
    end.

  Fixpoint app (ls1 ls2 : list) : list :=
    match ls1 with
      | Nil => ls2
      | Cons x ls1' => Cons x (app ls1' ls2)
    end.

  Theorem length_app : forall (ls1 ls2 : list),
                         length (app ls1 ls2) = plus (length ls1) (length ls2).
  Proof.
    induction ls1.
      induction ls2.
        reflexivity.
        reflexivity.
        intros. simpl. rewrite IHls1. reflexivity.
  Qed.
End list.

Arguments Nil [T].

Check list_ind.

Inductive pformula : Type :=
| Truth : pformula
| Falsehood : pformula
| Conjunction : pformula -> pformula -> pformula.

Fixpoint pformulaDenote (f:pformula): Prop :=
  match f with
    | Truth => True
    | Falsehood => False
    | Conjunction f1 f2 => pformulaDenote f1 /\ pformulaDenote f2
  end.

Theorem arith_neq : 2+2=5 -> 9+9=835.
  intros. elimtype False. inversion H.
Qed.

Print not.

Theorem arith_neq' : ~(2+2=5).
  unfold not.
  intros.
  inversion H.
Qed.

Theorem or_comm : forall P Q, P \/ Q -> Q \/ P.
Proof.
  destruct 1.
  right. assumption.
  left. assumption.
Qed.

Theorem or_comm' : forall P Q, P \/ Q -> Q \/ P.
Proof.
  tauto.
Qed.

Theorem arith_comm : forall (ls1 ls2 : list nat),
                       length nat ls1 = length nat ls2 \/ length nat ls1 + length nat ls2 = 6
                       -> length nat (app nat ls1 ls2) = 6 \/ length nat ls1 = length nat ls2.
Proof.
  intuition.
  rewrite length_app.
  tauto.
Qed.

Theorem arith_comm' : forall (ls1 ls2 : list nat),
                       length nat ls1 = length nat ls2 \/ length nat ls1 + length nat ls2 = 6
                       -> length nat (app nat ls1 ls2) = 6 \/ length nat ls1 = length nat ls2.
Proof.
  Hint Rewrite length_app.
  intuition.
  rewrite length_app.
  tauto.
Qed.

Theorem exsits1: exists (x : nat), x+1=2.
Proof.
  exists 1.
  trivial.
Qed.

Theorem exists3: forall (n m : nat), (exists (x : nat), n + x = m) -> n <= m.
Proof.
  intros.
  destruct H.
  omega.
Qed.

Theorem even_plus : forall n m, even n -> even m -> even (n + m).
Proof.
  induction n.
    induction m.
      simpl. intros. assumption.
      simpl. intros. assumption.
      simpl. intros. inversion H. simpl. constructor.
      Restart.
      induction 1.
        intros. simpl. assumption.
        intros. simpl. constructor. apply IHeven. assumption.
Qed.

Theorem even_contra: forall n, even (S (n + n)) -> False.
Proof.
  intros.
Abort.

Lemma zgtz : 0 > 0 -> False.
  intros. omega.
Qed.

Print zgtz.

Print pred.

(* Extraction pred. *)

(** The type of [pred_strong1] is [nat -> (n > 0 -> nat)].  So, [pred_strong]
  returns a thing that maps [n > 0] to [nat]. *)

Definition pred_strong1 (n:nat) : n > 0 -> nat :=
  match n with
    | O => fun pf : 0>0 => match zgtz pf with end
    | S n' => fun _ => n'
  end.

Eval compute in pred_strong1.

Eval compute in pred_strong1 1.

Lemma ogtz : 1 > 0.
  omega.
Qed.

Eval compute in pred_strong1 1 ogtz.

Check pred_strong1.

(** What does return do? *)

Definition pred_strong1' (n:nat) : n > 0 -> nat :=
  match n return n > 0 -> nat with
    | O => fun pf : 0 > 0 => match zgtz pf with end
    | S n' => fun _ => n'
  end.

Eval compute in pred_strong1' 1.

Eval compute in pred_strong1' 1 ogtz.

Print ogtz.

Check ogtz.

Print sig.

(** Note that in the definition of [sig] the term [exist] is a label for
  a case and not a quantifier. *)

Definition pred_strong2 (s : {n : nat | n > 0}) : nat :=
  match s with
    | exist _ O pf => match zgtz pf with end
    | exist _ (S n') _ => n'
  end.

Check exist.

Check exist (fun x => (x>0)) 1 ogtz.

Check exist _ 1 ogtz.

Check ogtz.

Check sig (fun x:nat => x=3).

Check {x : nat | x = 3}.

Eval compute in pred_strong2 (exist _ 1 ogtz).

Check pred_strong2.

Eval compute in pred_strong2 (exist _ 1 ogtz).

Lemma tgtz : S (S 0) > 0.
Proof.
  omega.
Qed.

Eval compute in pred_strong2 (exist _ 2 tgtz).

Lemma ttgtz : 3 > 0.
  omega.
Qed.

Print ttgtz.
  
Eval compute in pred_strong2 (exist _ 3 ttgtz).

Definition pred_strong4 : forall n:nat, n>0 -> {m : nat | n = S m}.
  refine (fun n =>
            match n with
              | O => fun _ => False_rec _ _
              | S n' => fun _ => exist _ n' _
            end).
  Proof.
    inversion g.
    trivial.
  Defined.

Print pred_strong4.

Eval compute in pred_strong4 2 tgtz.

(** Let's take all this cool stuff and build a dependently typed [Stack].
  We'll start with an inductive definition for [Stack] of [nat]. *)

Inductive Stack : Type :=
| Empty : Stack
| Push : nat -> Stack -> Stack.

(** Trivial proof that [Push] never results in [Empty].  This is a simple
  application of discriminate to show that the two constructors produce
  distinct values.  We'll need this later. *)

Lemma push_neq_empty : forall (t:nat) (s:Stack),
                         Push t s <> Empty.
Proof.
  intros.
  discriminate.
Qed.

(** Trival proof that [Empty] not equal to [Empty] is [False].  Again, we'll
  need this later when we instantiate [s <> Empty] with [Empty]. *)

Lemma empty_neq_empty: Empty <> Empty -> False.
Proof.
  intros.
  auto.
Qed.

(** Dependent [pop] takes a stack and returns a _function_ from a [Prop] to a
  [Stack] value. This is exceptionally cool. Remember that a theorem is a
  type and a proof is a witness to that type.  Thus, the type
  [s<>Empty -> Stack] takes a witness to the type [s<>Empty] -- a proof of
  that theorem -- and returns a [Stack]. So, we don't get a [Stack] until
  we provide that proof. *)

Definition pop(s:Stack):s<>Empty -> Stack := 
  match s with
    | Empty => fun pf : (Empty <> Empty) => match empty_neq_empty pf with end
    | Push _ s' => fun _ => s'
  end.

(** Alternative definition of [pop] using [refine] to refine a partial proof
  that generates the function. *)

Definition pop' : forall s:Stack, s<>Empty -> Stack.
  refine (fun s =>
            match s with
              | Empty => fun _ => False_rec _ _
              | Push _ s' => fun _ => s'
            end).
  apply empty_neq_empty. assumption.
Defined.

Example pop_push': forall n s, (pop' (Push n s)) (push_neq_empty n s) = s.
Proof.
  reflexivity.
Qed.
  
Eval compute in pop' Empty.

(* Extraction pop'. *)

(** Simple example that [pop] on [Push 1 Empty] is [Empty].  It's not the
  values that inter interesting, but the arguments to [pop].  The initial
  call to [pop] is a stack of size one. The result is a function from
  [Push 1 Empty <> Empty] to [Empty].  The second argument to [push] is
  an instance of the proof [push_neq_empty] for [Push 1 Empty].  The type of
  this proof is [Push 1 Empty <> Empty], thus the result is [Empty] as
  expected. *)

Example pop_push: forall n s, (pop (Push n s)) (push_neq_empty n s) = s.
Proof.
  reflexivity.
Qed.

Definition pop''(s:Stack) : s <> Empty -> Stack :=
  match s with
    | Empty => fun pf : Empty <> Empty => match empty_neq_empty pf with end
    | Push _ s' => fun _ => s'
  end.

Eval compute in (pop'' (Push 2 (Push 1 Empty)))
                  (push_neq_empty 2 (Push 1 Empty)).


Definition pop2(s:{s':Stack | s'<>Empty}) : Stack :=
  match s with
    | exist _ Empty pf => match empty_neq_empty pf with end
    | exist _ (Push _ s') _ => s'
  end.

Definition top2(s:{s':Stack | s'<>Empty}) : nat :=
  match s with
    | exist _ Empty pf => match empty_neq_empty pf with end
    | exist _ (Push t _) _ => t
  end.

Eval compute in {s' : Stack | s' <> Empty}.

Check exist.

(** Exist takes a predicate, value, and proof of the predicate.  Note the type of the proof and the type of the predicate *)

Eval compute in exist (fun s => s <> Empty)
                      (Push 1 Empty)
                      (push_neq_empty 1 Empty).

Eval compute in pop2 (exist (fun s => s <> Empty)
                            (Push 1 Empty)
                            (push_neq_empty 1 Empty)).

Eval compute in top2 (exist (fun s => s <> Empty)
                            (Push 1 Empty)
                            (push_neq_empty 1 Empty)).

Eval compute in pop2 (exist (fun s => s <> Empty)
                            (Push 1 (Push 2 Empty))
                            (push_neq_empty 1 (Push 2 Empty))).

Eval compute in top2 (exist (fun s => s <> Empty)
                            (Push 1 (Push 2 Empty))
                            (push_neq_empty 1 (Push 2 Empty))).

Eval compute in pop2 (exist (fun s => s <> Empty)
                            (Push 1 (Push 2 (Push 3 Empty)))
                            (push_neq_empty 1 (Push 2 (Push 3 Empty)))).

Eval compute in top2 (exist (fun s => s <> Empty)
                            (Push 1 (Push 2 (Push 3 Empty)))
                            (push_neq_empty 1 (Push 2 (Push 3 Empty)))).

(** Define [push] that takes any stack and produces a nonempty stack *)

Definition push(x:nat)(s:Stack):{s':Stack | s'<>Empty}:=
  exist (fun s => s <> Empty) (Push x s) (push_neq_empty x s).

(** [proj1_sig] pulls out the first element of [sig] containing the result
 value. *)

Eval compute in proj1_sig (push 1 Empty).

(** [proj2_sig] pulls out the second element of [sig] containing the proof
 result. *)

Eval compute in proj2_sig (push 1 Empty).

(** Proof for later that [pop] after two [push] operations results in a
  nonempty stack. *)

Lemma pop_push_push_neq_empty:
  forall n m, (pop2 (push n (proj1_sig (push m Empty)))) <> Empty.
Proof.
  intros.
  simpl.
  discriminate.
Qed.

Eval compute in (top2
                   (exist (fun s => s <> Empty)
                          (pop2 (push 2 (proj1_sig (push 1 Empty))))
                          (pop_push_push_neq_empty 2 1))).

(** Example mixing [push], [pop], and [top]:

<<<
  (top (pop (push 2 (push 1 Empty))))
>>>

 Note that we must provide a proof that the result of [pop] is a nonempty
 stack. *)

Example mixed: forall n m, (top2
                  (exist (fun s => s <> Empty)
                         (pop2 (push n (proj1_sig (push m Empty))))
                         (pop_push_push_neq_empty n m)))
               = m.
Proof.
  intros.
  reflexivity.
Qed.

(** Moving on to using [sumbool] to capture computable proofs *)

Print sumbool.

Lemma zez: 0=0. reflexivity. Qed.

Print zez.

Lemma znes : forall n, 0 <> S n. intros. discriminate. Qed.

Print znes.

Definition eq_nat_dec'' : forall n m : nat, {n=m} + {n<>m}.
  refine (fix f (n m:nat) : {n=m} + {n<>m} :=
            match n,m with
              | O, O => (left _ zez)
              | S n', S m' => (if (f n' m') then (left _ _) else (right _ _))
              | i,j => (right _ _)
            end).
    omega.
    omega.
    rewrite e. reflexivity.
    injection. intros. omega.
Defined.

Print eq_nat_dec''.

(* Extraction eq_nat_dec''. *)

Eval compute in eq_nat_dec'' 2 2.

Eval compute in eq_nat_dec'' 2 3.

Check left (1=0) ogtz.

Check right (1=0) ogtz.

Eval compute in left (1=1) _.

Eval compute in right (1<>1) _.

Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).
Notation "'Reduce' x" := (if x then Yes else No) (at level 50).

Eval compute in forall n m : nat, {n = m} + {n <> m}.

Definition eq_nat_dec : forall n m : nat, {n=m} + {n<>m}.
  refine (fix f (n m:nat) : {n=m} + {n<>m} :=
            match n,m with
              | O, O => Yes
              | S n', S m' => Reduce (f n' m')
              | _,_ => No
            end); intros. reflexivity. omega. omega. rewrite e. reflexivity. injection. intros. omega.
Defined.

Eval compute in eq_nat_dec 2 2.

Eval compute in eq_nat_dec 2 3.

(* Extraction eq_nat_dec. *)

Definition eq_nat_dec' (n m:nat) : {n=m}+{n<>m}.
  decide equality.
Defined.

(* Extraction eq_nat_dec'. *)

Inductive maybe {A : Set} (P : A -> Prop) : Set :=
| Unknown : maybe P
| Found : forall x:A, P x -> maybe P.

Definition pred_strong7 : forall n : nat, (maybe (fun m => n = S m)).
  refine (fun n =>
            match n with 
              | O => Unknown _
              | S n' => Found _ n' _
            end). trivial.
  Defined.

Eval compute in pred_strong7 5.

Eval compute in pred_strong7 0.

Notation "{{ x | P }}" := (maybe (fun x => P)).
Notation "??" := (Unknown _).
Notation "[| x |]" := (Found _ x _).

Module LenIndexLists.
Section ilist.
  Variable A : Type.

  Set Implicit Arguments.

  Inductive ilist : nat -> Type :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).

  Fixpoint app n1 (ls1 : ilist n1) n2 (ls2:ilist n2) : ilist (n1 + n2) :=
    match ls1 with 
      | Nil => ls2
      | Cons x ls1' => Cons x (app ls1' ls2)
    end.

  Print app.

  Fixpoint app' n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) : ilist (n1 + n2) :=
    match ls1 in (ilist n1) return (ilist (n1 + n2)) with
      | Nil => ls2
      | Cons x ls1' => Cons x (app' ls1' ls2)
    end.

End ilist.

Eval compute in Nil.
Eval compute in (Cons 12 (Cons 11 (Cons 10 (Nil nat)))).

Eval compute in app (Cons 12 (Cons 11 (Cons 10 (Nil nat)))) (Nil nat).
Eval compute in app' (Cons 12 (Cons 11 (Cons 10 (Nil nat)))) (Nil nat).

(** auto and Ltac examples *)

(** Two definitions of natural addition that demonstrate the functional and
  logic programming idioms.  They also demonstrate any important specification
  technique for languages where a rule-specified relation defines requirements
  for an operation and a function implements them.  [plus] is the functional
  definition: *)

Print plus.

(** [plusR] is the relational definition of the same function: *)

Inductive plusR : nat -> nat -> nat -> Prop :=
| PlusO : forall m, plusR O m m
| PlusS : forall n m r, plusR n m r -> plusR (S n) m (S r).

Hint Constructors plusR.

(** We can show that [plus] and [plusR] are consistent.  Specifically, that
  [plus] implements the relational defintion from [plusR].  This is the same
  thing as showing that a language interpreter implements its relational
  specification: *)

Theorem plus_plusR: forall n m,
    plusR n m (n + m).
Proof.
  intros.
  induction n.
  auto.
  simpl. auto.
Qed.

Theorem plusR_plus: forall n m r,
    plusR n m r -> r = n + m.
Proof.
  intros.
  induction H.
  reflexivity.
  simpl. auto.
Qed.

(** Using the functional definition to show that [4+3=7]: *)

Example four_plus_three: 4 + 3 = 7.
Proof.
  reflexivity.
Qed.

Print four_plus_three.

(** Using the relational definition to show that [4+3=7]: *)

Example four_plus_three' : plusR 4 3 7.
Proof.
  repeat apply PlusS.
  apply PlusO.
  Restart. auto.
Qed.

Print four_plus_three'.

(** To prevent bad things, [auto] only goes 5 levels deep by default.  We
  can tell it to go deeper by specifying an argument: *)

Example five_plus_three: plusR 5 3 8.
Proof.
  info_auto 6.
Qed.

(** Now we do subtraction by calculating [x].  We're not really doing a
  calculation though as we're providing the definition of [x] using
  [ex_intro], the rule for eliminating an existential quantifier by
  providing a witness.  Coq would have a difficult time finding this
  witness on its own. *)

Example seven_minus_three: exists x, x + 3 = 7.
Proof.
  apply ex_intro with 4.
  reflexivity.
Qed.

(** Same thing with the relational definition. *)

Example seven_minus_three': exists x, plusR x 3 7.
Proof.
  eapply ex_intro.
  apply PlusS. apply PlusS.  apply PlusS.  apply PlusS. apply PlusO.
  Restart.
  eapply ex_intro.
  info_eauto 6.
Qed.

SearchRewrite (O + _).

Hint Immediate plus_O_n.

Lemma plusS: forall n m r,
    n + m = r -> S n + m = S r.
Proof.
  intros.
  simpl. auto.
Qed.

Hint Resolve plusS.

Example seven_minus_three'' : exists x, x + 3 = 7.
Proof.
  eauto 6.
Qed.

Example seven_minus_four'' : exists x, 4 + x = 7.
Proof.
  eauto 7.
Qed.

Example beta1 : ((fun x => x + 1) 2) = 3.
Proof.
  cbv beta.
  trivial.
Qed.

Example beta2 : (((fun y => (fun x => x + y + 3)) 1) 2) = 6.
Proof.
  cbv beta.
  trivial.
Qed.