Require Import List.

Print LoadPath.

Require Import Monad.Maybe.

Set Implicit Arguments.

(** Definition of a simple expression language *)

Inductive exp : Set :=
| Nat : nat -> exp
| Plus : exp -> exp -> exp
| Bool : bool -> exp
| And : exp -> exp -> exp.

(** Definition of a simple type language *)

Inductive type : Set := TNat | TBool.

(** Definition of a typing relation.  Note this is a relation defined in the
  canonical Coq style. *)

Inductive hasType : exp -> type -> Prop :=
| HtNat : forall n, hasType (Nat n) TNat
| HtPlus : forall e1 e2,
             hasType e1 TNat -> hasType e2 TNat -> hasType (Plus e1 e2) TNat
| HtBool : forall b, hasType (Bool b) TBool
| HtAnd : forall e1 e2,
             hasType e1 TBool -> hasType e2 TBool -> hasType (And e1 e2) TBool.

(** Standard definition for comparing two types.  This seems rather silly
  as our type system contains only primitive values. *)

Definition eq_type_dec : forall t1 t2 : type, {t1=t2} + {t1 <> t2}.
  decide equality.
Defined.

(** Notation for maybe that allows sequencing.  If [e1] succeeds, then [e2]
 follows with access to the proof.  Otherwise, fail with [??]. Because this 
 is the maybe type rather than sumbool, we get a proof when [typeCheck]
 returns a type, but not when it doesn't.  This is the primary difference
 between sumbool and maybe. *) 

Notation "e1 ;; e2" := (if e1 then e2 else ??)
                         (right associativity, at level 60).

(** Define a function that generates an output satisfying [hasType].  The maybe
  type captures this in the definition of [typeCheck]. *)

Definition typeCheck : forall e : exp, {{t | hasType e t}}.
  refine (fix F (e:exp): {{t | hasType e t}} :=
            match e with
              | Nat _ => [|TNat|]
              | Plus e1 e2 =>
                t1 <- (F e1);
                t2 <- (F e2);
                eq_type_dec t1 TNat ;; eq_type_dec t2 TNat ;; [|TNat|]
              | Bool _ => [|TBool|]
              | And e1 e2 =>
                t1 <- (F e1);
                t2 <- (F e2);
                eq_type_dec t1 TBool ;; eq_type_dec t2 TBool ;; [|TBool|]
            end).
  constructor.
  apply HtPlus. rewrite _H in h. assumption. rewrite _H0 in h0. assumption.
  constructor.
  apply HtAnd. rewrite _H in h. assumption. rewrite _H0 in h0. assumption.
Defined.

Eval compute in typeCheck (Plus (Nat 0) (Nat 0)).

Print sumor.

Notation "!" := (False_rec _ _).
Notation "[ e ]" := (exist _ e _).
Notation "!!" := (inright _ _).
Notation "[|| x ||]" := (inleft _ [x]).
Notation "e1 ;;; e2" := (if e1 then e2 else !!) (right associativity, at level 60).
Notation "x <-- e1 ; e2" := (match e1 with
                               | inright _ => !!
                               | inleft (exist x _) => e2
                             end)
(right associativity, at level 60).


Lemma hasType_det: forall e t1, hasType e t1 -> forall t2, hasType e t2 -> t1 = t2.
Proof.
  intros.
    destruct e. inversion H. inversion H0. trivial.
    destruct e1; destruct e2;
      inversion H; inversion H0; trivial.
    inversion H; inversion H0; trivial.
    inversion H; inversion H0; trivial.
Qed.

Lemma test1: forall b e1, ~ hasType (Plus e1 (Bool b)) TNat.
Proof.
  unfold not.
  intros.
  assert (hasType (Bool b) TBool). apply HtBool.
  induction e1;
  inversion H; subst;
  assert (TNat = TBool);
  try( apply hasType_det with (Bool b); assumption );
  discriminate.
Qed.

Lemma test2: forall b e1, ~ hasType (Plus e1 (Bool b)) TBool.
Proof.
  unfold not.
  intros.
  induction e1; inversion H.
Qed.

Lemma test3: forall e1 e0 e3, ~ hasType (Plus e1 (And e0 e3)) TNat.
Proof.
  unfold not.
  intros.
  induction e1;
    inversion H;
    subst;
    inversion H3.
Qed.

Theorem test4: forall e0 e1 e3, ~ hasType (Plus e1 (And e0 e3)) TBool.
Proof.
  unfold not. intros.
  inversion H.

Definition typeCheck' : forall e:exp, {t:type | hasType e t} + {forall t, ~(hasType e t)}.
  refine (fix F (e:exp) : {t:type | hasType e t} + {forall t, ~(hasType e t)}:=
            match e return {t:type | hasType e t} + {forall t, ~(hasType e t)} with
              | Nat _ => [||TNat||]
              | Plus e1 e2 =>
                t1 <-- (F e1);
                t2 <-- (F e2);
                eq_type_dec t1 TNat ;;; eq_type_dec t2 TNat ;;; [||TNat||]
              | Bool _ => [||TBool||]
              | And e1 e2 =>
                t1 <-- (F e1);
                t2 <-- (F e2);
                eq_type_dec t1 TBool ;;; eq_type_dec t2 TBool ;;; [||TBool||]
            end).
  Proof.
    clear F.
    apply HtNat.
    apply HtPlus. subst. assumption. subst. assumption.
    intros. subst. inversion h0. subst. contradiction _H0. reflexivity.
    subst. inversion h0. subst. contradiction _H0. reflexivity.
    subst. destruct t. apply test1. apply test2.
    subst. destruct t. apply test3.
    unfold not. intros. inversion H1.
    unfold not. intros. subst.
      destruct t1. destruct t2.
        contradiction _H. trivial.
        contradiction _H. trivial.
        inversion H. subst. assert (TBool = TNat). apply hasType_det with e1. assumption. assumption. inversion H0.
    unfold not. intros. subst.
      inversion H. subst.
      assert (~ hasType e2 TNat). apply n. contradiction.
    unfold not. intros. subst.
      inversion H. subst.
      assert (~ hasType e1 TNat). apply n. contradiction.
    apply HtBool.
    subst. apply HtAnd. apply h. apply h0.
    unfold not. intros. subst.
      inversion H. subst. destruct t2. assert (TNat=TBool). apply hasType_det with e2. assumption. assumption. contradiction. contradiction _H0. trivial.
    unfold not. intros. subst.
      inversion H. subst. destruct t1. assert (TNat=TBool). apply hasType_det with e1. assumption. assumption. contradiction. contradiction _H. trivial.
    unfold not. intros. subst.
      inversion H. subst.
      assert (~ hasType e2 TBool). apply n. contradiction.
    unfold not. intros. subst.
      inversion H. subst.
      assert (~ hasType e1 TBool). apply n. contradiction.
Defined.

(** Returns a value *)
Eval compute in typeCheck' (Bool true).
Eval compute in typeCheck' (And (Bool true) (Bool false)).

(** Returns a proof that there is no type for the term.  See the type of
  the return value. *)
Eval compute in typeCheck' (And (Bool true) (Nat 3)).

(** [sumor] really does give a good indication of what is returned by the type
  checking function.  The type of [!!] is quite informative. *)

Eval compute in Found (fun x:nat => x>3) 1.
Eval compute in !!.
