(** The following exercises explore an alternative way of defining
    natural numbers, using the so-called _Church numerals_, named
    after mathematician Alonzo Church.  We can represent a natural
    number [n] as a function that takes a function [f] as a parameter
    and returns [f] iterated [n] times. *)

Module Church.
Definition cnat := forall X : Type, (X -> X) -> X -> X.

(** Let's see how to write some numbers with this notation. Iterating
    a function once should be the same as just applying it.  Thus: *)

Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

(** Similarly, [two] should apply [f] twice to its argument: *)

Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

(** Defining [zero] is somewhat trickier: how can we "apply a function
    zero times"?  The answer is actually simple: just return the
    argument untouched. *)

Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

(** More generally, a number [n] can be written as [fun X f x => f (f
    ... (f x) ...)], with [n] occurrences of [f].  Notice in
    particular how the [doit3times] function we've defined previously
    is actually just the Church representation of [3]. *)

(* Definition three : cnat := @doit3times. *)

Definition three : cnat := fun {X:Type} (f:X->X) (x:X) => (f (f (f x))).

(** Complete the definitions of the following functions. Make sure
    that the corresponding unit tests pass by proving them with
    [reflexivity]. *)

(** **** Exercise: 1 star, advanced (church_succ)  *)

(** Successor of a natural number: given a Church numeral [n],
    the successor [succ n] is a function that iterates its
    argument once more than [n]. *)
Definition succ (n : cnat) : cnat :=
  fun {X:Type} (f:X->X) (x:X) => (((n X) f) (f x)).

Example succ_1 : succ zero = one.
Proof.
  unfold succ.
  unfold zero.
  unfold one.
  reflexivity.
Qed.

Example succ_2 : succ one = two.
Proof.
  unfold succ.
  unfold one.
  unfold two.
  reflexivity.
Qed.

Example succ_3 : succ two = three.
Proof.
  unfold two.
  unfold three.
  unfold succ.
  reflexivity.
Qed.

(** [] *)

(** **** Exercise: 1 star, advanced (church_plus)  *)

(** Addition of two natural numbers: *)
Definition plus (n m : cnat) : cnat :=
  fun {X:Type} (f:X->X) (x:X) => (((n X) f) ((m X) f x)).
                                 
Example plus_1 : plus zero one = one.
Proof.
  unfold plus.
  unfold zero.
  unfold one.
  reflexivity.
Qed.

Hint Unfold zero one two three plus.  (** Allows [auto] to solve everything *)

Example plus_1' : plus zero one = one.
Proof.
  auto.
Qed.


Example plus_2 : plus two three = plus three two.
Proof.
  auto.
Qed.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof.
  auto.
Qed.

(** Note that all of the proofs involve only expanding definitions.  Nothing
  more.  That's the beauty of lambda calculus and Church.  Evaluation is
  accomplished via symbolic manipulation only. *)

(** [] *)

(** **** Exercise: 2 stars, advanced (church_mult)  *)

(** Multiplication: *)
Definition mult (n m : cnat) : cnat :=
  (fun {X:Type} (f:X -> X) (x:X) => n X (m X f) x).

Example mult_1 : mult one one = one.
Proof.
  auto.
Qed.

Example mult_2 : mult zero (plus three three) = zero.
Proof.
  auto.
Qed.

Example mult_3 : mult two three = plus three three.
Proof.
  auto.
Qed.

(** [] *)

(** **** Exercise: 2 stars, advanced (church_exp)  *)

(** Exponentiation: *)

(** (_Hint_: Polymorphism plays a crucial role here.  However,
    choosing the right type to iterate over can be tricky.  If you hit
    a "Universe inconsistency" error, try iterating over a different
    type.  Iterating over [cnat] itself is usually problematic.) *)

Check cnat.

Definition exp (n m : cnat) : cnat :=
  (fun {X:Type} (f:X->X) (x:X) =>
     (m (X->X) (fun f' => (fun x' => (n X f' x'))) f) x).

(* (fun X => m (X -> X) (n X)). *)

Example exp_1 : exp two two = plus two two.
Proof.
  auto.
Qed.

Example exp_2 : exp three zero = one.
Proof.
  auto.
Qed.

Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof.
  auto.
Qed.

(** [] *)

End Church.