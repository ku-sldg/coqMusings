(** * Notes for Subset Types and Variations

    from _Computer Programming with Dependent Types_ by Adam Chlipala 
    
    Note that I do not use [Set Implicit Arguments] nor do I use [crush].  These
    are wonderful tools, but I find using them makes things a bit more
    difficult to learn.
 *)

(* [Extraction] is not explicitly required in the original text, but is now
 * a library that must be imported explicitly *)
Require Extraction.
(* [Lia] is a handy although les general replacement for [crush]. *)
Require Export Lia.

(* When we do extract code, extract to Haskell rather than OCaml *)
Extraction Language Haskell.

(** ** 0>0

    First create a proof that [0>0] is [False].  This is an obvious result, but
    we need it in our deinition of a protected [pred] function. More importantly
    there are a number of interesting things we can learn by looking at such a
    proof:
 *)

Lemma zero_gtz : 0 > 0 -> False.
  intros.
  inversion H.
Qed.

(** [zero_gtz] is a value of type [0>0 -> False].  Literally, it is a function from a
    value of type [0>0] to a value of type [False].  Curry-Howard tells us that
    types are theorems and values from types are proofs of those theorems. 
    Considering that, [ztgz] says if provided a proof of theorem [0>0] a proof
    of theorem [False] results. However, [False] has no proofs meaning that if [0>0]
    has a proof then [False] must have a proof and an inconsistency would result.
    Thus, [0>0] similarly can have no proofs.
 *)

(** The Curry-Howard isomorphism tells us that types are theorems and values
    are proofs. A quick demonstration of definitions makes this quite evident
    using Coq's concrete syntax.  The following is a proof of [3>0] that
    might be a bit surprising:
 *)

Definition three_gtz: 3>0. Proof. lia. Qed.

(** Looking at the syntax is revealing.  A new identifier is being
    defined in the canonical Coq fashion.  It's name is [three_gtz] and its type
    as designated by the ":" is [3>0].  It's value is defined using a
    proof building script that is invoked by ".".  I used the [Definition]
    keyword rather than [Theorem] to emphasize that we are defining a
    new Coq identifier that is just like any other Coq identifer with a type
    and a value that must be of that type.  If you doubt this, take a look
    at the value of our new identifier:
 *)

Print three_gtz.

(** While not a fun read, the value of [three_gtz] is a Coq function that
    represents a proof value.  Types are theorems and values are proofs.
    In this case, our proof is a Coq function.
    
    If it's the case that proofs are values then we should be able to do
    with them what we do with any other value.  Specifically, write functions
    that take proofs as arguments.  The value:
    
    [fun pf:3>0 => 4]
    
    is such a function.  Given [three_gtz] is a proof of the theorem [3>0] or a
    value of type [3>0] we ought to be able to call our new function on
    that value:
 *)

Eval compute in ((fun pf:3>0 => 4) three_gtz).

(** As expected, this application results in the value [4]. We know [three_gtz] is
    of type [3>0] from its definition, the function accepts it and returns
    [4].  No magic, just application of beta reduction.

    Let's create another proof that 4 is
    greater than 0:
 *)

Theorem four_gtz: 4>0. Proof. lia. Qed.

(** and use that proof in the same way as a parameter to this function:

[Eval compute in ((fun pf:3>0 => 4) four_gtz).]

    In contrast this function application will not evaluate because type
    checking fails with the message:

The term "four_gtz" has type "4 > 0" while it is expected to have type
 "3 > 0".

    [four_gtz] is of type [4>0] not [3>0].  But both propositions are are true!
    Shouldn't the function evaluate both and be just fine with [True]?  When
    we evaluate the two proofs we do in fact get a true result.  But their
    values are not what is being compared.  It is their _types_ that are 
    not the same.  Thus the emphasis on this failing during type ckecking.
    This example will not fail at runtime because it will never get
    to runtime and that is precisely what we want.

    But why would we do this?  The value of the function does not depend on
    the input proof.  As long as we provide a value of type [3>0] the
    function always results in 4.  Said differently, as long as we can _prove
    3>0_ this function will run.  The function depends on a proof and we
    can use this in many ways.

    Now let's pick up Chliplala's story of dependent types using the
    built-in function [pred] as an first example
    using proofs as arguments to functions.  When
    looking at [pred] over [nat], the result of [pred 0] presents a problem that
    we've all seen.  Is this an error?  Is it [0]?  Should we us an [option]
    type or a monad?  The
    built-in Coq function defines [pred 0] in a common way:
 *)

Print Init.Nat.pred.

(** and [pred] extracts to code that produces [0] in the case of input [0]:
 *)

Extraction pred.

(** This is not horrible, but it can be a problem as it breaks theorems we
    might like to have.

    In fact, [pred 0] should be undefined and should never be allowed.  [pred]
    should only be called on values strictly greater than
    [0], a _subset_ of [nat].  One way to ensure this is to check at runtime and
    throw an error if the condition is not met.  A better solution would be to
    statically ensure the problem will never occur.  What if we required a proof
    that the input to [pred] is greater than [0] each time [pred] is called?  Sounds
    a great deal like what we just did with proofs as arguments to functions.
    
    [pred_strong1] is Chlipala's new version of [pred] that will require us to do the
    proof we need before taking the predecessor.  Let's start with its signature:

    [Definition pred_strong1 (n:nat) : n>0 -> nat]

    [pred_strong1] is defined as a function that takes a single argument [n:nat]
    and returns a function value of type [n>0 -> nat].  This looks like our functions
    with proofs as arguments except for the appearance of the parameter [n] in the
    type.  As it turns out we only know the value of [n] when [pred_strong1] is
    instantiated.  If our input is [3] then we need a proof of [3>0]. If [x+7]
    we need a proof of [x+7>0].

    The signature for [pred_strong1] gives us exactly this.  It specializes the
    proof for the input value.  Consider [3] and
    [x+7] in the context
    of [pred_strong1]:

    [(pred_strong1 3) : 3>0 -> nat]
    [(pred_strong1 x+7) : x+7>0 -> nat]

    Something quite subtle is happening here.  When insantiating [pred_strong1]
    it specializes the theorem we must prove.  Theorems are types, right?  So the
    the effect is changing the _type_ of [pred_strong1] based on its actual parameter.
    The type depends on an input value.  Type systems where this occurs are called
    _dependent_ because types depend on values.  The type of [pred_strong1] depends
    on and changes based on its input.
 *)

(** Before moving on to Chlipala's full definition of [pred_strong1] lets define a
    stronger [pred] that only uses what we've learned so far.  Consider the
    following definition of [pred_strong0], a first step towards a dependently
    typed [pred] function:
 *)

Definition pred_strong0 (n:nat) : n>0 -> nat :=
  match n with
  | O => fun _ => 42
  | S n' => fun _ => n'
  end.

(** Lots going on here, but lets start with the signature.  It is the same as
    [pred_strong1].  Given a natural number it will return a function from
    a proof that number is greater than zero to a natural number. The function
    body creates a return value for each constructor of [nat].  For [S n'], numbers
    1 and greater, the function takes any proof of the correct type and returns [n'], 
    the predecessor of [n].  Remember, the proof value itself is not important.  Only
    that it is a proof of the right theorem matters.  Using a wildcard match ignores
    the value and type checking ensures it will be of the right type. Looking at the
    returned function we have:
 *)

Eval compute in pred_strong0 3.

(** a function that given a proof of [3>0] will return [3].  Recall that [three_gtz] is 
    such a proof, a value of type [3>0]. Evaluating [pred_strong0 3 three_gtz] gives the
    result we want:
 *)

Eval compute in pred_strong0 3 three_gtz.

(** The case for [0] is similar to the case for [S n'].  Once again the proof value is
    irrelevant, but it must be of the correct type.  The value returned is a function
    that given a proof of [n>0] will return [42].  Looking at the returned function
    we have:
 *)

Eval compute in pred_strong0 0.

(** It would seem that [pred_strong0] works even for 0 as we get back a function
    similar to the one for [3].  However, we need a proof of [0>0] to fully evaluate
    [pred_strong0 0 zero_gtz] and such a proof does not exist.  [pred_strong0] does
    produce a value, but that value is waiting for a proof it will never get, thus
    [42] will never be returned.  Finally we see the power of dependent types.
    [pred_strong0 0 pf] will never type check for any value [pf].
 *)

(** The ony true distinction between Chlipala's [pred_strong1] and [pred_strong0] is
    the return value for the [0] case.  We used the absurd value [42].  Chlipala
    constructs a far more interesting absurd value that is worth taking a look at
    in detail.  First, Chlipala's [pred_strong1] has the form:
 *)

Definition pred_strong1 (n:nat) : n>0 -> nat :=
  match n with
  | O => fun pf : 0>0 => match zero_gtz pf with end
  | S n' => fun _ => n'
  end.

(** Let's confirm that [pred_strong1] and [pred_strong0] do the same thing:
 *)

Theorem ps1ps2: forall (n:nat) (pf:n>0), pred_strong0 n pf = pred_strong1 n pf.
Proof.
  intros.
  destruct n.
  inversion pf.
  reflexivity.
Qed.

(** This should not work, but it does! For the [(S n')] case the proof is obviously true.
    For the [0] case [pred_strong0] returns [42] and [pred_strong1] doesn't.
    However, the [0] case assumes the existence of [pf : 0>0] and creates an
    assumption [pf : 0>0].  One call to [inversion] ends that proof because [0>0]
    is inconsistent.

    Why create the absurd value to return?  It would seem to simply complicate the
    definition!  In a sense it does, but for an interesting reason.  Let's look at
    the value in isolation: (parentheses are mine.) 

    [fun pf : 0>0 => match (zero_gtz pf) with end]

    The function accepts a proof of [0>0].  If that proof is provided it evaluates
    [zero_gtz] on that proof.  Remember the type of [zero_gtz] is a proof of [0>0] to [False].
    Thus, the [match] expression becomes [match False with end].  Now we're stuck.
    We're matching the values of [False] with the cases between [with] and [end].
    There are no values of [False] and there are no cases, thus there is no value to
    return.  Literally, there is no value!  Thankfully, the [match] will never
    be evaluated because the [0] case for [pred_strong1] cannot occur.

    What Chlipala is doing is fascinating.  If the impossible case is evaluated an
    impossible value will be returned.  When understood, this makes more sense than
    returning [42] or any other arbitrary value.
 *)

(** Coq can be pretty smart at infering values when they are not provided.
    The proofs that each input to [pred_strong1] is greater than zero
    can get old.  We can leave a hole in the call to [pred_strong1] for the
    proof and see if Coq will find it:
 *)

Eval compute in pred_strong1 2 _.

Eval compute in pred_strong1 (pred_strong1 2 _) _.

(** Sure enough, Coq can find the values for our proofs when we leave a hole
    to fill.  Even if we nest [pred_strong1] calls.  What happens when we
    try the same thing with 0:
 *)

Eval compute in pred_strong1 0 _.

(** Oddly, [pred_strong1 0 _] does not fail to type check.  It even evaluates
    to something:

    <<
     = match zero_gtz ?g return nat with
       end
     : nat
    >>

    That something is not a value.  Instead of failing, Coq tries to fill in
    what it can.  Thus we see the absurd return value, but with a meta-variable
    for the proof of [0>0].  This makes sense.  Coq cannot find the proof
    because it does not exist.  It leaves the proof out and stops calculating
    when it cannot calculate further.  Thus, we get a constraint on the return
    value, but not a value.
 *)

(** A _predicate subtype_ is a type created using a predicate and set comprehension to
    filter an existing type.  In mathematics we do this the time using the notation
    {x:A|P(x)} where x is a variable of some type A and P(x) is a predicate that filters
    A. Predicte subtypes do exactly the same thing for types. {x:A|P(x)} can easily
    be view as the subtype of A containing elements that satisfy P.

    Coq uses the inductive type [sig] to represent predicate subtypes.  Specifically:

<<
Inductive sig (A : Type) (P : A -> Prop) : Type :=
   exist : forall x : A, P x -> {x : A | P x}
>>

    In this definition, [A] is the
    type being filtered while [P] defines the predicate that restricts [A].  [exist] is
    the single constructor for values of the subset type.  In the definition of
    [sig] the term [exist] is a constructor and should not be confused with the 
    quantifer [exists].

    Defining a [sig] type is done by specifying th filtering predicate.  The following
    defines a nonzero type: *)

Eval compute in sig (fun n => n > 0).

(** Coq easily finds a value for [A], by examining the argument to [sig] and
    using its domain type.

    Coq introduces a notation that makes [sig] types particularly easy to define and
    read.  An alternate definition of [nonzero] uses this notation that borrows from
    set comprehension:
 *)

Definition nonzero : Type := { n : nat | n > 0 }.

(** [nonzero] is the set of all [n:nat] such that [n>0].
 *)

Lemma one_gtz: 1>0. Proof. lia. Qed.

(** Now let's use [exist] to create some values of this nonzero type.  First, 
    lets explicitly define the value [1] as an element of nonzero:
 *)

Eval compute in exist (fun m:nat => m>0) 3 three_gtz.

(* Explain why 1 <= M is in the result *)

(** The filtering function is the first argument - a simple function that returns
    [True] when it's argument is greater than [0].  The value lifted into this subset
    type is [3].  Finally, the proof that [3] satisfies the filter is [three_gtz].

    Coq can frequently figure out values if we leave holes.  In this case Coq
    figures out the filtering function from the proof:
 *)

Eval compute in exist _ 1 one_gtz.

(** and we get the same value up to variable renaming.

    We can also leave off the proof, but the result is quite different:
 *)

Eval compute in exist (fun m:nat => m>0) 1 _.

(** In this case the value is waiting for a proof value.  The [?g] variable is
    a meta variable like we see when using [eapply] or [econstructor]. Coq gives
    us as much of the value as it can and waits for us to provide the rest.  We
    will see this in action when we start using [refine].

    Now back to [pred] definitions.  Hopefully you can imagine where we're headed.
    We now have a type that includes values greater than 0.  If we use that type
    as the domain type for [pred] we should get what we want:
 *)

Definition pred_strong2 (s : {n : nat | n > 0}) : nat :=
  match s with
    | exist _ O pf => match zero_gtz pf with end
    | exist _ (S n') _ => n'
  end.

(** [pred_strong2] should be reasonably easy to read at this point.  It takes
    a single argument [s] of type [{n:nat | n>0}], a [nat] that is greater than [0].
    The [match] that implements the function pulls apart the [exist] constructor
    and looks at [0] and [S n]

    Let's look at a few examples of [pred_strong2] at work.  First, a rather mundane
    example of calculating [pred 2] using [pred_strong2]:
 *)

Lemma two_gtz: 2 > 0. Proof. lia. Qed.

Eval compute in pred_strong2 (exist (fun n => n>0) 2 two_gtz).

(** We can allow Coq to find values for us by specifying holes.  The next two
    examples calculate [pred 2] as before, but leave out the predicate and proof
    respectively: 
 *)

Eval compute in pred_strong2 (exist _ 2 two_gtz).

Eval compute in pred_strong2 (exist (fun x => x>0) 2 _).

(** Both the proof and predicate can be left out.  When the lifted value is greater
    than 0 things work quite well as the value matches the second case for
    [pred_strong2]:
 *)

Eval compute in pred_strong2 (exist _ 1 _).

(** If we try [0] the absurd value is returned and cannot be caculated.  Note
     the meta-variable [?g] that is the proof argument to [zero_gtx]:
 *)

Eval compute in pred_strong2 (exist _ 0 _).

(** Now a couple of nested calls to [pred_strong2].  The first calculates a value
    while the second does not because we try to take the predecessor twice on
    [1]:
 *)

Eval compute in pred_strong2 (exist _ (pred_strong2 (exist _ 3 three_gtz)) two_gtz).

Eval compute in pred_strong2 (exist _ (pred_strong2 (exist _ 1 one_gtz)) _).

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
  
Print False_rec.
  
Print False_rect.
  
Print pred_strong4.

Eval compute in pred_strong4 2 two_gtz.

Eval compute in pred_strong4 2 _.

(** Let's take all this cool stuff and build a dependently typed [Stack].
    We'll start with an inductive definition for [Stack] of [nat]. We'll start
    out with a classic cosntructive definition of a [Stack] data type:
 *)

Inductive Stack : Type :=
| Empty : Stack
| Push : nat -> Stack -> Stack.

(** We'll start with a trivial proof that [Push] never results in [Empty].
    This is a simple application of discriminate to show that the two
    constructors produce distinct values.  We'll need this later when we
    need to show that a stack is not empty:
 *)

Lemma push_neq_empty : forall (t:nat) (s:Stack),
                         Push t s <> Empty.
Proof.
  discriminate.
Qed.

(** Trival proof that [Empty] not equal to [Empty] is [False].  Again, we'll
    need this later when we instantiate [s <> Empty] with [Empty].
 *)

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
    we provide that proof.
 *)

Definition pop(s:Stack):s<>Empty -> Stack := 
  match s with
    | Empty => fun pf : (Empty <> Empty) => match empty_neq_empty pf with end
    | Push _ s' => fun _ => s'
  end.

(** Note the absurd value returned in the [Empty] case is constructed exactly
    the way the absurd value for [pred_strong].
 *)

(** Let's do a simple proof that popping the result of pushing is the stack
    we started with:
 *)

Example pop_push: forall n s, (pop (Push n s)) (push_neq_empty n s) = s.
Proof.
  reflexivity.
Qed.

(** What happens when we [pop Empty]?  The same thing that happened for
    [pred_strong 0].  Coq tries to find a value, but it cannot because the proof
    that [Empty <> Empty] cannot be proved:
 *)

Eval compute in pop Empty.

(** If we extract [pop] to Haskell we get the function we would expect with two
    cases.  If you look at the [Empty] case Haskell throws an error that reports
    "absurd case".  However, this case will never be entered because of the proofs
    we need to do during evaluation:
 *)

Extraction pop.

(** Simple example that [pop] on [Push 1 Empty] is [Empty].  It's not the
    values that are interesting, but the arguments to [pop].  The initial
    call to [pop] is a stack of size one. The result is a function from
    [Push 1 Empty <> Empty] to [Empty].  The second argument to [push] is
    an instance of the proof [push_neq_empty] for [Push 1 Empty].  The type of
    this proof is [Push 1 Empty <> Empty], thus the result is [Empty] as
    expected.
 *)

Example pop_push_id: forall n s, (pop (Push n s)) (push_neq_empty n s) = s.
Proof.
  reflexivity.
Qed.

(** Alternative definition of [pop] using [refine] to refine a partial proof
    that generates the function.
 *)

Module PopFunction.

Definition pop(s:Stack):s<>Empty -> Stack := 
  match s with
    | Empty => fun pf : (Empty <> Empty) => match empty_neq_empty pf with end
    | Push _ s' => fun _ => s'
  end.

Eval compute in (pop (Push 2 (Push 1 Empty)))
                  (push_neq_empty 2 (Push 1 Empty)).

(** Let's do a simple proof that popping the result of pushing is the stack
    we started with:
 *)

Example pop_push: forall n s, (pop (Push n s)) (push_neq_empty n s) = s.
Proof.
  reflexivity.
Qed.

End PopFunction.
  
Module PopSubset.

Definition pop(s:{s':Stack | s'<>Empty}) : Stack :=
  match s with
    | exist _ Empty pf => match empty_neq_empty pf with end
    | exist _ (Push _ s') _ => s'
  end.

Definition top(s:{s':Stack | s'<>Empty}) : nat :=
  match s with
    | exist _ Empty pf => match empty_neq_empty pf with end
    | exist _ (Push t _) _ => t
  end.

Eval compute in {s' : Stack | s' <> Empty}.

Check exist.

(** [exist] takes a predicate, value, and proof of the predicate.  Note the type of
    the proof and the type of the predicate
 *)

Eval compute in exist (fun s => s <> Empty)
                      (Push 1 Empty)
                      (push_neq_empty 1 Empty).

(** Some simple examples of [pop] and [top] and work with good lifted stacks.
*)

Eval compute in pop (exist (fun s => s <> Empty)
                           (Push 1 Empty)
                           (push_neq_empty 1 Empty)).

Eval compute in top (exist (fun s => s <> Empty)
                           (Push 1 Empty)
                           (push_neq_empty 1 Empty)).

Eval compute in pop (exist (fun s => s <> Empty)
                           (Push 1 (Push 2 Empty))
                           (push_neq_empty 1 (Push 2 Empty))).

Eval compute in top (exist (fun s => s <> Empty)
                           (Push 1 (Push 2 Empty))
                           (push_neq_empty 1 (Push 2 Empty))).

Eval compute in pop (exist (fun s => s <> Empty)
                           (Push 1 (Push 2 (Push 3 Empty)))
                           (push_neq_empty 1 (Push 2 (Push 3 Empty)))).

Eval compute in top (exist (fun s => s <> Empty)
                           (Push 1 (Push 2 (Push 3 Empty)))
                           (push_neq_empty 1 (Push 2 (Push 3 Empty)))).

(** Define [push] that takes any stack and produces a nonempty stack
    [push] lifts [Push] into the subset type.  Note that push always
    produces a nonempty stack.  If it didn't, the lift would not be
    possible.
 *)

Definition push(x:nat)(s:Stack):{s':Stack | s'<>Empty}:=
  exist (fun s => s <> Empty) (Push x s) (push_neq_empty x s).

(** The Coq [sig] type is an implementation of the general concept of a
    _sigma type_.  A signma type is simply a dependent pair where the elements
    of the pair depend on each other.  Four our purposes, [sig] is a pair
    consisting of a value and a proof over that value.
    [proj1_sig] projects the value from [sig] value.  Creating a stack with
    [push] results in a subset type stack, thus [proj1_sig] produces the
    regular stack:
 *)

Eval compute in proj1_sig (push 1 Empty).

(** [proj2_sig] projects the proof value from a [sig] value. Creatig a stack
    with [push] results i a subset type stack, thus [proj2_sig] produces the
    proof of nonempty:
 *)

Eval compute in proj2_sig (push 1 Empty).

(** Proof for later that [pop] after two [push] operations results in a
    nonempty stack.
 *)

Lemma pop_push_push_neq_empty:
  forall n m, (pop (push n (proj1_sig (push m Empty)))) <> Empty.
Proof.
  intros n m.
  simpl.
  discriminate.
Qed.

Eval compute in (top
                   (exist (fun s => s <> Empty)
                          (pop (push 2 (proj1_sig (push 1 Empty))))
                          (pop_push_push_neq_empty 2 1))).

(** Let's do a quick example mixing [push], [pop], and [top] in a single
    expression. Without fancy sigma types, the theorem we would like to
    verify is this:

<<
forall n m, (top (pop (push n (push m Empty)))) = m
>>

    Using our dependent stack we express the theorem as [mixed] here with a
    trivial proof:
 *)

Example mixed: forall n m, (top
                         (exist (fun s => s <> Empty)
                                (pop (push n (proj1_sig (push m Empty))))
                                (pop_push_push_neq_empty n m)))
                      = m.
Proof.
  reflexivity.
Qed.

(** There is quite a bit going on in this definition and its proof.  Remember
    that [push] takes a stack and generates a dependent stack from it.  Thus,
    [push m Empty] pushes [m] on the empty stack and returns a new stack
    with a proof that it is not empty.  We would like to push [n] on that
    result to create a stack of size 2.
    Recall that neither [push] or the constructor [Push] accept a dependent
    stack as input.  We use [proj1_sig] to extract the stack value and again
    use [push] to create a new dependent stack with a proof that it is not
    empty.

    Now we [pop] the result.  Unlike [push], [pop] expects a dependent stack,
    thus no need to project a value from [push].  We know [pop] is safe
    because a proof its argument is not empty exists.  [pop] produces an
    ordinary stack because there is no proof that [pop s] is nonempty for
    all [s].

    The final operation, [top], requires a dependent stack.  We must know
    the argument to [top] is not empty.  To achieve this we create a dependent
    stack from the result of [pop] by pairing it with the a proof that
    [pop (push n (push m empty))] is not empty.  This proof is done manually
    and provided to the [exist] constructor with the [pop] result.  Now [top]
    safely does its thing knowing its stack argument cannot be empty.

    An observant reader should recognize immediately that the inner dependent
    stack that we project a value from need not be a dependent stack at all.
    The proof that [pop (push n (push m Empty))] is not empty is all we
    really need. The dependent list is included simply to demonstrate
    the projection function.
 *)

End PopSubset.

Module PopDerived.
  
(** What we've been doing to this point is refining the definition of [pop]
    and [top].  We started with definitions that operate on [Empty] and
    [Push] without regard to whether operations could be performed. We
    created a subset type that contains all the stacks that are
    not empty and defined [top] and [pop] over this new type.  What we did
    is add a _precondition_ to [pop] and [top] that defines when they will
    generate good values.  We can statically verify that precondition is
    met ensuring both operations are properly used.
    
    Let's make one more refinement and define when the output of [pop] is
    correct by encoding the requirements of pop's output in its return type.
    Here we are defining a _postcodition_ on the output of [pop] and [top]
    that defines what constitutes a valid output.  Any definition of [pop] or
    [top] must produce an output that meets its postcondition when its
    precondition is met by its input.

    We will define the subset type of possible outputs that contains
    only correct values of [pop].  Think about this carefully.  The
    signature becomes:

<<
pop(x:{x':Stack | pre(x')}) : {z':Stack | post(x,z')}
>>

    where [pre] is true when its argument is a valid input and [post] is true
    when given input [x], [z'] is a valid output. The range set contains _only_
    values that are good outputs, thus _any_ value from the range set is
    good result given some input [x].

    The next definition [pop] uses this approach.  It takes a nonempty
    stack and returns an element of a subset type that contains only those
    elements [s1] of
    [Stack] such that [s = Push x s1].  Note that [s] is the input to
    [pop] so [s1] in [s = Push x s1] is the tail of [s] - the result of
    [pop s].

    The resulting type signature for [pop] is defines as:
 *)
  
  Definition pop(s:{s0:Stack | s0<>Empty}) :
    {s1:Stack | exists x, proj1_sig s = Push x s1}.
    refine (fun s => match s with
                  | exist _ Empty pf => match empty_neq_empty pf with end
                  | exist _ (Push x s') pf => (exist _ s' _)
                  end).


  Definition pop(s:{s0:Stack | s0<>Empty}) :
    {s1:Stack | exists x, proj1_sig s = Push x s1}.

(** where the input is a nonempty [Stack] and the output is a [Stack s1] that
    some [x] pushed on it is [s].

    Let's look at this signature in a slightly different form:

<<
Lemma pop: d:{s0:Stack | s0<>Empty} -> r:{s1:Stack | exists x, s = Push x s1}.
>>
    This is not quite a legal Coq lemma because the names [s] and [r]
    are included
    in the signature to allow reference.  Regardless,
    this looks agreat deal like a Lemma [pop] stating that given nonempty [d]
    some [r] results that equals popping [d].  Or maybe a function [pop]
    that takes a nonempty stack and returns result that is it's tail.  Lemma
    or function?

    Turns out it's both. Types are Theorems so the type of [pop] is a
    theorem.  Proofs are Values so the Proof of this theorem is a Value
    of this Type.  The proof _is_ the function we're looking for.  Because
    Coq is constructive, the proof is an executable function.

    Let's
    derive the value of [pop].  The definition states that [pop s] is an
    element of set of correct results.  Curry-Howard anyone?  Types are
    theorems and values are proofs.
 *)
  
  Proof.
    inversion s.
    destruct x.
    * assert (Empty = Empty). reflexivity. contradiction.
    * exists (match (proj1_sig s) with Empty => Empty | Push x s => s end).
      exists (match (proj1_sig s) with Empty => 42 | Push x s => x end).
      destruct s. simpl.
      destruct x0.
      ** assert (Empty=Empty). reflexivity. contradiction.
      ** reflexivity.
  Defined.

(** Note that this proof ends with [Defined] rather than [Qed].  This exposes
    the function and makes it executable.

    Take a look in the midding of the proof were there are two [exists] uses.
    They correspond with the calculation of the [top] and [pop] of the
    input stack.  These are the critical steps because without these
    calculations [pop] would not be derivable.  What we would have
    written as the definition of [pop] is a part of the proof derivation.
    The clear advantage here is the subset types for inputs and outputs
    enforce corretness, thus the definition of [pop] is correct.  Make
    sure to walk through the proof to understand how the extistentials
    do their job.

    The resulting function is quite ugly, but we can look at it if we want
    to:
 *)
  
  Print pop.

  Extraction pop.

(** and more importantly we use it to calculate [pop] for several
    different stack values:
 *)

  Eval compute in proj1_sig
                    (pop
                       (exist _ (Push 1 (Push 2 Empty))
                              (push_neq_empty 1 (Push 2 Empty)))).
  
  Eval compute in proj2_sig
                    (pop
                       (exist _ (Push 1 (Push 2 Empty))
                              (push_neq_empty 1 (Push 2 Empty)))).
  
  Eval compute in (pop (exist _ Empty _)).

(** We can do the same with [top], automatically deriving its value:
 *)
  
  Definition top(s:{s0:Stack | s0<>Empty}):
    {x:nat | exists s1, proj1_sig s = Push x s1}.
  Proof.
    inversion s.
    destruct x.
    * assert (Empty = Empty). reflexivity. contradiction.
    * exists (match (proj1_sig s) with Empty => 42 | Push x s => x end).
      exists (match (proj1_sig s) with Empty => Empty | Push x s => s end).
      destruct s. simpl.
      destruct x0.
      ** assert (Empty=Empty). reflexivity. contradiction.
      ** reflexivity.
  Defined.

  Eval compute in proj1_sig
                    (top
                       (exist _ (Push 1 (Push 2 Empty))
                              (push_neq_empty 1 (Push 2 Empty)))).
  
  Eval compute in proj2_sig
                    (top
                       (exist _ (Push 1 (Push 2 Empty))
                              (push_neq_empty 1 (Push 2 Empty)))).
  
(** [Empty] is the interesting case.  [Eval] gives a result, but that 
    result cannot be reduced to a value because of the subset types.
 *)
 
  Eval compute in (top (exist _ Empty _)).

End PopDerived.

Module PopRefine.

  Definition pop : forall (s:Stack), s<>Empty -> {t : Stack | exists x, s = Push x t}.
    refine (fun s =>
              match s with
              | Empty => fun _ => False_rec _ _
              | Push _ s' => fun _ => exist _ s' _
              end).
    apply empty_neq_empty. assumption.
    exists n. reflexivity.
  Defined.
  
  Eval compute in (pop (Push 0 Empty)) (push_neq_empty _ _).
  
(** Let's do a simple proof that popping the result of pushing is the stack
    we started with:
 *)
  
  Eval compute in (pop (Push 0 Empty)) (push_neq_empty 0 Empty).
  
  Example pop_push: forall n s, proj1_sig
                             ((pop (Push n s)) (push_neq_empty n s)) = s.
  Proof.
    reflexivity.
  Qed.
  
  Notation "!" := (False_rec _ _).
  
  Notation "[ e ]" := (exist _ e _).
  
  Definition pop' : forall s, s<>Empty -> {s1:Stack | exists x, s = Push x s1}.
    refine (fun n =>
              match n with
              | Empty => fun _ => !
              | Push n s => fun _ => [s]
              end).
    unfold not in n0. apply n0. reflexivity.
    exists n. reflexivity.
  Defined.

  Eval compute in pop (Push 3 Empty) (push_neq_empty 3 Empty).

End PopRefine.

Module PopDefinition.

(** [Program Definition] is an extension to Coq that allows defining
    _predicate subtypes_ in a manner similar to PVS.  This approach automates
    some of the proving and bookkeeping required by generating and
    attempting verification of obligations from the program specification.
    
    This specification uses [Program Definition] to define a [pop] that
    satisfies the same requirements we've been using previous.  The
    signature defines a function that takes [s:Stack] and a proof that
    [s] is not empty.  Note that we don't care about the proof, just that
    it exists.  Thus the wildcard instead of an unused parameter.

    The return value is roughly the same type we just used.  Specfiically,
    a subset type that contains all the stacks that are the input stack
    with the top value removed:
 *)
  
  Program Definition pop(s:Stack) (_ : s <> Empty) :
    {s':Stack | exists x, s = Push x s'} :=
    match s with
    | Empty => _
    | Push _ s' => s'
    end.

(** The body of the definition is what one might expect with one interesting
    ommission.  The return value when given [Empty] is a hole.  We don't
    care what is returned in that case because it will never occur and the
    proof [s<>Empty] ensures that.  The notation says exactly what it
    should - we don't care about the [Empty] case.

    Now the cool stuff.  [Program Definition] automatically generates
    proof obligations to ensure the properties defined in the signature
    are satisifed by the implementation.  There are two obligations here.
    The first is solved automatically by a tactic defined to discharge
    oblications.

    The second we have to do ourselves. Use the [Obligation] command to
    first retrieve the remaining obligation.  Then it is a proof just
    like any other. *)
  
  Obligation 2 of pop.
  exists wildcard'. reflexivity. Defined.

(** And now we have yet another [pop] that given a stack and a proof
    produces a correct result.  Again, this [pop] is verified and
    cannot be used in bad ways. *)
  
  Eval compute in proj1_sig (pop (Push 2 Empty) (push_neq_empty 2 Empty)).

  Eval compute in proj1_sig (pop (Push 1 (Push 2 Empty))
                                 (push_neq_empty 1 (Push 2 Empty))).
  
End PopDefinition.

