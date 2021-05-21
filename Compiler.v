Add LoadPath "./cpdt/src" as CPDT.
Require Import Bool Arith List.
Require Import Omega.
Require Import Lia.
Set Implicit Arguments.

(** Simple enumeration of two binary operation identifiers, [Plus] and
  [Times] *)
Inductive binop : Set := Plus | Times.

(** Simple abstract syntax for an expression language, [exp], with a
  constant value constructed with [Const] and a binary operation [Binop].
  Note that [Binop] is recursive and uses the type [binop] to specify what
  binary operation is being represented.
*)
Inductive exp : Set := 
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp.

(** Denotation function for binary operators.  Note that the return value
 is a function of type [nat -> nat].  Thus, each binary operator is denoted to
 a function from [nat] to [nat].  The binary operation [Plus] denotes
 to the gallina [plus] operation.  The binary operation [Times]
 denotes to the gallina [mult] operator.
*)
Definition binopDenote (b:binop) : nat -> nat -> nat :=
 match b with
  | Plus => plus
  | Times => mult
 end.

(** A couple of experiments showing how [binopDenote] works. *)

Compute (binopDenote Plus) 2 3.
Compute (binopDenote Times) 2 3.
  
(** Recursive function that denotes an [exp] to a [nat]. [Const n] denotes
 to [n].  [Binop b e1 e2] denotes to the operation [(binopDenote b)] applied
 to the denotation of [e1] and [e2].  We might call this function [eval] 
 instead of [binopDenote].
 *)

Fixpoint expDenote (e:exp) : nat :=
  match e with
   | Const n => n
   | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
  end.

(** An experiment to show [expDenote] working as an interpreter *)
Compute expDenote (Binop Times (Binop Plus (Const 2) (Const 4)) (Const 5)).

(** A theorem over addition of natural numbers *)
Theorem ex0: forall x, (expDenote (Binop Plus (Const x) (Const 4))) >= 4.
Proof.
  simpl; induction x; [lia | lia].
Qed.

(** I'm going to take a detour here and define a relational specification
  of [exp] semantics and verify [expDenote] with respect to that
  definition. *)

(** [evalR] is a relation defining a big-step operational semantics for [evalR]
  that we would like to be congruent with the denotational semantics.  [evalR]
  is defined in the canonical Coq style for binary relations.
*)

Inductive evalR : exp -> nat -> Prop :=
| constR: forall n, (evalR (Const n) n)
| plusR: forall n1 n2 v1 v2 ,
    (evalR n1 v1) -> (evalR n2 v2) -> (evalR (Binop Plus n1 n2) (plus v1 v2))
| timesR: forall n1 n2 v1 v2 ,
    (evalR n1 v1) -> (evalR n2 v2) -> (evalR (Binop Times n1 n2) (mult v1 v2)).

Hint Constructors evalR.

Example ex1: (evalR (Const 4) 4).
Proof.
  apply constR.
  Restart.
  info_auto.
Qed.

Example ex2: (evalR (Binop Plus (Const 3) (Const 4)) (plus 3 4)).
Proof.
  apply plusR.
  apply constR.
  apply constR.
  Restart.
  info_auto.
Qed.

(** What we show here is that the relational definition is satisfied by
  the denotational definition.  Every term [t] evaluated using [expDenote]
  produces a value [v] that satisfies [expR t v]. *)

Theorem correctness1: forall e:exp, (evalR e (expDenote e)).
Proof.
  intros e; induction e.
  - apply constR.
  - destruct b; simpl; [apply plusR | apply timesR]; repeat assumption.
Qed.

(** What we've proved is that every call to [(expDenote e)] results in a
    value that satisfies [(evalR e e')].  The interpreter is correct with
    respect to the evaluation relation. *)

(** Now we'll move on to Chlipala's compiler from [exp] to a stack machine.
  [instr] defines the instructions available for a stack machine.  [prog] is
  a list of instructions representing a program. *)

Inductive instr : Set :=
| iConst : nat -> instr
| iBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list nat.

(** Denote the behavior of individual instructions.  Constants evaluate to
  constants that are added to the stack while binary operations operate on
  the top two values on the stack.  [insrDenote] denotes an instruction 
  and initial stack to a lifted stack, [option stack].  [i] is a single
  instruction while [s] is a value stack. [option stack] is the new stack. *)

Definition instrDenote (i:instr) (s:stack) : option stack :=
  match i with
    | iConst n => Some (n :: s)
    | iBinop b =>
       match s with
        | arg1 :: arg2 :: s' => Some ((binopDenote b) arg1 arg2 :: s')
        | _ => None
       end
  end.

(** Denoting a program is folding the instruction denotation function over a
 program and a stack.  When the program is empty, return the stack.  When
 the program is not empty, denote the next instruction along with the stack
 contents. Remember that Denote functions are interpreters.  Therefore
 [progDenote] is an interpreter for programs that are lists of instructions.
 In an odd way, this is a virtual machine.
*)
Fixpoint progDenote (p:prog) (s:stack) : option stack :=
  match p with
    | nil => Some s
    | i :: p' =>
      match instrDenote i s with
        | None => None
        | Some s' => progDenote p' s'
      end
  end.

(** [compile] takes a term in [exp] and creates a [prog] that is a list
  of [instr] instructions.  This is literally what a compiler does - takes
  a program and generates instructions for some machine.  In this case 
  a trivial virtual stack machine.  A [Const] in [exp] becomes the singleton
  list [iConst].  A [Binop b c1 c2] becomes a program for [c1] appended to
  a program for [c2] appended to an [iBinop] for the binary operation. *)

Fixpoint compile (e:exp) : prog :=
  match e with
    | Const n => iConst n :: nil
    | Binop b c1 c2 => compile c2 ++ compile c1 ++ iBinop b :: nil
  end.

(** These examples compile [exp] terms to [prog]. *)
Compute compile (Const 12).
Compute compile (Binop Plus (Const 12) (Const 2)).

(** These examples compile [exp] terms to [prog] and evalutes the result. *)
Compute progDenote (compile (Const 12)) nil.
Compute progDenote (compile (Binop Plus (Const 12) (Const 2))) nil.

(** The first correctness theorem states that the compiler is correct when
  given an expression [e] evaluating [e] directly using [expDenote] gives
  the same result as evaluating the program resulting from compiling [e]
  starting with an empty stack.  [progDenote] returns a stack while [expDenote]
  returns a value.  [(e :: nil)] converts the value into a stack for
  comparison. *)

Theorem compile_correct :
  forall e, progDenote (compile e) nil = Some (expDenote e :: nil).
Proof.
  intros; induction e.
  reflexivity.
  unfold compile. unfold progDenote. simpl. fold compile. fold progDenote.
  unfold expDenote. simpl. fold expDenote.
Abort.

(** This theorem turns out to be quite difficult to prove. But how do we
 know that just by looking the proof process?  Simplifying [progDenote],
 [compile], and [expDenote] transforms the goal into a more regular form.
 How do we know we're stuck?  This is worth thinking about. *)

(** Chlipala starts with a helper lemma that will be used to construct the
 correctness proof.  The theorem states that executing a program with a
 compiled expression added and the same program with the results of
 expression interpretation added to the stack results in the same stack.

 1. compile [e] and append the result to [p].
 2. execute result starting with with stack [s]
 3. evaluate [e] directly and add result to stack [s].
 4. evaluate [p] with [e :: s].

 Nice commuting diagram if you draw the whole thing out.  See
 [Compiler.pdf] for the diagrams.
*)

Lemma compile_correct' : forall e p s,
 (* progDenote (compile e) nil = Some (expDenote e :: nil). *)
    progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).
Proof.
  induction e.
  + intros. unfold compile. unfold expDenote.
    unfold progDenote at 1. simpl. fold progDenote.
    reflexivity.
  + intros. unfold compile. simpl. fold compile.
    unfold expDenote. simpl. fold expDenote.
    rewrite app_ass.
    rewrite IHe2.
    rewrite app_ass.
    rewrite IHe1.
    unfold progDenote at 1. simpl. fold progDenote.
    reflexivity.
Qed.

(** Alternate Lemma proved using an Ltac function to do unfolding and folding
    of functions.  Demonstrates a simple application of Ltac
*)

Ltac simplify_fn f := unfold f; simpl; fold f.
Ltac simplify_fns f := unfold f at 1; simpl; fold f.
Ltac rewrite_Hs := repeat match goal with
                          | [H: _ = _ |- _] => rewrite H
                          end.

Lemma compile_correct'' : forall e p s,
    progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).
Proof.
  induction e.
  + intros.
    unfold compile. unfold expDenote.
    simplify_fn progDenote.
    reflexivity.
  + intros.
    simplify_fn compile.
    simplify_fn expDenote.
    rewrite app_ass.
    rewrite IHe2.
    rewrite app_ass.
    rewrite IHe1.
    simplify_fn progDenote.
    reflexivity.
Qed.

Theorem compile_correct :
  forall e, progDenote (compile e) nil = Some (expDenote e :: nil).
  intros.
  rewrite (app_nil_end (compile e)).
  rewrite compile_correct'.
  reflexivity.
Qed.

(** Examining Types *)

Inductive type : Set := Nat | Bool.

Inductive tbinop : type -> type -> type -> Set :=
| TPlus : tbinop Nat Nat Nat
| TTimes : tbinop Nat Nat Nat
| TEq : forall t, tbinop t t Bool
| TLt : tbinop Nat Nat Bool.

Eval simpl in TLt.

Inductive texp : type -> Set :=
| TNConst : nat -> texp Nat
| TBConst : bool -> texp Bool
| TBinop : forall t1 t2 t, tbinop t1 t2 t -> texp t1 -> texp t2 -> texp t.

Eval simpl in TNConst 5.
Eval simpl in (TBinop (TEq Nat)) (TNConst 5) (TNConst 6).

Definition typeDenote (t : type) : Set :=
  match t with
    | Nat => nat
    | Bool => bool
  end.

Eval simpl in typeDenote(Nat).
Eval simpl in typeDenote(Bool).

Definition tbinopDenote arg1 arg2 res (b : tbinop arg1 arg2 res)
: typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b with
    | TPlus => plus
    | TTimes => mult
    | TEq Nat => beq_nat
    | TEq Bool => eqb
    | TLt => leb
  end.

Eval simpl in tbinopDenote(TEq Bool).
Eval simpl in tbinopDenote(TLt).

Fixpoint texpDenote t (e: texp t) : typeDenote t :=
  match e with
    | TNConst n => n
    | TBConst b => b
    | TBinop b e1 e2 => (tbinopDenote b) (texpDenote e1) (texpDenote e2)
  end.

Eval simpl in texpDenote (TNConst 42).
Eval simpl in texpDenote (TBConst true).
Eval simpl in texpDenote (TBinop TTimes (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)).
Eval simpl in texpDenote (TBinop (TEq Nat) (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)).
Eval simpl in texpDenote (TBinop TLt (TBinop TPlus (TNConst 2) (TNConst 2)) (TNConst 7)).

Definition tstack := list type.

Inductive tinstr : tstack -> tstack -> Set :=
| TiNConst : forall s, nat -> tinstr s (Nat :: s)
| TiBConst : forall s, bool -> tinstr s (Bool :: s)
| TiBinop : forall arg1 arg2 res s,
              tbinop arg1 arg2 res -> tinstr (arg1 :: arg2 :: s) (res :: s).

Inductive tprog : tstack -> tstack -> Set :=
| TNil : forall s, tprog s s
| TCons : forall s1 s2 s3,
            tinstr s1 s2
            -> tprog s2 s3
            -> tprog s1 s3.

Fixpoint vstack (ts: tstack) : Set :=
  match ts with
    | nil => unit
    | t :: ts' => typeDenote t * vstack ts'
  end%type.

Inductive unit : Set :=
| tt.

Check unit.
Check tt.

Theorem unit_singleton : forall x : unit, x = tt.
  intros.
  induction x.
  reflexivity.
Qed.

Check unit_ind.
Check list_ind.

(** Operational semantics not ready yet 

Inductive evalR' : exp -> exp -> Prop :=
| plusR': forall n1 n2 v1 v2,
    (evalR' n1 v1) -> (evalR' n2 v2) -> (evalR' (Binop Plus n1 n2)
                                              (match (n1,n2) with
                                                 ((Const v1'),(Const v2')) => (Const (plus v1' v2')) end))
| timesR': forall n1 n2 v1 v2,
    (evalR' n1 v1) -> (evalR' n2 v2) -> (evalR' (Binop Times n1 n2)
                                              (match (n1,n2) with
                                                 ((Const v1'),(Const v2')) => (Const (mult v1' v2')) end)).
*)
