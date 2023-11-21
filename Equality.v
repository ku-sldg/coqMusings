Set Implicit Arguments.
Set Asymmetric Patterns.

Definition pred' (x:nat) :=
  match x with
  | 0 => 0
  | S n' => let y := n' in y
  end.


Theorem reduce_me : pred' 1 = 0.
  (* [cbv] reduces the goal using only specified reduction rules *)
  cbv delta. (* delta reduction expands pred *)
  cbv beta.  (* beta reduction replaces the parameter *)
  cbv iota.  (* iota reduction chooses the case to evaluate *)
  cbv beta.  (* beta reduction again *)
  cbv zeta.  (* zeta reduction reduces a let to its body *)
  reflexivity.
Qed.

Theorem reduce_me' : pred' 1 = 0.
  lazy delta.
  lazy beta.
  lazy iota.
  lazy beta.
  lazy zeta.
  reflexivity.
Qed.


(* Using [Definition] implies no recursion and beta reduction is applied *)
Definition id (n:nat) := n.

Eval compute in fun x => id x.

(* Using [Fixedpoint] implies recursion and beta reduction is not fully applied
   to protect from potential non-termination.  There is no recursion here, but
   the [Fixedpoint] definition causes protections to turn on. *)
Fixpoint id' (n:nat) := n.

Eval compute in fun x => id' x.

Fixpoint addLists (ls1 ls2 : list nat) : list nat :=
  match ls1, ls2 with
  | (cons n1 ls1') , (cons n2 ls2') => n1 + n2 :: addLists ls1' ls2'
  | _ , _ => nil
  end.

Eval compute in fun ls => addLists nil ls.

Eval compute in fun ls => addLists ls nil.

Section fhlist.
  Variable A : Type.
  Variable B : A -> Type.

  Fixpoint fhlist (ls : list A) : Type :=
    match ls with
      | nil => unit
      | (cons x ls') => B x * fhlist ls'
    end%type.

  Variable elm : A.

  Fixpoint fmember (ls : list A) : Type :=
    match ls with
      | nil => Empty_set
      | (cons x ls') => (x = elm) + fmember ls'
    end%type.
  
  Fixpoint fhget (ls : list A) : fhlist ls -> fmember ls -> B elm :=
    match ls return fhlist ls -> fmember ls -> B elm with
      | nil => fun _ idx => match idx with end
      | (cons _ ls') => fun mls idx =>
        match idx with
          | inl pf => match pf with
                        | eq_refl => fst mls
                      end
          | inr idx' => fhget ls' (snd mls) idx'
        end
    end.

End fhlist.

Implicit Arguments fhget [A B elm ls].

Section fhlist_map.
  Variables A : Type.
  Variables B C : A -> Type.
  Variable f : forall x, B x -> C x.

  Fixpoint fhmap (ls : list A) : fhlist B ls -> fhlist C ls :=
    match ls return fhlist B ls -> fhlist C ls with
      | nil => fun _ => tt
      | (cons _  _) => fun hls => (f (fst hls), fhmap _ (snd hls))
    end.

  Implicit Arguments fhmap [ls].

