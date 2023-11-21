(** The [:>] notation is an implicit cast from things of type [foo] to things
 * of type [sort].  This example is directly from stack overflow:
 *)

Record foo := Foo {
                  sort :> Type;
                  op : sort -> sort -> sort }.

(** In this definition [bar] takes 3 arguments of type [T] where [T:foo].
 * It then calls [op] defined in [foo] as an operation over [sort] on things
 * of type [T].  [x], [y], and [z] are [T], not [sort].  The [:>] notation
 * says whenever you see things of type [foo] they can be implicitly cast
 * to [sort].
 *)

Check sort.
Check op.

Definition bar (T: foo) (x y z: T) : T :=
  (op T x (op T y z)).

Check bar.

Record foo' := Foo' {
                   sort' : Type;
                   op' : sort' -> sort' -> sort' }.

Definition bar' (T': foo') (x' y' z': sort' T') : sort' T' :=
  (op' T' x' (op' T' y' z')).

Check bar'.

Definition bar' (T': foo') (x' y' z': T') : T' :=
  (op' T' x' (op' T' y' z')).
