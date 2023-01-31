Require Import String. Open Scope string_scope.

Theorem f : forall (x : bool), if x then string else nat.
Proof.
  destruct x. apply "hello". apply 42. Defined.

Definition f' (x : bool) : if x then string else nat :=
  if x return (if x then string else nat)
  then "hello" else 42.
