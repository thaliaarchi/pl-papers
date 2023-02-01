Require Import List. Import ListNotations.

Module ND.

Inductive ND (A : Type) : Type :=
  | SuccessND (a : A)
  | FailND
  | OrND (l r : ND A).
Arguments SuccessND {A} _.
Arguments FailND {A}.
Arguments OrND {A} _ _.

Reserved Notation "m >>= f" (right associativity, at level 60).

Definition ret {A : Type} (a : A) : ND A :=
  SuccessND a.

Fixpoint bind {A B : Type} (m : ND A) (f : A -> ND B) : ND B :=
  match m with
  | SuccessND a => f a
  | FailND => FailND
  | OrND l r => OrND (l >>= f) (r >>= f)
  end
  where "m '>>=' f" := (bind m f).

(* TODO: Should be a set *)
Fixpoint nd {A : Type} (n : ND A) : list A :=
  match n with
  | SuccessND a => [a]
  | FailND => []
  | OrND l r => nd l ++ nd r
  end.

End ND.
Module NDRec.

Inductive NDRec (I O A : Type) : Type :=
  | Success (a : A)
  | Fail
  | Or (l r : NDRec I O A)
  | Rec (i : I) (f : O -> NDRec I O A).
Arguments Success {I O A} _.
Arguments Fail {I O A}.
Arguments Or {I O A} _ _.
Arguments Rec {I O A} _ _.

Reserved Notation "m >>= f" (right associativity, at level 60).

Definition ret {I O A : Type} (a : A) : NDRec I O A :=
  Success a.

Fixpoint bind {I O A B : Type} (m : NDRec I O A) (f : A -> NDRec I O B) : NDRec I O B :=
  match m with
  | Success a => f a
  | Fail => Fail
  | Or l r => Or (l >>= f) (r >>= f)
  | Rec i k => Rec i (fun x => k x >>= f)
  end
  where "m '>>=' f" := (bind m f).

End NDRec.
