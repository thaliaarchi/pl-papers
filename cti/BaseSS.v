Require Import String.

(* λ⇅ small-step semantics *)

(* Syntax *)

Inductive UNKNOWN : Type.

Inductive op1 : Set :=
  | Op1_IsNum
  | Op1_IsStr
  | Op1_IsCons
  | Op1_Car
  | Op1_Cdr.

Inductive op2 : Set :=
  | Op2_Plus
  | Op2_Minus
  | Op2_Times
  | Op2_Eq.

Inductive expr : Type :=
  | EX (x : UNKNOWN)
  | ELit (n : UNKNOWN)
  | EStr (s : string)
  | ELam (f : UNKNOWN) (x : UNKNOWN) (e : expr)
  | EApp (e1 e2 : expr)
  | ECons (e1 e2 : expr)
  | ELet (x : UNKNOWN) (e1 e2 : expr)
  | EIf (e1 e2 e3 : expr)
  | EOp1 (o : op1) (e : expr) (* ⊕¹ *)
  | EOp2 (o : op2) (e1 e2 : expr) (* ⊕² *)
  | ELift (e : expr)
  | ERun (e1 e2 : expr)
  | EG (g : UNKNOWN).

Inductive g : Type :=
  | GCode (e : expr)
  | GReflect (e : expr)
  | GLam_c (f : UNKNOWN) (x : UNKNOWN) (e : expr)
  | GLet_c (x : UNKNOWN) (e1 e2 : expr).

Inductive v : Type :=
  | VLit (n : UNKNOWN)
  | VStr (s : string)
  | VLam (f : UNKNOWN) (x : UNKNOWN) (e : expr)
  | VCons (v1 v2 : v)
  | VCode (e : expr).

(* Contexts *)

Inductive M : Type :=
  | Mnil (* [] *)
  | MB (m : M) (* B(M) *)
  | MR (m : M). (* R(M) *)

Inductive E : Type :=
  | Enil (* [] *)
  | EB (e : E). (* B(E) *)

(*
Inductive P : Type :=
  | Pnil (* [] *)
  | PB (q : Q) (* B(Q) *)
  | PR (p : P). (* R(P) *)

Inductive Q : Type :=
  | QB (q : Q) (* B(Q) *)
  | QR (p : P). (* R(P) *)
*)
