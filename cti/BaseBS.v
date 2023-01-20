Require Import String.

(*
  Syntax

  exp corresponds to exp from small-step, without internal-only forms ([Code],
  [Reflect], [LamC], [LetC]). Instead of explicit names, we use de Bruijn levels
  [Var n], hence [Lam e] instead of [Lam f x e].
*)
Inductive exp : Type :=
  | Lit (n : nat)
  | Var (n : nat)
  | Str (s : string)
  | Lam (e : exp)
  | App (e1 e2 : exp)
  | Cons (a b : exp)
  | Let (e1 e2 : exp)
  | If (c a b : exp)
  | IsNum (e : exp)
  | IsStr (e : exp)
  | IsCons (e : exp)
  | Car (e : exp)
  | Cdr (e : exp)
  | Plus (a b : exp)
  | Minus (a b : exp)
  | Times (a b : exp)
  | Eq (a b : exp)
  | Lift (e : exp)
  | Run (b e : exp).

Inductive val : Type :=
  | Cst (n : nat)
  | Tup (a b : val)
  | Clo (env : list val) (e : exp)
  | Code (e : exp).
