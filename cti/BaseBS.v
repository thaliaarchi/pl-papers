Require Import String List.
Import ListNotations.

(*
  Syntax

  exp corresponds to exp from small-step, without internal-only forms ([Code],
  [Reflect], [LamC], [LetC]). Instead of explicit names, we use de Bruijn levels
  [Var n], hence [Lam e] instead of [Lam f x e].
*)
Inductive exp : Type :=
  | Lit (n : nat)
  | Var (n : nat)
  | Lam (e : exp)
  | App (e1 e2 : exp)
  | Cons (a b : exp)
  | Let (e1 e2 : exp)
  | If (c a b : exp)
  | IsNum (e : exp)
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
  | Clo (ρ : list val) (e : exp)
  | Code (e : exp).

Definition env : Type := list val.

(* Definition reflect (s : exp) := *)

Reserved Notation "s -->* v" (at level 40).

Inductive evalms : env * exp -> val -> Prop :=
  | M_Lit ρ n :            (ρ, Lit n)                  -->* Cst n
  | M_Var ρ n v :          nth_error ρ n = Some v ->
                           (ρ, Var n)                  -->* v
  | M_Cons ρ e1 e2 v1 v2 : (ρ, e1)                     -->* v1 ->
                           (ρ, e2)                     -->* v2 ->
                           (ρ, Cons e1 e2)             -->* Tup v1 v2
  | M_Lam ρ e :            (ρ, Lam e)                  -->* Clo ρ e
  | M_Let ρ e1 e2 v1 v2 :  (ρ, e1)                     -->* v1 ->
                           (ρ ++ [v1], e2)             -->* v2 ->
                           (ρ, Let e1 e2)              -->* v2
  | M_App_Clo ρ e1 e2 ρ3 e3 v2 v3 :
                           (ρ, e1)                     -->* Clo ρ3 e3 ->
                           (ρ, e2)                     -->* v2 ->
                           (ρ3 ++ [Clo ρ3 e3; v2], e3) -->* v3 ->
                           (ρ, App e1 e2)              -->* v3
  (* | M_App_Code ρ e1 e2 s1 s2 :
                           (ρ, e1)                     -->* Code s1 ->
                           (ρ, e2)                     -->* Code s2 ->
                           (ρ, App e1 e2)              -->* reflectc (App s1 s2) *)
  (* ... *)

  where "s -->* v" := (evalms s v).
