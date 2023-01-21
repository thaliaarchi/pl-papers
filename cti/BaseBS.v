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
  | Clo (env : list val) (e : exp)
  | Code (e : exp).

Definition env : Type := list val.

(* Definition reflect (s : exp) := *)

Reserved Notation "env '/' e '-->*' v" (at level 40).

Inductive evalms : env * exp -> val -> Prop :=
  | M_Lit : forall env n,               env / Lit n        -->* Cst n
  | M_Var : forall env n v,             nth_error env n = Some v ->
                                        env / Var n        -->* v
  | M_Cons : forall env e1 e2 v1 v2,    env / e1           -->* v1 ->
                                        env / e2           -->* v2 ->
                                        env / Cons e1 e2   -->* Tup v1 v2
  | M_Lam : forall env e,               env / Lam e        -->* Clo env e
  | M_Let : forall env e1 e2 v1 v2,     env / e1           -->* v1 ->
                                        (env ++ [v1]) / e2 -->* v2 ->
                                        env / Let e1 e2    -->* v2
  | M_App_Clo : forall env e1 e2 env3 e3 v2 v3,
                                        env / e1           -->* Clo env3 e3 ->
                                        env / e2           -->* v2 ->
                                        (env3 ++ [Clo env3 e3; v2]) / e3 -->* v3 ->
                                        env / App e1 e2    -->* v3
  (* | M_App_Code : forall env e1 e2 s1 s2,
                                        env / e1           -->* Code s1 ->
                                        env / e2           -->* Code s2 ->
                                        env / App e1 e2    -->* reflectc (App s1 s2) *)
  (* ... *)
  where "env '/' e '-->*' v" := (evalms (env, e) v).
