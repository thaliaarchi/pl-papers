Require Import Arith List.
Import ListNotations.

(* λ⇅ small-step semantics *)

(* Syntax *)
Inductive exp : Type :=
  | Lit (n : nat)
  | Var (x : nat)
  | Lam (e : exp) (* Implicit f (self) and x (param ident) *)
  | App (e1 e2 : exp)
  | Cons (e1 e2 : exp)
  | Let (e1 e2 : exp) (* Implicit x (ident) *)
  | If (e1 e2 e3 : exp)

  (* ⊕¹ - Unary operators *)
  | IsNum (e : exp)
  | IsCons (e : exp)
  | Car (e : exp)
  | Cdr (e : exp)

  (* ⊕² - Binary operators *)
  | Plus (e1 e2 : exp)
  | Minus (e1 e2 : exp)
  | Times (e1 e2 : exp)
  | Eq (e1 e2 : exp)

  | Lift (e : exp)
  | Run (e1 e2 : exp)

  (* g - Internal small-step forms *)
  | Code (e : exp)
  | Reflect (e : exp)
  | LamC (e : exp) (* Implicit f (self) and x (param ident) *)
  | LetC (e1 e2 : exp). (* Implicit x (ident) *)

Definition is_v (e : exp) : bool :=
  match e with
  | Lit _ | Lam _ | Cons _ _ | Code _ => true
  | _ => false
  end.

(* Environment *)
Definition env : Type := list exp.

Definition lookup (ρ : env) (n : nat) : option exp :=
  nth_error (rev ρ) n.

Definition lit_of_bool (b : bool) : exp :=
  Lit (if b then 1 else 0).

Notation "'?'" := (Lit 42).

Reserved Notation "s --> s'" (at level 40).

(* Reduction rules *)
Inductive step : env * exp -> env * exp -> Prop :=
  | S_Var          ρ x v :       lookup ρ x = Some v ->
                                 (ρ, Var x)                            --> (ρ, v)
  | S_Let          ρ v e :       is_v v = true ->
                                 (ρ, Let v e)                          --> (v :: ρ, e)
  | S_App          ρ e v :       is_v v = true ->
                                 (ρ, App (Lam e) v)                    --> (v :: Lam e :: ρ, e)
  | S_App_Code     ρ e1 e2 :     (ρ, App (Code e1) (Code e2))          --> (ρ, Reflect (App e1 e2))
  | S_If_false     ρ e1 e2 :     (ρ, If (Lit 0) e1 e2)                 --> (ρ, e2)
  | S_If_true      ρ n e1 e2 :   n <> 0 ->
                                 (ρ, If (Lit n) e1 e2)                 --> (ρ, e1)
  | S_If_Code      ρ e0 e1 e2 :  (ρ, If (Code e0) (Code e1) (Code e2)) --> (ρ, Reflect (If e0 e1 e2))
  | S_IsNum_true   ρ n :         (ρ, IsNum (Lit n))                    --> (ρ, Lit 1)
  | S_IsNum_Code   ρ e :         (ρ, IsNum (Code e))                   --> (ρ, Reflect (IsNum e))
  | S_IsNum_false  ρ v n e :     v <> Lit n -> v <> Code e ->
                                 (ρ, IsNum v)                          --> (ρ, Lit 0)
  | S_IsCons_true  ρ e1 e2 :     (ρ, IsCons (Cons e1 e2))              --> (ρ, Lit 1)
  | S_IsCons_Code  ρ e :         (ρ, IsCons (Code e))                  --> (ρ, Reflect (IsCons e))
  | S_IsCons_false ρ v e1 e2 e : v <> Cons e1 e2 -> v <> Code e ->
                                 (ρ, IsCons v)                         --> (ρ, Lit 0)
  | S_Car_Cons     ρ e1 e2 :     (ρ, Car (Cons e1 e2))                 --> (ρ, e1)
  | S_Car_Code     ρ e :         (ρ, Car (Code e))                     --> (ρ, Reflect (Car e))
  | S_Cdr_Cons     ρ e1 e2 :     (ρ, Cdr (Cons e1 e2))                 --> (ρ, e2)
  | S_Cdr_Code     ρ e :         (ρ, Cdr (Code e))                     --> (ρ, Reflect (Cdr e))
  | S_Plus_Lit     ρ n1 n2 :     (ρ, Plus (Lit n1) (Lit n2))           --> (ρ, Lit (n1 + n2))
  | S_Plus_Code    ρ e1 e2 :     (ρ, Plus (Code e1) (Code e2))         --> (ρ, Reflect (Plus e1 e2))
  | S_Minus_Lit    ρ n1 n2 :     (ρ, Minus (Lit n1) (Lit n2))          --> (ρ, Lit (n1 - n2))
  | S_Minus_Code   ρ e1 e2 :     (ρ, Minus (Code e1) (Code e2))        --> (ρ, Reflect (Minus e1 e2))
  | S_Times_Lit    ρ n1 n2 :     (ρ, Times (Lit n1) (Lit n2))          --> (ρ, Lit (n1 * n2))
  | S_Times_Code   ρ e1 e2 :     (ρ, Times (Code e1) (Code e2))        --> (ρ, Reflect (Times e1 e2))
  | S_Eq_Lit       ρ n1 n2 :     (ρ, Eq (Lit n1) (Lit n2))             --> (ρ, lit_of_bool (n1 =? n2))
  | S_Eq_Code      ρ e1 e2 :     (ρ, Eq (Code e1) (Code e2))           --> (ρ, Reflect (Eq e1 e2))
  | S_Lift_Lit     ρ n :         (ρ, Lift (Lit n))                     --> (ρ, Code (Lit n))
  | S_Lift_Cons    ρ e1 e2 :     (ρ, Lift (Cons (Code e1) (Code e2)))  --> (ρ, Reflect (Code (Cons e1 e2)))
  | S_Lift_Lam     ρ e :         (ρ, Lift (Lam e))                     --> (ρ, Lift (LamC ?))
  | S_Lift_LamC    ρ e :         (ρ, Lift (LamC (Code e)))             --> (ρ, Reflect (Code (Lam e)))
  | S_Lift_Code    ρ e :         (ρ, Lift (Code e))                    --> (ρ, Reflect (Code (Lift e)))
  | S_Run_Code     ρ e1 e2 :     (ρ, Run (Code e1) (Code e2))          --> (ρ, Reflect (Code (Run e1 e2)))
  | S_Run_else     ρ v1 e1 e2 :  v1 <> Code e1 ->
                                 (ρ, Run v1 (Code e1))                 --> (ρ, e2)
  | S_Reflect_Code ρ e :         (ρ, Reflect (Code e))                 --> (ρ, ?)
  | S_LetC         ρ e1 e2 :     (ρ, LetC e1 (Code e2))                --> (ρ, Code (Let e1 e2))

  where "s --> s'" := (step s s').
