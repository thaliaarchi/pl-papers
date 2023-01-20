Require Import String Arith.

(* λ⇅ small-step semantics *)

(* Syntax *)

Inductive UNKNOWN : Type.

Inductive exp : Type :=
  | X (x : UNKNOWN)
  | Lit (n : nat)
  | Str (s : string)
  | Lam (f : UNKNOWN) (x : UNKNOWN) (e : exp)
  | App (e1 e2 : exp)
  | Cons (e1 e2 : exp)
  | Let (x : UNKNOWN) (e1 e2 : exp)
  | If (e1 e2 e3 : exp)

  (* ⊕¹ - Unary operators *)
  | IsNum (e : exp)
  | IsStr (e : exp)
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
  | LamC (f : UNKNOWN) (x : UNKNOWN) (e : exp)
  | LetC (x : UNKNOWN) (e1 e2 : exp).

Definition is_g (e : exp) : bool :=
  match e with
  | Code _ | Reflect _ | LamC _ _ _ | LetC _ _ _ => true
  | _ => false
  end.

Definition is_v (e : exp) : bool :=
  match e with
  | Lit _ | Str _ | Lam _ _ _ | Cons _ _ | Code _ => true
  | _ => false
  end.

Definition lit_of_bool (b : bool) : exp :=
  Lit (if b then 1 else 0).

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

(* Reduction rules *)

Notation "'?'" := (Str "unknown").

Reserved Notation "e '-->' e'" (at level 40).

Inductive step : exp -> exp -> Prop :=
  | M_Let : forall x v e,               Let x v e                        --> ?
  | M_App : forall f x e v,             App (Lam f x e) v                --> ?
  | M_App_Code : forall e1 e2,          App (Code e1) (Code e2)          --> Reflect (App e1 e2)
  | M_If_false : forall e1 e2,          If (Lit 0) e1 e2                 --> e2
  | M_If_true : forall n e1 e2,         n <> 0 ->
                                        If (Lit n) e1 e2                 --> e1
  | M_If_Code : forall e0 e1 e2,        If (Code e0) (Code e1) (Code e2) --> Reflect (If e0 e1 e2)
  | M_IsNum_true : forall n,            IsNum (Lit n)                    --> Lit 1
  | M_IsNum_Code : forall e,            IsNum (Code e)                   --> Reflect (IsNum e)
  | M_IsNum_false : forall v n e,       v <> Lit n -> v <> Code e ->
                                        IsNum v                          --> Lit 0
  | M_IsCons_true : forall e1 e2,       IsCons (Cons e1 e2)              --> Lit 1
  | M_IsCons_Code : forall e,           IsCons (Code e)                  --> Reflect (IsCons e)
  | M_IsCons_false : forall v e1 e2 e,  v <> Cons e1 e2 -> v <> Code e ->
                                        IsCons v                         --> Lit 0
  | M_Car_Cons : forall e1 e2,          Car (Cons e1 e2)                 --> e1
  | M_Car_Code : forall e,              Car (Code e)                     --> Reflect (Car e)
  | M_Cdr_Cons : forall e1 e2,          Cdr (Cons e1 e2)                 --> e2
  | M_Cdr_Code : forall e,              Cdr (Code e)                     --> Reflect (Cdr e)
  | M_Plus_Lit : forall n1 n2,          Plus (Lit n1) (Lit n2)           --> Lit (n1 + n2)
  | M_Plus_Code : forall e1 e2,         Plus (Code e1) (Code e2)         --> Reflect (Plus e1 e2)
  | M_Minus_Lit : forall n1 n2,         Minus (Lit n1) (Lit n2)          --> Lit (n1 - n2)
  | M_Minus_Code : forall e1 e2,        Minus (Code e1) (Code e2)        --> Reflect (Minus e1 e2)
  | M_Times_Lit : forall n1 n2,         Times (Lit n1) (Lit n2)          --> Lit (n1 * n2)
  | M_Times_Code : forall e1 e2,        Times (Code e1) (Code e2)        --> Reflect (Times e1 e2)
  | M_Eq_Lit : forall n1 n2,            Eq (Lit n1) (Lit n2)             --> lit_of_bool (n1 =? n2)
  | M_Eq_Code : forall e1 e2,           Eq (Code e1) (Code e2)           --> Reflect (Eq e1 e2)
  | M_Lift_Lit : forall n,              Lift (Lit n)                     --> Code (Lit n)
  | M_Lift_Cons : forall e1 e2,         Lift (Cons (Code e1) (Code e2))  --> Reflect (Code (Cons e1 e2))
  | M_Lift_Lam : forall f x e,          Lift (Lam f x e)                 --> Lift ?
  | M_Lift_LamC : forall f x e,         Lift (LamC f x (Code e))         --> Reflect (Code (Lam f x e))
  | M_Lift_Code : forall e,             Lift (Code e)                    --> Reflect (Code (Lift e))
  | M_Run_Code : forall e1 e2,          Run (Code e1) (Code e2)          --> Reflect (Code (Run e1 e2))
  | M_Run_else : forall v1 e1 e2,       v1 <> Code e1 ->
                                        Run v1 (Code e1)                 --> e2
  | (* ? *) PE_Reflect_Code : forall e, Reflect (Code e)                 --> ?
  | M_LetC : forall x1 e1 e2,           LetC x1 e1 (Code e2)             --> Code (Let x1 e1 e2)
  where "e '-->' e'" := (step e e').
