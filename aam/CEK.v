Require Import String. Open Scope string_scope.

Definition var : Type := string.

Inductive cexp :=
  | CVal (n : nat)
  | CVar (x : var)
  | CApp (e0 e1 : cexp)
  | CLam (x : var) (e : cexp).

Inductive env :=
  | ENil
  | ECons (x : var) (v : cexp) (ρ ρ' : env).

Fixpoint lookup (ρ : env) (x : var) : option (cexp * env) :=
  match ρ with
  | ENil => None
  | ECons y v ρ ρ' => if (x =? y)%string then Some (v, ρ)
                      else lookup ρ' x
  end.

Inductive cont :=
  | KMt
  | KAr (e : cexp) (ρ : env) (k : cont)
  | KFn (v : cexp) (ρ : env) (k : cont). (* v is CLam *)

Definition state : Type := cexp * env * cont.

Reserved Notation "s --> s'" (at level 40).

Inductive step : state -> state -> Prop :=
  (* Variable lookup *)
  | SVar x ρ v ρ' k :
      lookup ρ x = Some (v, ρ') ->
      (CVar x, ρ, k) --> (v, ρ', k)
  (* Function application *)
  | SApp e0 e1 ρ k :
      (CApp e0 e1, ρ, k) --> (e0, ρ, KAr e1 ρ k)
  (* Function value *)
  | SFun v ρ e ρ' k : (* v is CLam *)
      (v, ρ, KAr e ρ' k) --> (e, ρ', KFn v ρ k)
  (* Argument value *)
  | SArg v ρ x e ρ' k : (* v is CLam *)
      (v, ρ, KFn (CLam x e) ρ' k) --> (e, ECons x v ρ ρ', k)
  where "s '-->' s'" := (step s s').

Reserved Notation "s1 -->* s2" (at level 40).

Inductive multistep : state -> state -> Prop :=
  | multistep_refl x :
      x -->* x
  | multistep_step x y z :
      x --> y ->
      y -->* z ->
      x -->* z
  where "s1 -->* s2" := (multistep s1 s2).

Definition inj (e : cexp) : state := (e, ENil, KMt).

(* (((λx.x λy.y) 42), ⊥, mt) |->> (42, ⊥, mt) *)
Goal
  (inj (CApp (CApp (CLam "x" (CVar "x")) (CLam "y" (CVar "y"))) (CVal 42)))
  -->*
  (inj (CVal 42)).
Proof. repeat econstructor. Qed.
