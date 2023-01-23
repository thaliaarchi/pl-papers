Require Import String Arith List.
Import ListNotations.

(* λ⇅ multi-level core language *)

Inductive op1 :=
  | OCar
  | OCdr
  | OIsNat
  | OIsStr
  | OIsPair.

Inductive op2 :=
  | OAdd
  | OSub
  | OMul
  | OEq.

Inductive error :=
  | ErrUnboundVar.

Inductive exp :=
  | ENat (n : nat)
  | EStr (t : string)
  | ECons (e0 e1 : exp)
  | ELam (e0 : exp)
  | ELet (e0 e1 : exp)
  | EVar (x : nat)
  | EIf (e0 e1 e2 : exp)
  | EApp (e0 e1 : exp)
  | EOp1 (op : op1) (e0 : exp)
  | EOp2 (op : op2) (e0 e1 : exp)
  | ELift (e0 : exp)
  | ERun (e0 e1 : exp)
  | EErr (err : error).

Inductive val :=
  | VNat (n : nat)
  | VStr (t : string)
  | VPair (v0 v1 : val)
  | VClo (ρ : list val) (e0 : exp)
  | VCode (e0 : exp)
  | VErr (err : error).

Definition lookup_exp (ρ : list exp) (n : nat) : exp :=
  nth_default (EErr ErrUnboundVar) (rev ρ) n.

Definition lookup_val (ρ : list val) (n : nat) : val :=
  nth_default (VErr ErrUnboundVar) (rev ρ) n.

Definition state : Type := (nat * list exp). (* fresh, acc *)

Definition fresh (s : state) : state * exp :=
  let (n, acc) := s in ((1 + n, acc), EVar n).

Definition reflect (s : state) (e : exp) : state * exp :=
  let (n, acc) := s in fresh (n, e :: acc).

Definition reify (sρ : state * exp) : exp :=
  match sρ with
  | ((_, acc), ρ) => fold_right ELet ρ (rev acc)
  end.

Fixpoint anf (s : state) (ρ : list exp) (e : exp) : state * exp :=
  match e with
  | ENat n => (s, ENat n)
  | EStr t => (s, EStr t)
  | ECons e0 e1 =>
      let (s0, v0) := anf s ρ e0 in
      let (s1, v1) := anf s0 ρ e1 in
      reflect s1 (ECons v0 v1)
  | ELam e0 =>
      let (s0, v0) := fresh s in
      let (s1, v1) := fresh s0 in
      reflect (fst s, snd s1)
              (ELam (reify (anf (fst s1, []) (v1 :: v0 :: ρ) e0)))
  | ELet e0 e1 =>
      let (s0, v0) := anf s ρ e0 in
      anf s0 (v0 :: ρ) e1
  | EVar x => (s, lookup_exp ρ x)
  | EIf e0 e1 e2 =>
      let (s0, v0) := anf s ρ e0 in
      reflect s0 (EIf v0 (reify (anf (fst s0, []) ρ e1))
                         (reify (anf (fst s0, []) ρ e2)))
  | EApp e0 e1 =>
      let (s0, v0) := anf s ρ e0 in
      let (s1, v1) := anf s0 ρ e1 in
      reflect s1 (EApp v0 v1)
  | EOp1 op e0 =>
      let (s0, v0) := anf s ρ e0 in
      reflect s0 (EOp1 op v0)
  | EOp2 op e0 e1 =>
      let (s0, v0) := anf s ρ e0 in
      let (s1, v1) := anf s0 ρ e1 in
      reflect s1 (EOp2 op v0 v1)
  | ELift e0 =>
      let (s0, v0) := anf s ρ e0 in
      reflect s0 (ELift v0)
  | ERun e0 e1 =>
      let (s0, v0) := anf s ρ e0 in
      let (s1, v1) := anf s0 ρ e1 in
      reflect s1 (ERun v0 v1)
  | EErr err => (s, e)
  end.

Definition anf0 (e : exp) := reify (anf (0, []) [] e).

Example example_anf0 :
  anf0 (ELam (EVar 1)) = ELet (ELam (EVar 1)) (EVar 0).
Proof. reflexivity. Qed.
