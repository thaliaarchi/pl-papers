Require Import String Arith List.
Import ListNotations IfNotations.

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
  | ErrUnboundVar
  | ErrExpectedCode
  | ErrIfExpectedNat
  | ErrAppExpectedClo
  | ErrInvalidOp
  | ErrStage
  | ErrExceededDepth.

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

Notation ECar := (EOp1 OCar).
Notation ECdr := (EOp1 OCdr).
Notation EIsNat := (EOp1 OIsNat).
Notation EIsStr := (EOp1 OIsStr).
Notation EIsPair := (EOp1 OIsPair).
Notation EAdd := (EOp2 OAdd).
Notation ESub := (EOp2 OSub).
Notation EMul := (EOp2 OMul).
Notation EEq := (EOp2 OEq).

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
  let '((_, acc), ρ) := sρ in fold_right ELet ρ (rev acc).

Fixpoint anf (s : state) (ρ : list exp) (e : exp) : state * exp :=
  match e with
  | ENat n => (s, ENat n)
  | EStr t => (s, EStr t)
  | ECons e0 e1 =>
      let (s, v0) := anf s ρ e0 in
      let (s, v1) := anf s ρ e1 in
      reflect s (ECons v0 v1)
  | ELam e0 =>
      let (s0, v0) := fresh s in
      let (s1, v1) := fresh s0 in
      reflect (fst s, snd s1)
              (ELam (reify (anf (fst s1, []) (v1 :: v0 :: ρ) e0)))
  | ELet e0 e1 =>
      let (s, v0) := anf s ρ e0 in
      anf s (v0 :: ρ) e1
  | EVar x => (s, lookup_exp ρ x)
  | EIf e0 e1 e2 =>
      let (s, v0) := anf s ρ e0 in
      reflect s (EIf v0 (reify (anf (fst s, []) ρ e1))
                        (reify (anf (fst s, []) ρ e2)))
  | EApp e0 e1 =>
      let (s, v0) := anf s ρ e0 in
      let (s, v1) := anf s ρ e1 in
      reflect s (EApp v0 v1)
  | EOp1 op e0 =>
      let (s, v0) := anf s ρ e0 in
      reflect s (EOp1 op v0)
  | EOp2 op e0 e1 =>
      let (s, v0) := anf s ρ e0 in
      let (s, v1) := anf s ρ e1 in
      reflect s (EOp2 op v0 v1)
  | ELift e0 =>
      let (s, v0) := anf s ρ e0 in
      reflect s (ELift v0)
  | ERun e0 e1 =>
      let (s, v0) := anf s ρ e0 in
      let (s, v1) := anf s ρ e1 in
      reflect s (ERun v0 v1)
  | EErr err => (s, e)
  end.

Definition anf0 (e : exp) : exp :=
  reify (anf (0, []) [] e).

Definition reifyc (sv : state * val) : exp :=
  match sv with
  | (s, VCode e0) => reify (s, e0)
  | (_, VErr err) => EErr err
  | _ => EErr ErrExpectedCode
  end.

Definition reflectc (s : state) (e : exp) : state * val :=
  match reflect s e with
  | (s, EErr err) => (s, VErr err)
  | (s, v0) => (s, VCode v0)
  end.

Definition reifyv (sv : state * val) : val :=
  match sv with
  | ((_, []), v) => v
  | (s, VCode e0) => VCode (reify (s, e0))
  | (s, VErr err) => VErr err
  | _ => VErr ErrExpectedCode
  end.

Fixpoint eval (depth : nat) (s : state) (ρ : list val) (e : exp) : state * val :=
  match depth with
  | 0 => (s, VErr ErrExceededDepth)
  | S depth =>
      match e with
      | ENat n => (s, VNat n)
      | EStr t => (s, VStr t)
      | ECons e0 e1 =>
          let (s, v0) := eval depth s ρ e0 in
          if v0 is VErr err then (s, VErr err) else
          let (s, v1) := eval depth s ρ e1 in
          if v1 is VErr err then (s, VErr err) else
          (s, VPair v0 v1)
      | ELam e0 => (s, VClo ρ e0)
      | ELet e0 e1 =>
          let (s, v0) := eval depth s ρ e0 in
          if v0 is VErr err then (s, VErr err) else
          eval depth s (v0 :: ρ) e1
      | EVar n => (s, lookup_val ρ n)
      | EIf e0 e1 e2 =>
          let (s, v0) := eval depth s ρ e0 in
          match v0 with
          | VErr err => (s, VErr err)
          | VNat 0 => eval depth s ρ e2
          | VNat _ => eval depth s ρ e1
          | VCode v0 =>
              match eval depth (fst s, []) ρ e1,
                    eval depth (fst s, []) ρ e2 with
              | (_, VErr err), _ | _, (_, VErr err) => (s, VErr err)
              | r1, r2 => reflectc s (EIf v0 (reifyc r1) (reifyc r2))
              end
          | _ => (s, VErr ErrIfExpectedNat)
          end
      | EApp e0 e1 =>
          let (s, v0) := eval depth s ρ e0 in
          match v0 with
          | VErr err => (s, VErr err)
          | VClo ρ0 e0 =>
              let (s, v2) := eval depth s ρ e1 in
              if v2 is VErr err then (s, VErr err) else
              eval depth s (v2 :: VClo ρ0 e0 :: ρ0) e0
          | VCode e0 =>
              let (s, v2) := eval depth s ρ e1 in
              match v2 with
              | VErr err => (s, VErr err)
              | VCode e2 => reflectc s (EApp e0 e2)
              | _ => (s, VErr ErrExpectedCode)
              end
          | _ => (s, VErr ErrAppExpectedClo)
          end
      | EOp1 op e0 =>
          let (s, v0) := eval depth s ρ e0 in
          match op, v0 with
          | _, VErr err => (s, VErr err)
          | _, VCode v0 => reflectc s (EOp1 op v0)
          | OCar, VPair v0 v1 => (s, v0)
          | OCdr, VPair v0 v1 => (s, v1)
          | OIsNat, VNat _ => (s, VNat 1)
          | OIsNat, _ => (s, VNat 0)
          | OIsStr, VStr _ => (s, VNat 1)
          | OIsStr, _ => (s, VNat 0)
          | OIsPair, VPair _ _ => (s, VNat 1)
          | OIsPair, _ => (s, VNat 0)
          | _, _ => (s, VErr ErrInvalidOp)
          end
      | EOp2 op e0 e1 =>
          let (s, v0) := eval depth s ρ e0 in
          let (s, v1) := eval depth s ρ e1 in
          match op, v0, v1 with
          | _, VErr err, _ | _, _, VErr err => (s, VErr err)
          | _, VCode v0, VCode v1 => reflectc s (EOp2 op v0 v1)
          | _, VCode _, _ | _, _, VCode _ => (s, VErr ErrStage)
          | OAdd, VNat n0, VNat n1 => (s, VNat (n0 + n1))
          | OSub, VNat n0, VNat n1 => (s, VNat (n0 - n1))
          | OMul, VNat n0, VNat n1 => (s, VNat (n0 * n1))
          | OEq, VNat n0, VNat n1 => (s, VNat (if (n0 =? n1)%nat then 1 else 0))
          | OEq, VStr t0, VStr t1 => (s, VNat (if (t0 =? t1)%string then 1 else 0))
          | OEq, _, _ => (s, VNat 0)
          | _, _, _ => (s, VErr ErrInvalidOp)
          end
      | ELift e0 =>
          let (s, v0) := eval depth s ρ e0 in
          if v0 is VErr err then (s, VErr err) else
          let (s, v1) := lift depth s v0 in
          if v1 is EErr err then (s, VErr err) else
          (s, VCode v1)
      | ERun e0 e1 =>
          let (s0, v0) := eval depth s ρ e0 in
          match v0 with
          | VErr err => (s0, VErr err)
          | VCode v0 =>
              let (s1, v1) := eval depth (fst s0, []) ρ e1 in
              if v1 is VErr err then (s1, VErr err) else
              reflectc s0 (ERun v0 (reifyc (s1, v1)))
          | _ =>
              (s0, reifyv (eval depth (fst s0, []) ρ
                                (reifyc (eval depth (length ρ, snd s0) ρ e1))))
          end
      | EErr err => (s, VErr err)
      end
    end

with lift (depth : nat) (s : state) (v : val) : state * exp :=
  match depth with
  | 0 => (s, EErr ErrExceededDepth)
  | S depth =>
      match v with
      | VNat n => (s, ENat n)
      | VStr t => (s, EStr t)
      | VPair v0 v1 =>
          match v0, v1 with
          | VCode e0, VCode e1 => reflect s (ECons e0 e1)
          | VCode _, _ | _, VCode _ => (s, EErr ErrStage)
          | _, _ => (s, EErr ErrExpectedCode)
          end
      | VClo ρ e0 =>
          let (s0, v0) := fresh s in
          let (s1, v1) := fresh s0 in
          let (s2, v2) := eval depth (fst s1, []) (VCode v1 :: VCode v0 :: ρ) e0 in
          match v2 with
          | VErr err => (s0, EErr err)
          | VCode e2 => reflect (fst s, snd s1) (ELam (reify (s2, e2)))
          | _ => (s0, EErr ErrExpectedCode)
          end
      | VCode e0 => reflect s (ELift e0)
      | VErr err => (s, EErr err)
      end
  end.

Definition eval0 (e : exp) : state * val :=
  eval 100 (0, []) [] e.

Module Tests.
Example ex0 : eval0 (ELam (EVar 1))                                  = ((0, []), VClo [] (EVar 1)).                                   reflexivity. Qed.
Example ex1 : eval0 (anf0 (ELam (EVar 1)))                           = ((0, []), VClo [] (EVar 1)).                                   reflexivity. Qed.
Example ex2 : eval0 (ELam (ELam (EVar 1)))                           = ((0, []), VClo [] (ELam (EVar 1))).                            reflexivity. Qed.
Example ex3 : eval0 (anf0 (ELam (ELam (EVar 1))))                    = ((0, []), VClo [] (ELet (ELam (EVar 1)) (EVar 2))).            reflexivity. Qed.
Example ex4 : reifyc (eval0 (ELift (ELam (EVar 1))))                 = ELet (ELam (EVar 1)) (EVar 0).                                 reflexivity. Qed.
Example ex5 : anf0 (ELam (EVar 1))                                   = ELet (ELam (EVar 1)) (EVar 0).                                 reflexivity. Qed.
Example ex6 : reifyc (eval0 (ELift (ELam (ELift (ELam (EVar 1))))))  = ELet (ELam (ELet (ELam (EVar 1)) (EVar 2))) (EVar 0).          reflexivity. Qed.
Example ex7 : anf0 (ELam (ELam (EVar 1)))                            = ELet (ELam (ELet (ELam (EVar 1)) (EVar 2))) (EVar 0).          reflexivity. Qed.
Example ex8 : eval0 (ERun (ELam (EVar 1)) (ELift (ELam (EVar 1))))   = ((0, []), VClo [] (EVar 1)).                                   reflexivity. Qed.
Example ex9 : reifyc (eval0 (ELift (ELam (EApp (EVar 0) (EVar 1))))) = ELet (ELam (ELet (EApp (EVar 0) (EVar 1)) (EVar 2))) (EVar 0). reflexivity. Qed.

(* Test from POPL 2018 Scala artifact:
   https://github.com/TiarkRompf/collapsing-towers/blob/master/popl18/base.scala#L330-L364 *)
(*
  Pattern:
    def f = fun { n => if (n != 0) f(n-1) else 1 }
  Corresponds to:
    val f = { () => lift({ n => if (n != 0) f()(n-1) else 1 }) }
*)
Definition f_self := EApp (EVar 0) (ENat 99).
Definition n := EVar 3.
Definition fac_body := ELam (EIf n
                                 (EMul n (EApp f_self (ESub n (ELift (ENat 1)))))
                                 (ELift (ENat 1))).
Definition fac := EApp (ELam (ELift fac_body)) (ENat 99).

Definition fac_out :=
  ELet (ELam (ELet (EIf (EVar 1)
                        (ELet (ESub (EVar 1) (ENat 1))
                              (ELet (EApp (EVar 0) (EVar 2))
                                    (ELet (EMul (EVar 1) (EVar 3))
                                          (EVar 4))))
                        (ENat 1))
             (EVar 2)))
       (EVar 0).

Example factorial : reifyc (eval0 fac) = fac_out. Admitted.
End Tests.
