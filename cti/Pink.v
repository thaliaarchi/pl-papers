Require Import String.
From CTI Require Import BaseFix.
Open Scope string_scope.

Definition ECadr e := ECar (ECdr e).
Definition ECaddr e := ECar (ECdr (ECdr e)).
Definition ECadddr e := ECar (ECdr (ECdr (ECdr e))).

Definition maybe_lift e := EApp (EVar 1) e.
Definition eval e := EApp (EVar 2) e.
Definition exp := EVar 3.
Definition env := EVar 5.
Definition local n := EVar (6 + n).

(* Meta-circular stage-parametric evaluator for Pink *)
Definition pink_eval :=
  ELam (*_ maybe_lift*) (ELam (*eval exp*) (ELam (*_ env*)
    (EIf (EIsNat exp) (maybe_lift exp)
    (EIf (EIsStr exp) (EApp env exp)
    (EIf (EEq "quote"  (ECar exp)) (maybe_lift (ECadr exp))
    (EIf (EEq "+"      (ECar exp)) (EAdd (EApp (eval (ECadr exp)) env) (EApp (eval (ECaddr exp)) env))
    (EIf (EEq "-"      (ECar exp)) (ESub (EApp (eval (ECadr exp)) env) (EApp (eval (ECaddr exp)) env))
    (EIf (EEq "*"      (ECar exp)) (EMul (EApp (eval (ECadr exp)) env) (EApp (eval (ECaddr exp)) env))
    (EIf (EEq "eq?"    (ECar exp)) (EEq  (EApp (eval (ECadr exp)) env) (EApp (eval (ECaddr exp)) env))
    (EIf (EEq "if"     (ECar exp)) (EIf  (EApp (eval (ECadr exp)) env) (EApp (eval (ECaddr exp)) env)
                                                                       (EApp (eval (ECadddr exp)) env))
    (EIf (EEq "lambda" (ECar exp)) (maybe_lift (ELam (*f x*) (EApp (eval (ECadddr exp))
                                                                   (ELam (*_ y*) (EIf (EEq (local 3 (*y*)) (ECadr exp)) (local 0 (*f*))
                                                                                 (EIf (EEq (local 3 (*y*)) (ECaddr exp)) (local 1 (*x*))
                                                                                 (EApp env (local 3 (*y*)))))))))
    (EIf (EEq "let"    (ECar exp)) (ELet (*x*) (EApp (eval (ECaddr exp)) env)
                                                     (EApp (eval (ECadddr exp))
                                                           (ELam (*_ y*) (EIf (EEq (local 2 (*y*)) (ECadr exp)) (local 0 (*x*)) (EApp env (local 2 (*y*)))))))
    (EIf (EEq "lift"   (ECar exp)) (ELift   (EApp (eval (ECadr exp)) env))
    (EIf (EEq "num?"   (ECar exp)) (EIsNat  (EApp (eval (ECadr exp)) env))
    (EIf (EEq "str?"   (ECar exp)) (EIsStr  (EApp (eval (ECadr exp)) env))
    (EIf (EEq "pair?"  (ECar exp)) (EIsPair (EApp (eval (ECadr exp)) env))
    (EIf (EEq "car"    (ECar exp)) (ECar    (EApp (eval (ECadr exp)) env))
    (EIf (EEq "cdr"    (ECar exp)) (ECdr    (EApp (eval (ECadr exp)) env))
    (EIf (EEq "cons"   (ECar exp)) (maybe_lift (ECons (EApp (eval (ECadr exp)) env) (EApp (eval (ECaddr exp)) env)))
    (EIf (EEq "app"    (ECar exp)) (EApp (EApp (eval (ECadr exp)) env) (EApp (eval (ECaddr exp)) env))
    (EErr ErrPinkEval))))))))))))))))))))).
