Require Import String.
From CTI Require Import BaseFix.

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
    (EIf (EEq (EStr "quote")  (ECar exp)) (maybe_lift (ECadr exp))
    (EIf (EEq (EStr "+")      (ECar exp)) (EAdd (EApp (eval (ECadr exp)) env) (EApp (eval (ECaddr exp)) env))
    (EIf (EEq (EStr "-")      (ECar exp)) (ESub (EApp (eval (ECadr exp)) env) (EApp (eval (ECaddr exp)) env))
    (EIf (EEq (EStr "*")      (ECar exp)) (EMul (EApp (eval (ECadr exp)) env) (EApp (eval (ECaddr exp)) env))
    (EIf (EEq (EStr "eq?")    (ECar exp)) (EEq  (EApp (eval (ECadr exp)) env) (EApp (eval (ECaddr exp)) env))
    (EIf (EEq (EStr "if")     (ECar exp)) (EIf  (EApp (eval (ECadr exp)) env) (EApp (eval (ECaddr exp)) env)
                                                                              (EApp (eval (ECadddr exp)) env))
    (EIf (EEq (EStr "lambda") (ECar exp)) (maybe_lift (ELam (*f x*) (EApp (eval (ECadddr exp))
                                                                          (ELam (*_ y*) (EIf (EEq (local 3 (*y*)) (ECadr exp)) (local 0 (*f*))
                                                                                        (EIf (EEq (local 3 (*y*)) (ECaddr exp)) (local 1 (*x*))
                                                                                        (EApp env (local 3 (*y*)))))))))
    (EIf (EEq (EStr "let")    (ECar exp)) (ELet (*x*) (EApp (eval (ECaddr exp)) env)
                                                            (EApp (eval (ECadddr exp))
                                                                  (ELam (*_ y*) (EIf (EEq (local 2 (*y*)) (ECadr exp)) (local 0 (*x*)) (EApp env (local 2 (*y*)))))))
    (EIf (EEq (EStr "lift")   (ECar exp)) (ELift   (EApp (eval (ECadr exp)) env))
    (EIf (EEq (EStr "num?")   (ECar exp)) (EIsNat  (EApp (eval (ECadr exp)) env))
    (EIf (EEq (EStr "str?")   (ECar exp)) (EIsStr  (EApp (eval (ECadr exp)) env))
    (EIf (EEq (EStr "pair?")  (ECar exp)) (EIsPair (EApp (eval (ECadr exp)) env))
    (EIf (EEq (EStr "car")    (ECar exp)) (ECar    (EApp (eval (ECadr exp)) env))
    (EIf (EEq (EStr "cdr")    (ECar exp)) (ECdr    (EApp (eval (ECadr exp)) env))
    (EIf (EEq (EStr "cons")   (ECar exp)) (maybe_lift (ECons (EApp (eval (ECadr exp)) env) (EApp (eval (ECaddr exp)) env)))
    (EIf (EEq (EStr "app")    (ECar exp)) (EApp (EApp (eval (ECadr exp)) env) (EApp (eval (ECaddr exp)) env))
    (EErr ErrPinkEval))))))))))))))))))))).
