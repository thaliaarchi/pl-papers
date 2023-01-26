#lang plait
(require (typed-in racket/base [gensym : (Symbol -> Symbol)]))

(module s-exp-printer racket/base
  (require racket/pretty
           (only-in plait s-exp-content))
  (define (pretty-print-s-exp s-exp)
    (pretty-print (s-exp-content s-exp)))

  (provide pretty-print-s-exp))

(require (typed-in 's-exp-printer [pretty-print-s-exp : (S-Exp -> Void)]))

; s-expression extraction

(define (seref* pp ss fail)
  (type-case (Listof S-Exp) pp
    [empty
     (type-case (Listof S-Exp) ss
       [empty (none)]
       [(cons _₀ _₁) (fail)])]
    [(cons p pp)
     (type-case (Listof S-Exp) ss
       [empty (fail)]
       [(cons s ss)
        (type-case (Optionof S-Exp) (seref p s fail)
          [(some s) (some s)]
          [(none) (seref* pp ss fail)])])]))

(seref : (S-Exp S-Exp (-> 'a) -> (Optionof S-Exp)))
(define (seref p s fail)
  (cond
    [(s-exp-match? `• p)
     (some s)]
    [(s-exp-match? `_ p)
     (none)]
    [(equal? p s)
     (none)]
    [(s-exp-list? p)
     (if (s-exp-list? s)
       (let ([pp (s-exp->list p)]
             [ss (s-exp->list s)])
         (seref* pp ss fail))
       (fail))]
    [else
     (fail)]))

(define (s-exp-ref p s)
  (let ([fail (λ ()
                (error
                 's-exp-ref
                 (string-append
                  "bad reference "
                  (string-append
                   (to-string p)
                   (string-append
                    " in "
                    (to-string s))))))])
    (type-case (Optionof S-Exp) (seref p s fail)
    [(some s) s]
    [(none) (fail)])))



(define-type-alias Env (Hashof Symbol Val))

(define-type Exp
  (Lit [n : Number])
  (Ref [x : Symbol])
  (Con [e₀ : Exp]
       [e₁ : Exp])
  (Lam [f : Symbol]
       [x : Symbol]
       [e : Exp])
  (Let [x : Symbol]
       [e₀ : Exp]
       [e₁ : Exp])
  (App [e₀ : Exp]
       [e₁ : Exp])
  (If0 [e₀ : Exp]
       [e₁ : Exp]
       [e₂ : Exp])
  (IsN [e : Exp])
  (Plu [e₀ : Exp]
       [e₁ : Exp])
  (Min [e₀ : Exp]
       [e₁ : Exp])
  (Lif [e : Exp])
  (Run [e₀ : Exp]
       [e₁ : Exp]))

(define-type Val
  (Cst [n : Number])
  (Tup [v₀ : Val]
       [v₁ : Val])
  (Clo [f : Symbol]
       [x : Symbol]
       [e : Exp]
       [ρ : Env])
  (Cod [e : Exp]))

(define ρ-empty (hash empty))

(define (ρ-extend ρ x v)
  (hash-set ρ x v))

(define (ρ-lookup ρ x)
  (type-case (Optionof Val) (hash-ref ρ x)
    [(some v)
     v]
    [(none)
     (error 'ρ-lookup "unbound variable")]))


(define (parse s)
  (cond
    [(s-exp-match? `NUMBER s)
     (Lit (s-exp->number s))]
    [(s-exp-match? `SYMBOL s)
     (Ref (s-exp->symbol s))]
    [(s-exp-match? `(cons ANY ANY) s)
     (Con (parse (s-exp-ref `(cons • _) s))
          (parse (s-exp-ref `(cons _ •) s)))]
    [(s-exp-match? `(λ SYMBOL (SYMBOL) ANY) s)
     (Lam (s-exp->symbol (s-exp-ref `(λ • (_) _) s))
          (s-exp->symbol (s-exp-ref `(λ _ (•) _) s))
          (parse         (s-exp-ref `(λ _ (_) •) s)))]
    [(s-exp-match? `(let ([SYMBOL ANY]) ANY) s)
     (Let (s-exp->symbol (s-exp-ref `(let ([• _]) _) s))
          (parse         (s-exp-ref `(let ([_ •]) _) s))
          (parse         (s-exp-ref `(let ([_ _]) •) s)))]
    [(s-exp-match? `(@ ANY ANY) s)
     (App (parse (s-exp-ref `(@ • _) s))
          (parse (s-exp-ref `(@ _ •) s)))]
    [(s-exp-match? `(if0 ANY ANY ANY) s)
     (If0 (parse (s-exp-ref `(if0 • _ _) s))
          (parse (s-exp-ref `(if0 _ • _) s))
          (parse (s-exp-ref `(if0 _ _ •) s)))]
    [(s-exp-match? `(num? ANY) s)
     (IsN (parse (s-exp-ref `(num? •) s)))]
    [(s-exp-match? `(+ ANY ANY) s)
     (Plu (parse (s-exp-ref `(+ • _) s))
          (parse (s-exp-ref `(+ _ •) s)))]
    [(s-exp-match? `(- ANY ANY) s)
     (Min (parse (s-exp-ref `(- • _) s))
          (parse (s-exp-ref `(- _ •) s)))]
    [(s-exp-match? `(lift ANY) s)
     (Lif (parse (s-exp-ref `(lift •) s)))]
    [(s-exp-match? `(run ANY ANY) s)
     (Run (parse (s-exp-ref `(run • _) s))
          (parse (s-exp-ref `(run _ •) s)))]
    [else
     (error 'parse (string-append "unrecognized: " (to-string s)))]))

(define (unparse e)
  (type-case Exp e
    [(Lit n)
     (number->s-exp n)]
    [(Ref x)
     (symbol->s-exp x)]
    [(Con e₀ e₁)
     `(cons ,(unparse e₀)
            ,(unparse e₁))]
    [(Lam f x e)
     `(λ ,(symbol->s-exp f)
        ,(symbol->s-exp x)
        ,(unparse e))]
    [(Let x e₀ e₁)
     `(let ([,(symbol->s-exp x)
             ,(unparse e₀)])
        ,(unparse e₁))]
    [(App e₀ e₁)
     `(@ ,(unparse e₀)
         ,(unparse e₁))]
    [(If0 e₀ e₁ e₂)
     `(if0 ,(unparse e₀)
           ,(unparse e₁)
           ,(unparse e₂))]
    [(IsN e)
     `(num? ,(unparse e))]
    [(Plu e₀ e₁)
     `(+ ,(unparse e₀)
         ,(unparse e₁))]
    [(Min e₀ e₁)
     `(- ,(unparse e₀)
         ,(unparse e₁))]
    [(Lif e)
     `(lift ,(unparse e))]
    [(Run e₀ e₁)
     `(run ,(unparse e₀)
           ,(unparse e₁))]))

(define (lift v)
  (type-case Val v
    [(Cst n)
     (Lit n)]
    [(Tup v₀ v₁)
     (let ([x₀ (lift v₀)]
           [x₁ (lift v₁)])
       (reflect (Con x₀ x₁)))
     #;
     (type-case Val v₀
       [(Cod e₀)
        (type-case Val v₁
          [(Cod e₁)
           (reflect (Con e₀ e₁))]
          [else
           (error 'lift "1")])]
       [else
        (error 'lift "2")])]
    [(Clo f x e ρ)
     (let ([f-fresh (gensym f)]
           [x-fresh (gensym x)])
       (reflect (Lam f-fresh
                     x-fresh
                     (reifyc
                      (λ ()
                        (let* ([ρ (ρ-extend ρ f (Cod (Ref f-fresh)))]
                               [ρ (ρ-extend ρ x (Cod (Ref x-fresh)))])
                          (evalms ρ e)))))))]
    [(Cod e)
     (reflect (Lif e))]))

(define (liftc v)
  (Cod (lift v)))

(define (reflect e)
  (let ([x (gensym 'x)])
    (begin
      (set! stBlock (cons (pair x e) stBlock))
      (Ref x))))

(define (reflectc e)
  (Cod (reflect e)))

(define (evalms ρ e)
  (type-case Exp e
    [(Lit n)
     (Cst n)]
    [(Ref x)
     (ρ-lookup ρ x)]
    [(Con e₀ e₁)
     (Tup (evalms ρ e₀)
          (evalms ρ e₁))]
    [(Lam f x e)
     (Clo f x e ρ)]
    [(Let x e₀ e₁)
     (let ([v (evalms ρ e₀)])
       (evalms (ρ-extend ρ x v) e₁))]
    [(App e₀ e₁)
     (let ([v₀ (evalms ρ e₀)]
           [v₁ (evalms ρ e₁)])
       (type-case Val v₀
         [(Clo f x e ρ)
          (let* ([ρ (ρ-extend ρ f v₀)]
                 [ρ (ρ-extend ρ x v₁)])
            (evalms ρ e))]
         [(Cod f)
          (reflectc (App f (lift v₁)))]
         [else
          (error 'evalms "App 1")]))]
    [(If0 e₀ e₁ e₂)
     (type-case Val (evalms ρ e₀)
       [(Cst n)
        (evalms ρ (if (zero? n) e₁ e₂))]
       [(Cod e)
        (reflectc (If0 e
                       (reifyc (λ () (evalms ρ e₁)))
                       (reifyc (λ () (evalms ρ e₂)))))]
       [else
        (error 'evalms "If0 1")])]
    [(IsN e)
     (type-case Val (evalms ρ e)
       [(Cst n)
        (Cst 0)]
       [(Cod e)
        (reflectc (IsN e))]
       [else
        (error 'evalms "IsN 1")])]
    [(Plu e₀ e₁)
     (let ([v₀ (evalms ρ e₀)]
           [v₁ (evalms ρ e₁)])
       (type-case Val v₀
         [(Cst n₀)
          (type-case Val v₁
            [(Cst n₁)
             (Cst (+ n₀ n₁))]
            ; first is a constant but second is code
            [(Cod e₁)
             (reflectc (Plu (lift v₀) e₁))]
            [else
             (error 'evalms "Plu 2")])]
         [(Cod e₀)
          (type-case Val v₁
            [(Cod e₁)
             (reflectc (Plu e₀ e₁))]
            ; second is a constant but first is code
            [(Cst n₁)
             (reflectc (Plu e₀ (lift v₁)))]
            [else
             (error 'evalms "Plu 3")])]
         [else
          (error 'evalms "Plu 1")]))]
    [(Min e₀ e₁)
     (let ([v₀ (evalms ρ e₀)]
           [v₁ (evalms ρ e₁)])
       (type-case Val v₀
         [(Cst n₀)
          (type-case Val v₁
            [(Cst n₁)
             (Cst (- n₀ n₁))]
            [else
             (error 'evalms "Min 2")])]
         [(Cod e₀)
          (type-case Val v₁
            [(Cod e₁)
             (reflectc (Min e₀ e₁))]
            [else
             (error 'evalms "Min 3")])]
         [else
          (error 'evalms "Min 1")]))]
    [(Lif e)
     (liftc (evalms ρ e))]
    [(Run e₀ e₁)
     (type-case Val (evalms ρ e₀)
       [(Cod e₀)
        (reflectc (Run e₀ (reifyc (λ () (evalms ρ e₁)))))]
       [else
        (evalmsg ρ (reifyc (λ () (evalms ρ e₁))))])]))

(define stBlock empty)

(define (run f)
  (let ([sB stBlock])
    (let ([v (f)])
      (begin
        (set! stBlock sB)
        v))))

(define (let-combine x×e e)
  (Let (fst x×e) (snd x×e) e))

(define (reify f)
  (run (λ ()
         (begin
           (set! stBlock empty)
           (let ([e (f)])
             (foldr let-combine e (reverse stBlock)))))))

(define (reifyc f)
  (reify (λ ()
           (type-case Val (f)
             [(Cod e)
              e]
             [else
              (error 'reifyc "1")]))))

(define (reifyv f)
  (run (λ ()
         (begin
           (set! stBlock empty)
           (let ([v (f)])
             (if (empty? stBlock)
               v
               (type-case Val v
                 [(Cod e)
                  (Cod (foldr let-combine e (reverse stBlock)))]
                 [else
                  (error 'reifyv "1")])))))))

(define (evalmsg ρ e)
  (reifyv (λ () (evalms ρ e))))

(define (round-trip e)
  (begin
    (display "input s-expression\n")
    (pretty-print-s-exp e)
    (let ([e (parse e)])
      (begin
        (display "parsed representation\n")
        (display (to-string e))
        (display "\n")
        (let ([v (evalmsg ρ-empty e)])
          (begin
            (display "result value\n")
            (display (to-string v))
            (display "\n")
            (let ([e (reify (λ () (lift v)))])
              (begin
                (display "value lifted into syntax\n")
                (display (to-string e))
                (display "\n")
                (let ([e (unparse e)])
                  (begin
                    (display "unparsed representation\n")
                    (pretty-print-s-exp e)))))))))
    (display "\n")))

(round-trip `(let ([x (+ 5 6)])
               x))


(round-trip
 `(@ (λ tri (n)
        (if0 n
             0
             (+ n (@ tri (- n 1)))))
     5))

(round-trip
 `(@ (λ tri (n)
        (if0 n
             (lift 0)
             (+ (lift n) (@ tri (- n 1)))))
     5))

; loops forever
#;
(round-trip
 `(@ (λ tri (n)
        (if0 n
             (lift 0)
             (+ (lift n)
                (@ tri (- (lift n)
                          (lift 1))))))
     5))

; inconsistent lifting

(round-trip
 `(@ (λ tri (n)
        (if0 n
             (lift 0)
             (+ n
                (@ tri (- n 1)))))
     5))

(round-trip
 `(lift 42))

(round-trip
 `(run 0
       (lift 42)))

(round-trip
 `(run (lift 0)
       (lift 42)))

; exposes incorrect implementation of tuple lifting?

(round-trip
 `(lift (cons 1 2)))

(round-trip
 `(let ([f (λ g (x) (num? x))])
    (cons f f)))

#;
(round-trip
 `(@ (λ f (x)
       (if0 x
            x
            (@ (lift f) (- x 1))))
     4))
