;; ** The Brang interpreter, using environments

#lang pl 06

#|
The grammar:
  <BRANG> ::= <num>
            | { + <BRANG> <BRANG> }
            | { - <BRANG> <BRANG> }
            | { * <BRANG> <BRANG> }
            | { / <BRANG> <BRANG> }
            | { with { <id> <BRANG> } <BRANG> }
            | <id>
            | { fun { <id> <id> ... } <BRANG> }
            | { call <BRANG> <BRANG> <BRANG> ... }

Evaluation rules:
  eval(N,env)                = N
  eval({+ E1 E2},env)        = eval(E1,env) + eval(E2,env)
  eval({- E1 E2},env)        = eval(E1,env) - eval(E2,env)
  eval({* E1 E2},env)        = eval(E1,env) * eval(E2,env)
  eval({/ E1 E2},env)        = eval(E1,env) / eval(E2,env)
  eval(CRef(N),env)          = list-ref(env,N)
  eval({with {x E1} E2},env) = eval(E2,cons(eval(E1,env),env))
  eval({fun {x} E},env)      = <{fun {x} E}, env>
  eval({call E1 E2},env1)    = eval(Ef,cons(eval(E2,env1),env2))
                                   if eval(E1,env1) = <{fun {x} Ef}, env2>
                             = error!          otherwise
|#

(define-type BRANG
  [Num  Number]
  [Add  BRANG BRANG]
  [Sub  BRANG BRANG]
  [Mul  BRANG BRANG]
  [Div  BRANG BRANG]
  [Id   Symbol]
  [With Symbol BRANG BRANG]
  [Fun  (Listof Symbol) BRANG]
  [Call BRANG (Listof BRANG)])

(define-type CORE
  [CNum  Number]
  [CAdd  CORE CORE]
  [CSub  CORE CORE]
  [CMul  CORE CORE]
  [CDiv  CORE CORE]
  [CRef  Natural]
  [CFun  CORE]
  [CCall CORE CORE])

(: parse-sexpr : Sexpr -> BRANG)
;; parses s-expressions into BRANGs
(define (parse-sexpr sexpr)
  (match sexpr
    [(number: n)    (Num n)]
    [(symbol: name) (Id name)]
    [(cons 'with more)
     (match sexpr
       [(list 'with (list (symbol: name) named) body)
        (With name (parse-sexpr named) (parse-sexpr body))]
       [else (error 'parse-sexpr "bad `with' syntax in ~s" sexpr)])]
    [(cons 'fun more)
     (match sexpr
       [(list 'fun (list (symbol: name) (symbol: names)...) body)
        (Fun (cons name names) (parse-sexpr body))]
       [else (error 'parse-sexpr "bad `fun' syntax in ~s" sexpr)])]
    [(list '+ lhs rhs) (Add (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '- lhs rhs) (Sub (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '* lhs rhs) (Mul (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '/ lhs rhs) (Div (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list 'call fun arg1 args ...)
     (Call (parse-sexpr fun) (map parse-sexpr (cons arg1 args)))]
    [else (error 'parse-sexpr "bad syntax in ~s" sexpr)]))

(: parse : String -> BRANG)
;; parses a string containing a BRANG expression to a BRANG AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

;; Types for environments, values, and a lookup function

(define-type ENV = (Listof VAL))
(define-type DE-ENV = Symbol -> Natural)

(define-type VAL
  [NumV Number]
  [FunV CORE ENV])

(: de-empty-env : DE-ENV)
(define (de-empty-env sym)
  (error 'empty-env "there is no mapping for ~s" sym))

(: de-extend : DE-ENV Symbol -> DE-ENV)
;; take a DE-ENV and a symbol, and returns the extended environment
(define (de-extend env id)
  (lambda ([sym : Symbol])
    (if (eq? id sym) 0 (+ 1 (env sym)))))

(: preprocess : BRANG DE-ENV -> CORE)
;; translates parsed BRANG input into CORE
(define (preprocess expr de-env)
  (cases expr
    [(Num n) (CNum n)]
    [(Add l r) (CAdd (preprocess l de-env) (preprocess r de-env))]
    [(Sub l r) (CSub (preprocess l de-env) (preprocess r de-env))]
    [(Mul l r) (CMul (preprocess l de-env) (preprocess r de-env))]
    [(Div l r) (CDiv (preprocess l de-env) (preprocess r de-env))]
    [(With name named-expr bound-body)
     (CCall (CFun (preprocess bound-body (de-extend de-env name)))
            (preprocess named-expr de-env))]
    [(Id name) (CRef (de-env name))]
    [(Fun bound-id bound-body)
     ;; (CFun (preprocess bound-body (de-extend de-env bound-id)))
     (if (null? (cdr bound-id))
         (CFun (preprocess bound-body (de-extend de-env (first bound-id))))
         (preprocess (Fun (list (first bound-id))
                          (Fun (rest bound-id) bound-body)) de-env))]
    [(Call fun-expr args-expr)
     (if (null? (cdr args-expr))
         (CCall (preprocess fun-expr de-env)
                (preprocess (first args-expr) de-env))
         (preprocess (Call (Call fun-expr (list (first args-expr)))
                           (rest args-expr)) de-env))]))

(: NumV->number : VAL -> Number)
;; convert a BRANG runtime numeric value to a Racket one
(define (NumV->number val)
  (cases val
    [(NumV n) n]
    [else (error 'arith-op "expected a number, got: ~s" val)]))

(: arith-op : (Number Number -> Number) VAL VAL -> VAL)
;; gets a Racket numeric binary operator, and uses it within a NumV
;; wrapper
(define (arith-op op val1 val2)
  (NumV (op (NumV->number val1) (NumV->number val2))))

(: eval : CORE ENV -> VAL)
;; evaluates CORE expressions by reducing them to values
(define (eval expr env)
  (cases expr
    [(CNum n) (NumV n)]
    [(CAdd l r) (arith-op + (eval l env) (eval r env))]
    [(CSub l r) (arith-op - (eval l env) (eval r env))]
    [(CMul l r) (arith-op * (eval l env) (eval r env))]
    [(CDiv l r) (arith-op / (eval l env) (eval r env))]
    [(CRef pos) (list-ref env pos)]
    [(CFun bound-body) (FunV bound-body env)]
    [(CCall fun-expr arg-expr)
     (let ([fval (eval fun-expr env)])
       (cases fval
         [(FunV bound-body f-env)
          (eval bound-body
                (cons (eval arg-expr env) f-env))]
         [else (error 'eval "`call' expects a function, got: ~s"
                      fval)]))]))

(: run : String -> Number)
;; evaluate a FLANG program contained in a string
(define (run str)
  (let ([result (eval (preprocess (parse str) de-empty-env) (list))])
    (cases result
      [(NumV n) n]
      [else (error 'run "evaluation returned a non-number: ~s"
                   result)])))

;; tests
(test (run "{call {fun {x} {+ x 1}} 4}")
      => 5)
(test (run "{with {add3 {fun {x} {+ x 3}}}
              {call add3 1}}")
      => 4)
(test (run "{with {add3 {fun {x} {+ x 3}}}
              {with {add1 {fun {x} {+ x 1}}}
                {with {x 3}
                  {call add1 {call add3 x}}}}}")
      => 7)
(test (run "{with {identity {fun {x} x}}
              {with {foo {fun {x} {+ x 1}}}
                {call {call identity foo} 123}}}")
      => 124)
(test (run "{with {x 3}
              {with {f {fun {y} {+ x y}}}
                {with {x 5}
                  {call f 4}}}}")
      => 7)
(test (run "{call {with {x 3}
                    {fun {y} {+ x y}}}
                  4}")
      => 7)
(test (run "{with {f {with {x 3} {fun {y} {+ x y}}}}
              {with {x 100}
                {call f 4}}}")
      => 7)
(test (run "{call {call {fun {x} {call x 1}}
                        {fun {x} {fun {y} {+ x y}}}}
                  123}")
      => 124)

;; tests for run-time and static environments

(test (run "{call {fun {x} {+ x 1}} 4}")
      => 5)
(test (run "{with {add3 {fun {x} {+ x 3}}}
              {call add3 1}}")
      => 4)
(test (run "{with {add3 {fun {x} {+ x 3}}}
              {with {add1 {fun {x} {+ x 1}}}
                {with {x 3}
                  {call add1 {call add3 x}}}}}")
      => 7)
(test (run "{with {identity {fun {x} x}}
              {with {foo {fun {x} {+ x 1}}}
                {call {call identity foo} 123}}}")
      => 124)
(test (run "{with {x 3}
              {with {f {fun {y} {+ x y}}}
                {with {x 5}
                  {call f 4}}}}")
      => 7)
(test (run "{call {with {x 3}
                    {fun {y} {+ x y}}}
                  4}")
      => 7)
(test (run "{with {f {with {x 3} {fun {y} {+ x y}}}}
              {with {x 100}
                {call f 4}}}")
      => 7)
(test (run "{call {call {fun {x} {call x 1}}
                        {fun {x} {fun {y} {+ x y}}}}
                  123}")
      => 124)

(test (run "{with {min2 {fun {x} {- x 2}}}
              {with {mul6 {fun {x} {* x 6}}}
                {with {div2 {fun {x} {/ x 2}}}
                  {call div2 {call mul6 {call min2 8}}}}}}") => 18)
(test (run "{with x 5}") =error>
      "parse-sexpr: bad `with' syntax in (with x 5)")
(test (run "{fun x {+ x 2}}") =error>
      "parse-sexpr: bad `fun' syntax in (fun x (+ x 2))")
(test (run "{+ 2}") =error> "parse-sexpr: bad syntax in (+ 2)")
(test (run "{+ 5 n}") =error> "empty-env: there is no mapping for n")
(test (run "{+ 5 {fun {x} {+ x 3}}}") =error>
      "arith-op: expected a number, got: (FunV (CAdd (CRef 0) (CNum 3)) ())")
(test (run "{call {+ 1 2} 6}") =error>
      "eval: `call' expects a function, got: (NumV 3)")
(test (run "{fun {x} {+ x 1}}") =error>
      (string-append "run: evaluation returned a non-number: "
                     "(FunV (CAdd (CRef 0) (CNum 1)) ())" ))

;; tests for language extension
(test (run "{call {fun {x y z} {+ x {+ y  z}}} 4 5 6}") => 15)
(test (run "{with {add {fun {x y} {+ x y}}} {call add 1 2}}")
      => 3)
(test (run "{with {mul {fun {x y} {* x y}}} {call mul 3 4}}")
      => 12)
#|(test (run "{fun {} 0}")
      =error> "parse-sexpr: no arguments provided in (fun () 0)")
(test (run "{call {fun {x} {+ x 1}}}")
      =error> "parse-sexpr: no arguments provided in (call (fun (x) (+ x 1)))")
|#
(define minutes-spent 840)