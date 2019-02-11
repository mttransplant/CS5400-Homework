#lang pl 06
;; ** The Brang interpreter, using environments

#|
The grammar:
  <BRANG> ::= <num>
            | { + <BRANG> <BRANG> }
            | { - <BRANG> <BRANG> }
            | { * <BRANG> <BRANG> }
            | { / <BRANG> <BRANG> }
            | { with { <id> <BRANG> } <BRANG> }
            | <id>
            | { fun { <id> } <BRANG> }
            | { call <BRANG> <BRANG> }

Core Evaluation rules:
  eval(N,env)                = N
  eval({+ E1 E2},env)        = eval(E1,env) + eval(E2,env)
  eval({- E1 E2},env)        = eval(E1,env) - eval(E2,env)
  eval({* E1 E2},env)        = eval(E1,env) * eval(E2,env)
  eval({/ E1 E2},env)        = eval(E1,env) / eval(E2,env)
  eval(CRef,env)             = list-ref(env,N)
  eval({with {x E1} E2},env) = eval(E2,extend(x,eval(E1,env),env))
  eval({fun {x} E},env)      = <{fun {x} E}, env>
  eval({call E1 E2},env1)
           = eval(Ef,extend(x,eval(E2,env1),env2))
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
  [Fun  Symbol BRANG]
  [Call BRANG BRANG])

(define-type CORE
  [CNum  Number]
  [CAdd  CORE CORE]
  [CSub  CORE CORE]
  [CMul  CORE CORE]
  [CDiv  CORE CORE]
  [CRef   Natural]
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
       [(list 'fun (list (symbol: name)) body)
        (Fun name (parse-sexpr body))]
       [else (error 'parse-sexpr "bad `fun' syntax in ~s" sexpr)])]
    [(list '+ lhs rhs) (Add (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '- lhs rhs) (Sub (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '* lhs rhs) (Mul (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '/ lhs rhs) (Div (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list 'call fun arg)
     (Call (parse-sexpr fun) (parse-sexpr arg))]
    [else (error 'parse-sexpr "bad syntax in ~s" sexpr)]))

(: parse : String -> BRANG)
;; parses a string containing a BRANG expression to a BRANG AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))


;; Type for environments is now a list of values
(define-type ENV = (Listof VAL))

;; Type for values
(define-type VAL
  [NumV Number]
  [FunV CORE ENV])

;; new environment type
(define-type DE-ENV = Symbol -> Natural)

(: de-empty-env : DE-ENV)
;; as the empty environment, a vacuous mapping — it always throws an error.
(define (de-empty-env id)
  (error 'empty-env "no mapping for ~s" id))

(: de-extend : DE-ENV Symbol -> DE-ENV)
;; de-extend consumes a DE-ENV and a symbol, and returns the extended environment.
(define (de-extend env id)
  (lambda([sym : Symbol])
    (if (eq? sym id)
        0
        (+ 1 (env sym)))))

(: preprocess : BRANG DE-ENV -> CORE)
;; a simple recursive scan of its input that translates a given BRANG value
;; (and a DE-ENV mapping) to the corresponding CORE value
(define (preprocess expr env)
  (: helper : BRANG -> CORE)
  ;; simply recursive call by saving enviroment variable
  (define (helper expr) (preprocess expr env))
  (cases expr
    [(Num n) (CNum n)]
    [(Add l r) (CAdd (helper l) (helper r))]
    [(Sub l r) (CSub (helper l) (helper r))]
    [(Mul l r) (CMul (helper l) (helper r))]
    [(Div l r) (CDiv (helper l) (helper r))]
    [(With bound-id named-expr bound-body)
     (helper (Call (Fun bound-id bound-body) named-expr))]
    [(Id name) (CRef (env name))]
    [(Fun bound-id bound-body)
     (CFun (preprocess bound-body (de-extend env bound-id)))]
    [(Call fun-expr arg-expr)
     (CCall (helper fun-expr) (helper arg-expr))]))

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
    [(CRef name) (list-ref env name)]
    [(CFun fun-expr)
     (FunV fun-expr env)]
    [(CCall fun-expr arg-expr)
     (let ([fval (eval fun-expr env)])
       (cases fval
         [(FunV bound-body f-env)
          (eval bound-body
                (cons (eval arg-expr env) f-env))]
         [else (error 'eval "`call' expects a function, got: ~s"
                      fval)]))]))

(: run : String -> Number)
;; evaluate a BRANG program contained in a string
(define (run str)
  (let ([result (eval (preprocess (parse str) de-empty-env) null)])
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


;; tests from Adam
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
(test (run "{+ 5 n}") =error> "empty-env: no mapping for n")
(test (run "{+ 5 {fun {x} {+ x 3}}}") =error>
      "arith-op: expected a number, got: (FunV (CAdd (CRef 0) (CNum 3)) ())")
(test (run "{call {+ 1 2} 6}") =error>
      "eval: `call' expects a function, got: (NumV 3)")
(test (run "{fun {x} {+ x 1}}") =error>
      (string-append "run: evaluation returned a non-number: "
                     "(FunV (CAdd (CRef 0) (CNum 1)) ())" ))