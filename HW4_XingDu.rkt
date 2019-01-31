#lang pl 04

#| BNF for the ALGAE language:
     <ALGAE> ::= <num>
               | <True>
               | <False>
               | { + <ALGAE> ... }
               | { * <ALGAE> ... }
               | { - <ALGAE> <ALGAE> ... }
               | { / <ALGAE> <ALGAE> ... }
               | { < <ALGAE> <ALGAE> }
               | { <= <ALGAE> <ALGAE> }
               | { = <ALGAE> <ALGAE> }
               | { if <ALGAE> <ALGAE> <ALGAE> }
               | { not <ALGAE> }
               | { and <ALGAE> <ALGAE> }
               | { or <ALGAE> <ALGAE> }
               | { with { <id> <ALGAE> } <ALGAE> }
               | <id>
|#

;; ALGAE abstract syntax trees
(define-type ALGAE
  [Num  Number]
  [Bool Boolean]
  [Add  (Listof ALGAE)]
  [Mul  (Listof ALGAE)]
  [Sub  ALGAE (Listof ALGAE)]
  [Div  ALGAE (Listof ALGAE)]
  [Less ALGAE ALGAE]
  [LessEq ALGAE ALGAE]
  [If ALGAE ALGAE ALGAE]
  [Equal ALGAE ALGAE]
  [Id   Symbol]
  [With Symbol ALGAE ALGAE])

(: Not : ALGAE -> ALGAE)
;; fake bindings for Not
;; return false if ture and true if false
(define (Not expr)
  (If expr (Bool false) (Bool true)))

(: And : ALGAE ALGAE -> ALGAE)
;; return true if both are true
(define (And fst scd)
  (If fst scd (Bool false)))

(: Or : ALGAE ALGAE -> ALGAE)
;; return true if either one if true
(define (Or fst scd)
  (If fst (Bool true) scd))

(: parse-sexpr : Sexpr -> ALGAE)
;; parses s-expressions into ALGAEs
(define (parse-sexpr sexpr)
  ;; utility for parsing a list of expressions
  (: parse-sexprs : (Listof Sexpr) -> (Listof ALGAE))
  (define (parse-sexprs sexprs) (map parse-sexpr sexprs))
  (match sexpr
    [(number: n)    (Num n)]
    [(symbol: name)
     (cond
       [(eq? name 'True) (Bool true)]
       [(eq? name 'False) (Bool false)]
       [else (Id name)])]
    [(cons 'with more)
     (match sexpr
       [(list 'with (list (symbol: name) named) body)
        (With name (parse-sexpr named) (parse-sexpr body))]
       [else (error 'parse-sexpr "bad `with' syntax in ~s" sexpr)])]
    [(list '+ args ...)     (Add (parse-sexprs args))]
    [(list '* args ...)     (Mul (parse-sexprs args))]
    [(list '- fst args ...) (Sub (parse-sexpr fst) (parse-sexprs args))]
    [(list '/ fst args ...) (Div (parse-sexpr fst) (parse-sexprs args))]
    [(list '< fst scd) (Less (parse-sexpr fst) (parse-sexpr scd))]
    [(list '= fst scd) (Equal (parse-sexpr fst) (parse-sexpr scd))]
    [(list '<= fst scd) (LessEq (parse-sexpr fst) (parse-sexpr scd))]
    [(list 'If fst scd trd) (If (parse-sexpr fst)
                                (parse-sexpr scd)
                                (parse-sexpr trd))]
    [(list 'not arg) (Not (parse-sexpr arg))]
    [(list 'and fst scd) (And (parse-sexpr fst) (parse-sexpr scd))]
    [(list 'or fst scd) (Or (parse-sexpr fst) (parse-sexpr scd))]
    [else (error 'parse-sexpr "bad syntax in ~s" sexpr)]))

(: parse : String -> ALGAE)
;; parses a string containing an ALGAE expression to an ALGAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

#| Formal specs for `subst':
   (`N' is a <num>, `E1', `E2' are <ALGAE>s, `x' is some <id>, `y' is a
   *different* <id>)
      N[v/x]                = N
      {+ E ...}[v/x]        = {+ E[v/x] ...}
      {* E ...}[v/x]        = {* E[v/x] ...}
      {- E1 E ...}[v/x]     = {- E1[v/x] E[v/x] ...}
      {/ E1 E ...}[v/x]     = {/ E1[v/x] E[v/x] ...}
      {< E1 E2}[v/x]        = {< E1[v/x] E2[v/x]}
      {= E1 E2}[v/x]        = {= E1[v/x] E2[v/x]}
      {<= E1 E2}[v/x]       = {<= E1[v/x] E2[v/x]}
      {If E1 E2 E3][v/x]    = {If E1[v/x] E2[v/x] E3[v/x]}
      y[v/x]                = y
      x[v/x]                = v
      {with {y E1} E2}[v/x] = {with {y E1[v/x]} E2[v/x]}
      {with {x E1} E2}[v/x] = {with {x E1[v/x]} E2}
|#

(: subst : ALGAE Symbol ALGAE -> ALGAE)
;; substitutes the second argument with the third argument in the
;; first argument, as per the rules of substitution; the resulting
;; expression contains no free instances of the second argument
(define (subst expr from to)
  ;; convenient helper -- no need to specify `from' and `to'
  (: subst* : ALGAE -> ALGAE)
  (define (subst* x) (subst x from to))
  ;; helper to substitute lists
  (: substs* : (Listof ALGAE) -> (Listof ALGAE))
  (define (substs* exprs) (map subst* exprs))
  (cases expr
    [(Num n)        expr]
    [(Bool b)        expr]
    [(Add args)     (Add (substs* args))]
    [(Mul args)     (Mul (substs* args))]
    [(Sub fst args) (Sub (subst* fst) (substs* args))]
    [(Div fst args) (Div (subst* fst) (substs* args))]
    [(Less fst scd) (Less (subst* fst) (subst* scd))]
    [(Equal fst scd) (Equal (subst* fst) (subst* scd))]
    [(LessEq fst scd) (LessEq (subst* fst) (subst* scd))]
    [(If fst scd trd) (If (subst* fst) (subst* scd) (subst* trd))]
    [(Id name)      (if (eq? name from) to expr)]
    [(With bound-id named-expr bound-body)
     (With bound-id
           (subst* named-expr)
           (if (eq? bound-id from)
             bound-body
             (subst* bound-body)))]))

#| Formal specs for `eval':
     eval(N)            = N
     eval(B)            = B
     eval({+ E ...})    = evalN(E) + ...
     eval({* E ...})    = evalN(E) * ...
     eval({- E})        = -evalN(E)
     eval({/ E})        = 1/evalN(E)
     eval({- E1 E ...}) = evalN(E1) - (evalN(E) + ...)
     eval({/ E1 E ...}) = evalN(E1) / (evalN(E) * ...)
     eval({< E1 E2}) = evalN(E1) < evalN(E2)
     eval({= E1 E2}) = evalN(E1) = evalN(E2)
     eval({<= E1 E2}) = evalN(E1) <= evalN(E2)
     eval({If E1 E2 E3}) = if eval(E1) eval(E2) eval(E3)
     eval({Not E}) = eval({if E False True})
     eval({And E1 E2}) = eval({if E1 E2 False})
     eval({Or E1 E2}) = eval({if E1 True E2})
     eval(id)           = error!
     eval({with {x E1} E2}) = eval(E2[eval(E1)/x])
     evalN(E) = eval(E) if it is a number, error otherwise
|#

(: eval-number : ALGAE -> Number)
;; helper for `eval': verifies that the result is a number
(define (eval-number expr)
  (let ([result (eval expr)])
    (if (number? result)
      result
      (error 'eval-number "need a number when evaluating ~s, but got ~s"
             expr result))))

(: eval-boolean : ALGAE -> Boolean)
;; helper for `eval': verifies that the result is a boolean
(define (eval-boolean expr)
  (let ([result (eval expr)])
    (if (boolean? result)
      result
      (error 'eval-boolean "need a boolean when evaluating ~s, but got ~s"
             expr result))))

(: value->algae : (U Number Boolean) -> ALGAE)
;; converts a value to an ALGAE value (so it can be used with `subst')
(define (value->algae val)
  (cond [(number? val) (Num val)]
        [(boolean? val) (Bool val)]
        ;; Note: a `cond' doesn't make much sense now, but it will when
        ;; we extend the language with booleans.  Also, since we use
        ;; Typed Racket, the type checker makes sure that this function
        ;; is never called with something that is not in its type, so
        ;; there's no need for an `else' branch like
        ;;     [else (error 'value->algae "unexpected value: ~s" val)]
        ;; (Strictly speaking, there's no need for the last predicate
        ;; (which is the only one here until you extend this), but it's
        ;; left in for clarity.)
        ))

(: eval : ALGAE -> (U Number Boolean))
;; evaluates ALGAE expressions by reducing them to numbers or booleans
(define (eval expr)
  (cases expr
    [(Num n) n]
    [(Bool b) b]
    [(Add args) (foldl + 0 (map eval-number args))]
    [(Mul args) (foldl * 1 (map eval-number args))]
    [(Sub fst args) (- (eval-number fst)
                       (foldl + 0 (map eval-number args)))]
    [(Div fst args)    (let ([x (foldl * 1 (map eval-number args))])
                         (if (zero? x)
                            (error 'eval "division by zero")
                            (/ (eval-number fst) x)))]
    [(Less fst scd) (< (eval-number fst) (eval-number scd))]
    [(Equal fst scd) (= (eval-number fst) (eval-number scd))]
    [(LessEq fst scd) (<= (eval-number fst) (eval-number scd))]
    [(If fst scd trd) (if (eval-boolean fst) (eval scd) (eval trd))]
    [(With bound-id named-expr bound-body)
     (eval (subst bound-body
                  bound-id
                  ;; see the above `value->algae' helper
                  (value->algae (eval named-expr))))]
    [(Id name) (error 'eval "free identifier: ~s" name)]))

(: run : String -> (U Number Boolean))
;; evaluate an ALGAE program contained in a string
(define (run str)
  (eval (parse str)))

;; tests (for simple expressions)
(test (run "5") => 5)
(test (run "{+ 5 5}") => 10)
(test (run "{with {x {+ 5 5}} {+ x x}}") => 20)
(test (run "{with {x 5} {+ x x}}") => 10)
(test (run "{with {x {+ 5 5}} {with {y {- x 3}} {+ y y}}}") => 14)
(test (run "{with {x 5} {with {y {- x 3}} {+ y y}}}") => 4)
(test (run "{with {x 5} {+ x {with {x 3} 10}}}") => 15)
(test (run "{with {x 5} {+ x {with {x 3} x}}}") => 8)
(test (run "{with {x 5} {+ x {with {y 3} x}}}") => 10)
(test (run "{with {x 5} {with {y x} y}}") => 5)
(test (run "{with {x 5} {with {x x} x}}") => 5)
;; complete test coverage
(test (run "{with x {+ x 5}}") =error> "bad `with' syntax in (with x (+ x 5)")
(test (run "{with {x 4} {* x {/ x 2}}}") => 8)
(test (run "{1}") =error> "bad syntax in (1)")
(test (run "{with {x 1} y}") =error> "free identifier: y")
;; fix arithmetics
(test (run "{with {x 4} {+ x 5 3}}") => 12)
(test (run "{with {x 10} {- x 5 3}}") => 2)
(test (run "{with {x 3} {* x 5 3}}") => 45)
(test (run "{with {x 25} {/ x 5 5}}") => 1)
(test (run "{/ 7 0}") =error> "division by zero")
;; adding boolean and conditions
(test (run "{with {x 5} {< x 10}}") => #t)
(test (run "{= {with {x 3} {+ x 3}} 6}") => #t)
(test (run "{with {x 3} {<= x 3}}") => #t)
(test (run "{with {x 5} {= 5 x}}") => #t)
(test (run "True"))
(test (not (run "False")))
(test (run "{with {x True} x}") => #t)
(test (run "{with {x 0} {If True x 1}}") => 0)
(test (run "{If 1 2 3}") =error> "need a boolean when evaluating")
(test (run "{with {x True} {+ 5 x}}") =error> "need a number when evaluating")
(test (run "{If False {+ 1 2} {with {x 10} {+ 2 x}}}") => 12)
;; futher extensions: not, and, or
(test (run "{not False}") => #t)
(test (run "{and True True}") => #t)
(test (run "{and True False}") => #f)
(test (run "{or False True}") => #t)
(test (run "{or False False}") => #f)
(test (run "{and True 123}") => 123)
(test (run "{and 124 456}") =error> "need a boolean when evaluating")