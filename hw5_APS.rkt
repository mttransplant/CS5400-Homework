#lang pl 05

(define minutes-spent 000)

#|
Completed:
Part 0: Complete Coverage
Part 1: Fixing Arithmetics
Part 2: Adding Booleans and Conditionals
Part 3: Further Extensions

Working on:
Part 3b: Further Extensions

Yet to start:
Part 4: Moving to Programs
Part 5: Making the Language Higher Order
|#

#| BNF for the ALGAE language:
     <ALGAE> ::= <num>
               | { + <ALGAE> ... }
               | { * <ALGAE> ... }
               | { - <ALGAE> <ALGAE> ... }
               | { / <ALGAE> <ALGAE> ... }
               | { with { <id> <ALGAE> } <ALGAE> }
               | <id>
               | { < <ALGAE> <ALGAE> }
               | { = <ALGAE> <ALGAE> }
               | { <= <ALGAE> <ALGAE> }
               | Bool
               | True
               | False
               | { If <ALGAE> <ALGAE> <ALGAE> }
               | { not Bool }
               | { and Bool ... }
               | { or Bool ... }
|#

;; ALGAE abstract syntax trees
(define-type ALGAE
  [Num  Number]
  [Add  (Listof ALGAE)]
  [Mul  (Listof ALGAE)]
  [Sub  ALGAE (Listof ALGAE)]
  [Div  ALGAE (Listof ALGAE)]
  [Id   Symbol]
  [With Symbol ALGAE ALGAE]
  [Less ALGAE ALGAE]
  [Equal ALGAE ALGAE]
  [LessEq ALGAE ALGAE]
  [Bool Boolean]
  [If ALGAE ALGAE ALGAE])

(: Not : ALGAE -> ALGAE)
;; fake binding for Not
;; returns the opposite boolean of what's given
(define (Not expr)
  (If expr (Bool #f) (Bool #t)))

(: And : (Listof ALGAE) -> ALGAE)
;; fake binding for And
;; returns True if both exprs are True, else returns False
(define (And args)
  (cond [(null? args) (Bool #t)]
        [(null? (rest args)) (first args)]
        [else (If (first args) (And (rest args)) (Bool #f))]))

(: Or : (Listof ALGAE) -> ALGAE)
;; fake binding for Or
;; returns True if either expr is True, else returns False
(define (Or args)
  (cond [(null? args) (Bool #f)]
        [(null? (rest args)) (first args)]
        [else (If (first args) (Bool #t) (Or (rest args)))]))

(: parse-sexpr : Sexpr -> ALGAE)
;; parses s-expressions into ALGAEs
(define (parse-sexpr sexpr)
  ;; utility for parsing a list of expressions
  (: parse-sexprs : (Listof Sexpr) -> (Listof ALGAE))
  (define (parse-sexprs sexprs) (map parse-sexpr sexprs))
  (match sexpr
    [(number: n)    (Num n)]
    [(symbol: name) (cond [(eq? name 'True) (Bool true)]
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
    [(list '< fst scnd) (Less (parse-sexpr fst) (parse-sexpr scnd))]
    [(list '= fst scnd) (Equal (parse-sexpr fst) (parse-sexpr scnd))]
    [(list '<= fst scnd) (LessEq (parse-sexpr fst) (parse-sexpr scnd))]
    [(list 'If cnd fst scnd) (If (parse-sexpr cnd)
                                 (parse-sexpr fst)
                                 (parse-sexpr scnd))]
    [(list 'not arg) (Not (parse-sexpr arg))]
    [(list 'and args ...) (And (parse-sexprs args))]
    [(list 'or args ...) (Or (parse-sexprs args))]
    [else (error 'parse-sexpr "bad syntax in ~s" sexpr)]))

(: parse : String -> ALGAE)
;; parses a string containing an ALGAE expression to an ALGAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

#| Formal specs for `subst':
   (`N' is a <num>, `E1', `E2' are <ALGAE>s, `x' is some <id>, `y' is a
   *different* <id>, `B' is a True/False)
      N[v/x]                = N
      {+ E ...}[v/x]        = {+ E[v/x] ...}
      {* E ...}[v/x]        = {* E[v/x] ...}
      {- E1 E ...}[v/x]     = {- E1[v/x] E[v/x] ...}
      {/ E1 E ...}[v/x]     = {/ E1[v/x] E[v/x] ...}
      y[v/x]                = y
      x[v/x]                = v
      {with {y E1} E2}[v/x] = {with {y E1[v/x]} E2[v/x]}
      {with {x E1} E2}[v/x] = {with {x E1[v/x]} E2}
      {< E1 E2}[v/x]        = {< E1[v/x] E2[v/x]}
      {= E1 E2}[v/x]        = {= E1[v/x] E2[v/x]}
      {<= E1 E2}[v/x]       = {<= E1[v/x] E2[v/x]}
      B[v/x]                = B
      {If B E1 E2}[v/x]     = {If B[v/x] E1[v/x] E2[v/x]}
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
    [(Add args)     (Add (substs* args))]
    [(Mul args)     (Mul (substs* args))]
    [(Sub fst args) (Sub (subst* fst) (substs* args))]
    [(Div fst args) (Div (subst* fst) (substs* args))]
    [(Id name)      (if (eq? name from) to expr)]
    [(With bound-id named-expr bound-body)
     (With bound-id
           (subst* named-expr)
           (if (eq? bound-id from)
               bound-body
               (subst* bound-body)))]
    [(Less fst scnd) (Less (subst* fst) (subst* scnd))]
    [(Equal fst scnd) (Equal (subst* fst) (subst* scnd))]
    [(LessEq fst scnd) (LessEq (subst* fst) (subst* scnd))]
    [(Bool b) expr]
    [(If cnd fst scnd) (If (subst* cnd) (subst* fst) (subst* scnd))]))

#| Formal specs for `eval':
     eval(N)                = N
     eval({+ E ...})        = evalN(E) + ...
     eval({* E ...})        = evalN(E) * ...
     eval({- E})            = -evalN(E)
     eval({/ E})            = 1/evalN(E)
     eval({- E1 E ...})     = evalN(E1) - (evalN(E) + ...)
     eval({/ E1 E ...})     = evalN(E1) / (evalN(E) * ...)
     eval(id)               = error!
     eval({with {x E1} E2}) = eval(E2[eval(E1)/x])
     evalN(E)               = eval(E) if it is a number, error otherwise
     eval({< E1 E2})        = evalN(E1) < evalN(E2)
     eval({= E1 E2})        = evalN(E1) = evalN(E2)
     eval({<= E1 E2})       = evalN(E1) <= evalN(E2)
     eval(B)                = B
     eval({If B E1 E2})     = if evalB(B) then evalN(E1) else evalN(E2)
     eval({not E})          = eval({if E False True})
     eval({And E})          = E
     eval({And E ...})      = eval({if (first(E)) (And (rest(E))) False})
     eval({Or E})           = E
     eval({Or E1 E2})       = eval({if (first(E)) True (Or (rest(E)))})
|#

(: eval-number : ALGAE -> Number)
;; helper for `eval': verifies that the result is a number
(define (eval-number expr)
  (let ([result (eval expr)])
    (if (number? result)
        result
        (error 'eval-number "need a number when evaluating ~s, but got ~s"
               expr
               result))))

(: eval-boolean : ALGAE -> Boolean)
;; helper for `eval': verifies that the result is a boolean
(define (eval-boolean expr)
  (let ([result (eval expr)])
    (if (boolean? result)
        result
        (error 'eval-boolean "need a boolean when evaluating ~s, but got ~s"
               expr
               result))))

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
;; evaluates ALGAE expressions by reducing them to numbers
(define (eval expr)
  (cases expr
    [(Num n) n]
    [(Add args) (foldl + 0 (map eval-number args))]
    [(Mul args) (foldl * 1 (map eval-number args))]
    [(Sub fst args) (if (null? args)
                        (- (eval-number fst))
                        (- (eval-number fst)
                           (foldl + 0 (map eval-number args))))]
    [(Div fst args) (let ([denom (foldl * 1 (map eval-number args))])
                      (cond [(null? args) (/ 1 (eval-number fst))]
                            [(zero? denom)
                             (error 'eval "attempted to divide by zero")]
                            [else (/ (eval-number fst) denom)]))]
    [(With bound-id named-expr bound-body)
     (eval (subst bound-body
                  bound-id
                  ;; see the above `value->algae' helper
                  (value->algae (eval named-expr))))]
    [(Id name) (error 'eval "free identifier: ~s" name)]
    [(Less fst scnd) (< (eval-number fst) (eval-number scnd))]
    [(Equal fst scnd) (eq? (eval-number fst) (eval-number scnd))]
    [(LessEq fst scnd) (<= (eval-number fst) (eval-number scnd))]
    [(Bool b) b]
    [(If cnd fst scnd) (if (eval-boolean cnd)
                           (eval fst)
                           (eval scnd))]))

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
;; completing test coverage
(test (run "{with {x 5} {* x {with {y 3} x}}}") => 25)
(test (run "{with {x 5} {/ {with {y 100} y} x}}") => 20)
(test (run "{+ 1 s}") =error> "eval: free identifier: s")
(test (run "{with 5 x}")
      =error> "parse-sexpr: bad `with' syntax in (with 5 x)")
(test (run "{abs -5}") =error> "parse-sexpr: bad syntax in (abs -5)")
;; fixing arethmetics
(test (run "{+ 5 4 3 2 1}") => 15)
(test (run "{- 10 3 2 1}") => 4)
(test (run "{* 10 2 {/ 500 10 5}}") => 200)
(test (run "{- 5}") => -5)
(test (run "{/ 2}") => 1/2)
(test (run "{/ 1 0}") =error> "attempted to divide by zero")
;; adding booleans and conditionals
(test (run "{with {x False} {If x 5 4}}") => 4)
(test (run "{with {x True} {If x 5 4}}") => 5)
(test (run "{If 5 4 3}") =error>
      "eval-boolean: need a boolean when evaluating (Num 5), but got 5")
#;(test (run "{If True True 3}") =error>
        "eval-number: need a number when evaluating (Bool #t), but got #t")
(test (run "{+ True 3}") =error>
      "eval-number: need a number when evaluating (Bool #t), but got #t")
(test (run "{If True True 3}") => #t)
(test (run "{with {x 0} {If True x 3}}") => 0)
(test (run "{with {x 9} {with {y {- x 5}}{< x y}}}") => #f)
(test (run "{with {x 0} {with {y {= 0 0}} {If y {If {<= 1 x} 0 1} -1}}}") => 1)
;; adding not, and, or
(test (run "{not True}") => #f)
(test (run "{not False}") => #t)
(test (run "{and True True}") => #t)
(test (run "{and True False}") => #f)
(test (run "{and False True}") => #f)
(test (run "{and False False}") => #f)
(test (run "{or {not True} {not False}}") => #t)
(test (run "{or True True}") => #t)
(test (run "{or False False}") => #f)
(test (run "{and True 123}") => 123)
(test (run "{or False 123}") => 123)
(test (run "{and 123 True}") =error>
      "eval-boolean: need a boolean when evaluating (Num 123), but got 123")
(test (run "{or 123 True}") =error>
      "eval-boolean: need a boolean when evaluating (Num 123), but got 123")
;; further extensions
(test (run "{and True True True True}") => #t)
(test (run "{and True True True True False}") => #f)
(test (run "{and True True True True 123}") => 123)
(test (run "{and}") => #t)
(test (run "{and True}") => #t)
(test (run "{and False}") => #f)
(test (run "{or True False False False False}") => #t)
(test (run "{or False False False False True}") => #t)
(test (run "{or False False False False False}") => #f)
(test (run "{or}") => #f)
(test (run "{or True}") => #t)
(test (run "{or False}") => #f)
(test (run "{or False 123}") => 123)