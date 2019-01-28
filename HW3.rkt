#lang pl 03

;;  new rule for a unary sqrt in the BNF definition.
#| BNF for the new MUWAE language:
     <MUWAE> ::= <num>
             | { + <MUWAE> <MUWAE> }
             | { - <MUWAE> <MUWAE> }
             | { * <MUWAE> <MUWAE> }
             | { / <MUWAE> <MUWAE> }
             | { sqrt <MUWAE> } 
             | { with { <id> <MUWAE> } <MUWAE> }
             | <id>
|#

;; new variant to the AST type definition: Sqrt.
;; WAE abstract syntax trees
(define-type MUWAE
  [Num  (Listof Number)]
  [Add  MUWAE MUWAE]
  [Sub  MUWAE MUWAE]
  [Mul  MUWAE MUWAE]
  [Div  MUWAE MUWAE]
  [Sqrt MUWAE]
  [Id   Symbol]
  [With Symbol MUWAE MUWAE])

;; Fixing sqrt
(: sqrt+ : (Listof Number) -> (Listof Number))
;; a version of `sqrt' that takes a list of numbers, and return a
;; list with twice the elements, holding the two roots of each of
;; the inputs; throws an error if any input is negative.
(define (sqrt+ ns)
  (cond [(null? ns) null]
        [(< (first ns) 0) (error 'sqrt+ "requires a non-negative input")]
        [else (let ([x (sqrt (first ns))])
                (cons x (cons (- 0 x) (sqrt+ (rest ns)))))]))

;; Fixing the Arithmetic Operators
(: bin-op : (Number -> Number) (Listof Number) (Listof Number) -> (Listof Number))
;; applies a binary numeric function on all combinations
;; of numbers from the two input lists, and return the
;; list of all of the results
(define (bin-op op ls rs)
  (: helper : Number (Listof Number) -> (Listof Number))
  ;; helper applies the operator to number and a list
  ;; return the computed result in a list
  (define (helper l rs)
    (: f : Number -> Number)
    ;; f take 1 number and applies the operator
    ;; return the computed result
    (define (f n)
      (op l n))
    (map f rs))
  (if (null? ls)
      null
      (append (helper (first ls) rs) (bin-op op (rest ls) rs))))

(: parse-sexpr : Sexpr -> MUWAE)
;; parses s-expressions into WAEs
(define (parse-sexpr sexpr)
  (match sexpr
    [(number: n)    (Num (list n))]
    [(symbol: name) (Id name)]
    [(cons 'with more)
     (match sexpr
       [(list 'with (list (symbol: name) named) body)
        (With name (parse-sexpr named) (parse-sexpr body))]
       [else (error 'parse-sexpr "bad `with' syntax in ~s" sexpr)])]
    [(list '+ lhs rhs) (Add (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '- lhs rhs) (Sub (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '* lhs rhs) (Mul (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '/ lhs rhs) (Div (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list 'sqrt hs) (Sqrt (parse-sexpr hs))]
    [else (error 'parse-sexpr "bad syntax in ~s" sexpr)]))

(: parse : String -> MUWAE)
;; parses a string containing a WAE expression to a WAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

#| Formal specs for `subst':
   (`N' is a <num>, `E1', `E2' are <MUWAE>s, `x' is some <id>,
   `y' is a *different* <id>)
      N[v/x]                = N
      {+ E1 E2}[v/x]        = {+ E1[v/x] E2[v/x]}
      {- E1 E2}[v/x]        = {- E1[v/x] E2[v/x]}
      {* E1 E2}[v/x]        = {* E1[v/x] E2[v/x]}
      {/ E1 E2}[v/x]        = {/ E1[v/x] E2[v/x]}
      {sqrt E1}             = {sqrt E1[v/x]}
      y[v/x]                = y
      x[v/x]                = v
      {with {y E1} E2}[v/x] = {with {y E1[v/x]} E2[v/x]}
      {with {x E1} E2}[v/x] = {with {x E1[v/x]} E2}
|#

;; 5.the corresponding case in the subst implementation.
(: subst : MUWAE Symbol MUWAE -> MUWAE)
;; substitutes the second argument with the third argument in the
;; first argument, as per the rules of substitution; the resulting
;; expression contains no free instances of the second argument
(define (subst expr from to)
  (cases expr
    [(Num n) expr]
    [(Add l r) (Add (subst l from to) (subst r from to))]
    [(Sub l r) (Sub (subst l from to) (subst r from to))]
    [(Mul l r) (Mul (subst l from to) (subst r from to))]
    [(Div l r) (Div (subst l from to) (subst r from to))]
    [(Sqrt expr) (Sqrt (subst expr from to))]
    [(Id name) (if (eq? name from) to expr)]
    [(With bound-id named-expr bound-body)
     (With bound-id
           (subst named-expr from to)
           (if (eq? bound-id from)
               bound-body
               (subst bound-body from to)))]))

(: eval : MUWAE -> (Listof Number))
;; evaluates MUWAE expressions by reducing them to numbers
(define (eval expr)
  (cases expr
    [(Num n) n]
    [(Add l r) (bin-op + (eval l) (eval r))]
    [(Sub l r) (bin-op - (eval l) (eval r))]
    [(Mul l r) (bin-op * (eval l) (eval r))]
    [(Div l r) (bin-op / (eval l) (eval r))]
    [(Sqrt expr) (sqrt+ (eval expr))]
    [(With bound-id named-expr bound-body)
     (eval (subst bound-body
                  bound-id
                  (Num (eval named-expr))))]
    [(Id name) (error 'eval "free identifier: ~s" name)]))

(: run : String -> (Listof Number))
;; evaluate a MUWAE program contained in a string
(define (run str)
  (eval (parse str)))

;; tests
(test (run "5") => 5)
(test (run "{+ 5 5}") => 10)
(test (run "{with {x 5} {+ x x}}") => 10)
(test (run "{with {x {+ 5 5}} {+ x x}}") => 20)
(test (run "{with {x 5} {with {y {- x 3}} {+ y y}}}") => 4)
(test (run "{with {x {+ 5 5}} {with {y {- x 3}} {+ y y}}}") => 14)
(test (run "{with {x 5} {+ x {with {x 3} 10}}}") => 15)
(test (run "{with {x 5} {+ x {with {x 3} x}}}") => 8)
(test (run "{with {x 5} {+ x {with {y 3} x}}}") => 10)
(test (run "{with {x 5} {with {y x} y}}") => 5)
(test (run "{with {x 5} {with {x x} x}}") => 5)
(test (run "{with {x 1} y}") =error> "free identifier")

(test (run "{sqrt -1}")
      =error> "requires a non-negative input")
(test (run "{+ {sqrt 1} 3}")
      => '(4 2))
(test (run "{+ {/ {+ {sqrt 1} 3} 2} {sqrt 100}}")
      => '(12 -8 11 -9))
(test (run "{sqrt {+ 16 {* {+ 1 {sqrt 1}} {/ 9 2}}}}")
      => '(5 -5 4 -4))