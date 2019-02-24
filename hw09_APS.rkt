#lang pl 09

;; Y-combinator takes a single-argument function and returns a recursive
;; version
(define (Y f)
  ((lambda (x) (x x))
   (lambda (x) (f (lambda (z) ((x x) z))))))

;; define/rec takes a multi-argument function and returns a recursive version
;; by applying the Y-combinator
(rewrite (define/rec (f x ...) E)
         => (define f
              (let ([g (Y (lambda (f)
                            (lambda (_)
                              (lambda (x ...)
                                (let ([f (f #f)])
                                  E)))))])
                (g #f))))

;; the Ackermann function is one of the simplest and earliest-discovered
;; examples of a total computable function that is not primitive recursive.
;; source: https://en.wikipedia.org/wiki/Ackermann_function
(define/rec (ackermann m n)
  (cond [(zero? m) (+ n 1)]
        [(zero? n) (ackermann (- m 1) 1)]
        [else      (ackermann (- m 1) (ackermann m (- n 1)))]))

;; tests for ackermann
(test (ackermann 3 3) => 61)
(test (ackermann 4 0) => 13)

;; letfuns takes a specially formed mutually referrential set of functions
;; and returns the recurisive version
(rewrite (letfuns ([(f x ...) E] ...) B)
         => (let ([g (Y (lambda (funs)
                          (lambda (name)
                            (match name
                              ['f (lambda (x ...)
                                    (let ([f (funs 'f)] ...)
                                      E))] ...))))])
              (let ([f (g 'f)] ...)
                B)))

;; tests for even?/odd?
(test (not (letfuns ([(even? n) (or (= n 0) (odd?  (- n 1)))]
                     [(odd?  n) (if (= n 0) #f (even? (- n 1)))])
                    (even? 123))))

(test (letfuns ([(even? n) (or (= n 0) (odd?  (- n 1)))]
                [(odd?  n) (if (= n 0) #f (even? (- n 1)))])
               (list (even? 123) (even? 124) (odd? 123) (odd? 124)))
      => (list #f #t #t #f))

;; an extended example
;; scan is an automaton (a state machine) that consumes a string,
;; and returns #t if the parens in the string are balanced, and if every
;; continuous block of numeric characters is strictly increasing.
(define scan
  (letfuns ([(start str)  (loop (explode-string str) 0)]
            [(loop l n)   (match l
                            [(list)
                             (zero? n)]
                            [(cons 'open more)
                             (loop more (add1 n))]
                            [(cons 'close more)
                             (and (> n 0) (loop more (sub1 n)))]
                            [(cons (number: m) more)
                             (nums more m n)]
                            [(cons _ more)
                             (loop more n)])]
            [(nums l m n) (match l
                            [(cons (number: m1) more)
                             (and (< m m1) (nums more m1 n))]
                            [else (loop l n)])])
           start))

;; tests for scan
(test (scan "(()123(246x12)) (blah)"))
(test (not (scan "(1232)")))
(test (not (scan "()(")))
(test (not (scan "())")))

(define minutes-spent 180)