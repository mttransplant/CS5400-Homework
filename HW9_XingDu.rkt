#lang pl 09

;; Y combinator consumes a funciton to create recursive functions 
(define (Y f)
  ((lambda (x) (x x))
   (lambda (x) (f (lambda (z) ((x x) z))))))

;; rewrite form in schlac 
(rewrite (define/rec (f x ...) E)
         => (define f
              (let ([g (Y (lambda (f)
                            (lambda (_)
                              (lambda(x ...)
                                (let ([f (f #f)])
                                  E)))))])
                (g #f))))

;; definition of ackermann 
(define/rec (ackermann m n)
  (cond [(zero? m) (+ n 1)]
        [(zero? n) (ackermann (- m 1) 1)]
        [else      (ackermann (- m 1) (ackermann m (- n 1)))]))

;; test case for ackermann
(test (ackermann 0 1) => 2)
(test (ackermann 1 0) => 2)
(test (ackermann 1 1) => 3)
(test (ackermann 3 3) => 61)

;; rewrite letfuns to implement two mutually-recursive functions
(rewrite (letfuns ([(f x ...) E] ...) B)
         => (let ([g (Y (lambda (funs)
                          (lambda (name)
                            (match name
                              ['f (lambda (x ...)
                                    (let ([f (funs 'f)] ...)
                                      E))] ...))))])
              (let ([f (g 'f)] ...)
                B)))

;; test case for even? odd?
(test (letfuns
       ([(even? n) (if (= n 0) #t (odd?  (- n 1)))]
        [(odd?  n) (if (= n 0) #f (even? (- n 1)))])
       (or (even? 123) (odd? 122) (even? 120))))

;; an extended example
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
(test (scan "(()123(246x12)) (blah)"))
(test (not (scan "(1232)")))
(test (not (scan "()(")))
(test (not (scan "())")))

(define minutes-spent 200)