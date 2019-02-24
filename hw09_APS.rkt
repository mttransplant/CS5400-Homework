#lang pl 09

(define (Y f)
  ((lambda (x) (x x))
   (lambda (x) (f (lambda (z) ((x x) z))))))


(rewrite (define/rec (f x ...) E)
         => (define f
              (let ([g (Y (lambda (f)
                            (lambda (_)
                              (lambda (x ...)
                                (let ([f (f #f)])
                                  E)))))])
                (g #f))))

(define/rec (ackermann m n)
  (cond [(zero? m) (+ n 1)]
        [(zero? n) (ackermann (- m 1) 1)]
        [else      (ackermann (- m 1) (ackermann m (- n 1)))]))

(test (ackermann 3 3) => 61)
(test (ackermann 4 0) => 13)