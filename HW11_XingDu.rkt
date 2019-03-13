#lang pl 11
;; First, you need to explain
;; why tail call elimination is a crucial aspect
;; in making all of this work properly.

;; Answer: tail call elimination means that
;; calls that are in tail position of a function are "eliminated"
;; which means the stack frame for function call can be saved.
;; For Fibonacci problem, this is important. To keep track of
;; the call stacks will take up space in an exponential way.
;; Tail call elimination will help to prevent the stack overflow.

;; we represent labels (goto targets) as thunks, and registers (or
;; memory locations in general) as integer boxes.
(define-type Label    = (-> Integer))
(define-type Register = (Boxof Integer))

;; "X = Y"
;; assigns the contents of register Y to register X
(: mov : Register Register -> Void)
(define (mov X Y) (set-box! X (unbox Y)))

;; "X = N"
;; assigns the constant N (an "immediate" value)  to register X
;; (: movi : Register Integer -> Void)
;; (define (movi X N) (set-box! X N))

;; "X += Y"
;; increments register X by register Y
(: add : Register Register -> Void)
(define (add X Y) (set-box! X (+ (unbox X) (unbox Y))))

;; "X += N"
;; increments register X by a constant N
;; (: addi : Register Integer -> Void)
;; (define (addi X N) (set-box! X (+ (unbox X) N)))

;; "X -= Y"
;; deccrements register X by register Y
(: sub : Register Register -> Void)
(define (sub X Y) (set-box! X (- (unbox X) (unbox Y))))

;; "X -= N"
;; decrements register X by a constant N
(: subi : Register Integer -> Void)
(define (subi X N) (set-box! X (- (unbox X) N)))

;; "X &= Y"
;; sets X to the bitwise "and" of X and Y
;; (: and : Register Register -> Void)
;; (define (and X Y) (set-box! X (bitwise-and (unbox X) (unbox Y))))

;; "X &= N"
;; sets X to the bitwise "and" of X and a constant N
;; (: andi : Register Integer -> Void)
;; (define (andi X N) (set-box! X (bitwise-and (unbox X) N)))

;; "X >>= N"
;; shifts register X right by N bits
(: shri : Register Integer -> Void)
(define (shri X N) (set-box! X (arithmetic-shift (unbox X) (- N))))

;; "goto L"
;; (goto L) jumps to the label -- labels are represented as nullary
;; functions (also called "thunks")
(: goto : Label -> Integer)
(define (goto L) (L))

;; "ret X"
;; return the contents of register X
(: ret : Register -> Integer)
(define (ret X) (unbox X))

;; "ret N"
;; return the constant N
(: reti : Integer -> Integer)
(define (reti N) N)

;; "if X=0 goto L1 else goto L2"
;; if register X is zero, jump to L1, else jump to L2
(: if0 : Register Label Label -> Integer)
(define (if0 a l1 l2) (if (zero? (unbox a)) (goto l1) (goto l2)))

;; "if X>0 goto L1 else goto L2"
;; if register X is positive, jump to L1, else jump to L2
(: ifp : Register Label Label -> Integer)
(define (ifp a l1 l2) (if (positive? (unbox a)) (goto l1) (goto l2)))

(: fib : Integer -> Integer)
;; compute the nth fibonacci number using the assembly language
(define (fib n)
  (: A : Register) (define A (box 0))
  (: B : Register) (define B (box 1))
  (: C : Register) (define C (box 0))
  (: N : Register) (define N (box n))
  ;;
  (: main : Label)
  (: step : Label)
  (: done : Label)
  ;;
  (define (main) (if0  N done step))
  (define (step) (mov  C A)
                 (add  C B)
                 (mov  A B)
                 (mov  B C)
                 (subi N 1)
                 (goto main))
  (define (done) (ret  A))
  ;;
  (main))
;; test
(test (map fib '(0 1 2 3 4 5 6 7 8 9 10))
      => '(0 1 1 2 3 5 8 13 21 34 55))

(: more-ones? : Integer Integer -> Integer)
;; returns 1 if `a' has more 1s in its binary representation than `b'
(define (more-ones? a b)
  (: A : Register) (define A (box a))
  (: B : Register) (define B (box b))
  (: C : Register) (define C (box 0)) ; temp register
  (: D : Register) (define D (box 0)) ; temp register
  (: A-ONES : Register) (define A-ONES (box 0)) ; store number of 1 in binary(a)
  (: B-ONES : Register) (define B-ONES (box 0)) ; store number of 1 in binary(b)
  ;; ... more registers ...
  ;;
  (: main : Label)
  (: sumA : Label) ;; called by main function
  (: compareAB : Label) ;; compare A and B 1's count
  (: sumA-cont : Label) ;; when A not reach 0, continue step
  (: compareAB-cont : Label) ;; when B not reach 0, continue step
  (: diffAB : Label) ;; return if A-ONES larger than B-ONES
  (: true : Label)
  (: false : Label)
  ;; ... more labels ...
  ;;
  ;; Strategy: decimal to binary algorithm
  ;; divide by 2, take the remainder
  ;; compare A and B each step
  ;; if any one reaches 0 first, 
  ;; then finish the other and compare
  (define (main) (sumA))  
  
  (define (sumA)
    (if0 A compareAB sumA-cont))
  
  (define (sumA-cont) 
    (mov C A) ; save value in register A to register C
    (shri A 1)
    (mov D A) ; A / 2 save to D
    (add D A) ; add D by A / 2
    (sub C D) ; calculate remainder
    (add A-ONES C) ; add to counter
    (goto sumA))

  (define (compareAB)
    (if0 B diffAB compareAB-cont))

  (define (compareAB-cont)
    (mov C B)
    (shri B 1)
    (mov D B)
    (add D B)
    (sub D C)
    (add B-ONES C)
    (goto compareAB))

  (define (diffAB)
    (sub A-ONES B-ONES)
    (ifp A-ONES true false))

  (define (true) (reti 1))

  (define (false) (reti 0))
  ;; ... more thunks ...
  ;;
  (main))
;; tests
(test (more-ones? 0 0) => 0)
(test (more-ones? 1 0) => 1)
(test (more-ones? 1 2) => 0)
(test (more-ones? 2 0) => 1)
(test (more-ones? 0 1) => 0)
(test (more-ones? 0 2) => 0)
(test (more-ones? 2 1) => 0)
(test (more-ones? 2 2) => 0)
(test (more-ones? 3 1) => 1)