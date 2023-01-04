#lang racket
(require plot)

; make big vector
(define (values->list proc) (call-with-values proc list))
(define values->snd (compose cadr values->list))
(define values->third (compose caddr values->list))

(define (test n)
  (define v (build-vector n (lambda (x) x)))
  (map (lambda (j) (values->snd (thunk (time-apply (curry vector-ref v) (list j)))))
       (range n)))
;(apply max (test (inexact->exact 1e6))) ;70,12 <- high variance, maybe gc

(define (test-vec-access n) ;8
  (define en (expt 10 n))
  (define en- (expt 10 (- n 1)))
  (define v (build-vector en (const 0)))
  (define pts
    (points
     (map (lambda (j)
            (vector j (values->third
                       (thunk (time-apply (curry vector-ref v) (list j))))))
          (range 0 en en-))))
  (plot pts))

; out of memory failure during allocation for 1e9
; really quite constant time access for 1e8
; most of time taken up by allocation in the first place
; actually accesses are effectively
; can't tell how long though
; would have to do a test with accessing all elements and dividing
; but should be on order of nanoseconds

(define (test-average-vec-access n) ;~.15 us
  (define en (expt 10 n))
  (define v (build-vector en (const 0)))
  (let-values ([(a b c d) (time-apply (lambda (x) (map (lambda (i) (vector-ref v i)) (range x)))
                                      (list en))])
    (exact->inexact (/ c en))))

(define (test-average-vec-set n) ;.17 us
  (define en (expt 10 n))
  (define v (build-vector en (const 0)))
  (let-values ([(a b c d) (time-apply (lambda (x) (map (lambda (i) (vector-set! v i 1)) (range x)))
                                      (list en))])
    (exact->inexact (/ c en))))

(define (test-average-vec-access-caching n) ;~.16 us
  (define en (expt 10 n))
  (define v (build-vector en (const 0)))
  (let-values ([(a b c d) (time-apply (lambda (x) (map (lambda (i) (vector-ref v 0)) (range x)))
                                      (list en))])
    (exact->inexact (/ c en))))

; so not effected by caching? what if read in reverse order?

(define (test-average-vec-access-caching-rev n) ;~.18 us <- no caching
  (define en (expt 10 n))
  (define v (build-vector en (const 0)))
  (let-values ([(a b c d) (time-apply (lambda (x) (map (lambda (i) (vector-ref v (- en i 1))) (range x)))
                                      (list en))])
    (exact->inexact (/ c en))))

(define (test-average-vec-access-caching-rand n) ;.34 us <- not from caching, all ram
  ; time diff prob from evaluating random
  (define en (expt 10 n))
  (define v (build-vector en (const 0)))
  (let-values ([(a b c d)
                (time-apply (lambda (x) (map (lambda (i) (vector-ref v (random en)))
                                             (range x)))
                            (list en))])
    (exact->inexact (/ c en))))

; checked clock rate -- 1.4GHz ->1.4e9 ops/sec -> 1 sec / 1.4e9 ops -> .7e-9 sec/op
; .7 ns / op ~ 1 ns
; so taking around 100 clocks to do an access or set
; (.17,-6)/(7,-10) = (17,-8)/(7,-10) = (2.2,2) = 200 instructions
; memory fetch is hundreds of instruction cycles
;  getting factor of 2 from not random order? -- more likely that is how long many random evaluations take
;  all held in ram, not disk, so about the same

; so ram memory model -- function from finset n to finset m take constant time
;  latency 100's of nanoseconds, throughput probably nanosecs

; idea of hash table -- have extra information about fxn from fn to fm
;  namely know that only a subset of domain will be used in practice
;  so add another table for sparsity

; suppose know all inputs are divisible by 7
; define i <- index fxn f(i(x)), where i(x) = x/7
;  notice that the complexity of i scales in x
(define n 1e5)
(define (f x) ; f : A->B
  (+ 22 (/ x 7)))
(define v1 (list->vector (map f (range n))))
; (eq? (f x) (f1 x)) <- like a cached answer, trading memory for time
(define (f1 x) (vector-ref v1 x))
(define (i x) (/ x 7))
(define v2 (list->vector (map f (range 0 n 7))))
(define (f2 x) (vector-ref v2 (i x))) ; (eq? (f x) (f1 x) (f2 x))
; but what is the point of smaller lookup table if constant time anyway
; well memory allocation itself takes time
; also saves time of pre-computing f on domain where it will never be applied
;  f1 and f2 are about ways of pre-computing
;  if you do not now anything about the f's inputs, f1 is the best you can do

; so this is the story about hashmaps, what about hashsets?
;  just when function is to f:A->finset 2, multisets are f:A->Nat

; datastructures (or maybe just tables/trees/sets/multisets)
;  are about ways of pre-computing functions
;  making different trade-offs between memory and time

; ok, so what about probabilistic components
; Suppose the effective domain is still A, but there is a distribution over A
;  if it is uniform, f1 is still the best you can do
; suppose I have p:A->[0,1] which says what frac of time I will receive an input

; how do I talk about about how long allocation takes

(define ski-order '((S . 1) (K . 2) (I . 3)))
(define order-ski '((1 . S) (2 . K) (3 . I)))
(define (ski-to-quat t)
  (match t
    [(cons a b) (append (list 0) (ski-to-quat a) (ski-to-quat b))]
    [x (list (cdr (assoc x ski-order)))]))
;(ski-to-quat '((I . I) . K))
;'(0 0 3 3 2)
;(ski-to-quat 'I) ; '(3)
;(ski-to-quat '(I . I)) ; '(0 3 3)

(define (quat-to-ski l fuel)
  (let ([nxt (car l)])
     (if (and (= 0 fuel) (not (= 0 nxt)))
         (cdr (assoc nxt order-ski))
         (if (= 0 nxt)
             (quat-to-ski (cdr l) (+ 2 fuel))
             (cons nxt (quat-to-ski (cdr l) (- fuel 1)))))))


(define (split l)
  (define (split-index l)
    (let ([out 0] [fuel 2])
      (for ([i (range (length l))] #:break (= fuel 1))
        (set! out i)
        (if (= 0 (list-ref l i))
            (set! fuel (+ fuel 2))
            (set! fuel (- fuel 1))))
      out))
  (split-at l (split-index l)))

;(define (quat-to-ski l)
;  (if (null? l) l
;      (let ([nxt (car l)])
;        (if (= 0 nxt)
;            (let-values ([(left right) (split (cdr l))])
;              (cons (quat-to-ski left) (quat-to-ski right)))
;            nxt))))
