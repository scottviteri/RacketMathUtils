#lang racket

(require srfi/1)
(require (only-in racket/list remove-duplicates cartesian-product index-of))
(require racket/set)
(require (only-in relation partial app curry andf onto))

(define m '((1 2) (3 4)))
(define (mat-row m j) (list-ref m j))

(define (mat-col m i) (map car m))
(define (mat-ind m j i) (list-ref (mat-row m j) i))
(define sum (partial apply +))
(define mul (partial apply *))

(define (v* v1 v2) (sum (map mul (zip v1 v2))))

(define transpose (partial apply zip))

(define (m* m1 m2)
  (let ([m2t (transpose m2)])
    (map (lambda (left-vec) (map (app v* left-vec _) m2t)) m1)))

(define (vec . l) (map list l))

(define (v+ v1 v2) (map sum (zip v1 v2)))
(define (m+ m1 m2) (map (partial apply v+) (zip m1 m2)))

(define (deep-apply f m) (map (partial map f) m))
(define (s* k m) (deep-apply (partial * k) m))

(define (impulse i len) (map (lambda (x) (if (= x i) 1 0)) (iota len)))
(define (m-id dim) (map (app impulse _ dim) (iota dim)))

(define v= equal?)
(define all (curry fold andf #t))

(define (m= m1 m2)
  (and (eq? (length m1) (length m2))
       (all (map (partial apply v=) (zip m1 m2)))))

(define (square m) (m* m m))

(define (m-pow m n)
  (define (odd? n) (= 1 (modulo n 2)))
  (if (= n 0) (m-id (length m))
      (if (= n 1) m
          (if (odd? n)
              (m* m (m-pow m (- n 1)))
              (square (m-pow m (/ n 2)))))))

(define (cube m) (m-pow m 3))
(define (hypercube m) (m-pow m 4))

(define (m-mod m n) (deep-apply (lambda (y) (modulo y n)) m))
(define (m-pow-mod m n k)
  (m-mod (m-pow m n) k))

(define (all-vals dim top)
  (letrec (;[l (iota (* 2 top) (- top))]
           [l (iota top)]
           [ls (make-list (* dim dim) l)])
    (apply cartesian-product ls)))

(define (split l n)
  (if (null? l) '()
      (if (< (length l) n) (cons l '())
          (cons (take l n) (split (drop l n) n)))))

(define (all-matrices dim top)
  (map (lambda (l) (split l dim)) (all-vals dim top)))

(define (all-mod-matrices dim mod top)
  (map (lambda (m) (m-mod m mod)) (all-matrices dim top)))

(define (test condition dim top)
  (let ([target (m-id dim)]
        [ms (all-matrices dim top)])
    (filter (condition m target) ms)))

;(test square 3)
(define (count-zeros m)
  (sum (map (lambda (row) (count (lambda (x) (= x 0)) row)) m)))

(define (perm l)
  ;input must be set= (iota (length l))
  (map (app impulse _ (length l)) l))

(define (rot-mat n) (perm (map (lambda (x) (modulo x n)) (iota n 1))))
(define (conjoin m1 m2)
  (let ([l1 (length (car m1))]
        [l2 (length (car m2))])
    (append (map (lambda (row) (append row (make-list l2 0))) m1)
            (map (lambda (row) (append (make-list l1 0) row)) m2))))

(define (p m)
  (map (lambda (x) (display x) (newline)) m) 1)

(define six-periodic (conjoin (rot-mat 3) (rot-mat 2)))

(define (sqrts n)
  (filter (lambda (x) (= 1 (modulo (* x x) n))) (iota n)))
(define (trips n)
  (filter (lambda (x) (= 1 (modulo (* x x x) n))) (iota n)))
(define (sqrts3 n)
  (filter (lambda (x) (= 3 (modulo (* x x) n))) (iota n)))
(define (sqrtsk n k)
  (filter (lambda (x) (= k (modulo (* x x) n))) (iota n)))

(define (find-solns n)
  (filter (lambda (x) (= 1 (modulo (* 2 (expt x 2)) n))) (iota n)))
(define (quats n)
  (filter (lambda (x) (= 1 (modulo (* x x x x) n))) (iota n)))

(define (enumerate l) (zip (iota (length l)) l))
(define (count-sqrts n) (enumerate (map (compose length sqrts) (iota n))))
(define (is-prime n)
  (all (map (lambda (d) (not (= 0 (modulo n d))))
            (iota (- n 2) 2))))
(define (primes-up-to n)
  (filter is-prime (iota (- n 1) 2)))

(define (power-period base domain-size)
  (if (= base 0) 0
      (let ([l (filter (lambda (k) (= 1 (modulo (expt base k) domain-size)))
                       (iota (- domain-size 1) 1))])
        (if (null? l) domain-size (car l)))))

(define (check m) (and (= (caar m) (caadr m)) (= (cadar m) (- 5 (cadadr m)))))

(define (m-pows m k mod) (map (lambda (x) (m-pow-mod m x mod)) (iota k)))

(define (m-per m mod)
  (define (m-per-aux m orig cnt)
    (if (> cnt 100) 10
      (let ([meq (m= (m-id 2) m)])
        (if meq cnt (m-per-aux (m-mod (m* orig m) mod) orig (+ cnt 1))))))
  (m-per-aux m m 1))

(define (normalize cycle)
  (remove-duplicates (filter (lambda (x) (not (= (car x) (cdr x)))) cycle)))

(define (rot n k)
  (normalize (map (lambda (x) (cons x (modulo (+ x k) n))) (iota n))))

(define (apply-cycle cycle x)
  (let ([result (assoc x cycle)])
    (if result (cdr result) x)))

(define (compose-cycles f g)
  (normalize
   (set->list
    (letrec ([d1 (list->set (map car f))]
             [d2 (list->set (map car g))]
             [domain (set-union d1 d2)])
      (set-map domain
               (lambda (x) (cons x (apply-cycle f (apply-cycle g x)))))))))

(define (mirror-pairs pairs)
  (append (map (lambda (x) (cons (cdr x) (car x))) pairs) pairs))

(define (face-flip n k)
  (let ([mod (lambda (x) (modulo x n))]
        [len (if (= 0 (modulo n 2)) (/ n 2) (/ (- n 1) 2))])
    (mirror-pairs (map (lambda (i) (cons (mod (- k i)) (mod (+ k i 1)))) (iota len)))))

(define (vertex-flip n k)
  (let ([mod (lambda (x) (modulo x n))]
        [len (if (= 0 (modulo n 2)) (- (/ n 2) 1) (/ (- n 1) 2))])
    (mirror-pairs (map (lambda (i) (cons (mod (+ k i 1)) (mod (- k i 1)))) (iota len)))))

(define (cycle-eq? c1 c2)
  (equal? (list->set c1) (list->set c2)))

(define (get-dihedral-symmetries n)
  (if (= 0 (modulo n 2))
      (append (map (lambda (k) (rot n k)) (iota n))
              (map (lambda (k) (vertex-flip n k)) (iota (/ n 2)))
              (map (lambda (k) (face-flip n k)) (iota (/ n 2))))
      (append (map (lambda (k) (rot n k)) (iota n))
              (map (lambda (k) (vertex-flip n k)) (iota n)))))

(define (create-operation-table objects bin-op equality-fxn)
  (map (lambda (y)
         (map (lambda (x) (index-of objects (bin-op y x) equality-fxn)) objects))
       objects))

(define (cayley-table symms)
  (create-operation-table symms compose-cycles cycle-eq?))

(define dihedral-cayley (compose cayley-table get-dihedral-symmetries))

(define d4 (get-dihedral-symmetries 4))

(define my-d4
  (let ([pos-half
         (list (rot 4 0) (rot 4 1) (face-flip 4 0) (vertex-flip 4 0))]
        [negate (lambda (x) (compose-cycles (rot 4 2) x))])
    (append pos-half (map negate pos-half))))

; now want to check that my proposed matrices form d8
; by checking their symmetries
; and seeing that they create the same symmetry table

(define (cycle-to-matrix c n)
  (transpose (perm (map (lambda (x) (apply-cycle c x)) (iota n)))))

(define (cycles-to-matrices-naive cycles n)
  (map (lambda (x) (cycle-to-matrix x n)) cycles))

(define (m-cayley mats) (create-operation-table mats m* m=))

(define (check-matrix-rep symms mats)
  (m= (cayley-table symms)
      (m-cayley mats)))

(define (m-mod-cayley mats k)
  (create-operation-table mats (compose (lambda (m) (m-mod m k)) m*) m=))

(define (check-matrix-rep-mod symms mats k)
  (m= (cayley-table symms) (m-mod-cayley mats k)))

;(let ([symms (get-dihedral-symmetries 3)])
;  (check-matrix-rep symms (cycles-to-matrices-naive symms 3))) ;#t

(define (m-mod-period m n)
  (define (m-mod-period-aux curr-m curr-pow)
    (if (m= curr-m (m-id 2)) curr-pow
        (if (>= curr-pow 100)
            #f
            (m-mod-period-aux (m-mod (m* curr-m m) n) (+ curr-pow 1)))))
  (m-mod-period-aux m 1))

(define (xy-to-rot-mat x y) `((,x ,(- y)) (,y ,x)))

(define (check-rotation x y field-size polygon-size)
  (and (= 1 (modulo (+ (* x x) (* y y)) field-size))
       (= polygon-size (m-mod-period (xy-to-rot-mat x y) field-size))))

; looking for (x y) st x^2+y^2 = 1, and ((x -y) (y x))^k = ((1 0)(0 1))
(define (find-rotation field-size rotation-size)
  (findf (lambda (p) (check-rotation (car p) (cadr p) field-size rotation-size))
         (cartesian-product (iota field-size) (iota field-size))))

(define (accum f x n) (if (= n 1) (list x) (cons x (accum f (f x) (- n 1)))))
(define (rot-mat-to-vertices m field-size polygon-size)
  (accum (lambda (x) (m-mod (m* m x) field-size)) (vec 1 0) polygon-size))

(define 8gon (rot-mat-to-vertices (xy-to-rot-mat 2 2) 7 8))
(define 4gon (rot-mat-to-vertices (xy-to-rot-mat 0 1) 7 4))

(define (col-vecs-to-mat . cols)
  (map (lambda (l) (apply append l)) (apply zip cols)))

(define (find-field-size polygon-size)
  (findf (lambda (field-size) (find-rotation field-size polygon-size)) (iota 100)))

;(map find-field-size (range 2 18)) ; '(2 9 3 19 9 29 7 27 19 43 9 53 29 59 17 67)
; 17-gon lives in Z/67Z!

(define f0 '((1 0) (0 6)))
(define field-size 7)
(define polygon-size 8)
(define r '((2 2) (5 2)))

(define (pt-to-rot pt field-size)
  (m-mod (apply xy-to-rot-mat (apply append pt)) field-size))

(define (points-to-rots pts field-size)
  (map (lambda (pt) (pt-to-rot pt field-size)) pts))

(define (points-to-vertex-flips pts field-size)
  (let ([r (pt-to-rot (list-ref pts 1) field-size)]
        [f `((1 0) (0 ,(- field-size 1)))]
        [how-many (if (= 0 (modulo (length pts) 2)) (/ (length pts) 2) (length pts))]
        [num-pts (length pts)])
    (map (lambda (p)
           (let ([i (car p)] [pt (cdr p)])
             (m-mod
              (m* (m-pow-mod r i field-size)
                  (m* f (m-pow-mod r (- num-pts i) field-size)))
              field-size)
           ))
         (take (enumerate pts) how-many))))

(define (points-to-face-flips pts field-size)
  (let ([r (pt-to-rot (list-ref pts 1) field-size)]
        [f `((1 0) (0 ,(- field-size 1)))]
        [how-many (if (= 0 (modulo (length pts) 2)) (/ (length pts) 2) 0)]
        [num-pts (length pts)])
    (map (lambda (p)
           (let ([i (car p)] [pt (cdr p)])
             (m-mod
              (m* (m-pow-mod r i field-size)
                  (m* f (m-pow-mod r (- num-pts i 1) field-size)))
              field-size)))
         (take (enumerate pts) how-many))))

(define (points-to-matrices pts field-size)
  (append (points-to-rots pts field-size)
          (points-to-vertex-flips pts field-size)
          (points-to-face-flips pts field-size)))

(define (get-dihedral-matrices field-size polygon-size)
  (letrec ([point1 (find-rotation field-size polygon-size)]
           [vertices (rot-mat-to-vertices (apply xy-to-rot-mat point1)
                                          field-size polygon-size)])
    (points-to-matrices vertices field-size)))

(define (check-matrices polygon-size)
  (let ([field-size (find-field-size polygon-size)])
    (m= (dihedral-cayley polygon-size)
        (m-mod-cayley (get-dihedral-matrices field-size polygon-size) field-size))))

;(get-dihedral-matrices 67 17)
;'(((1 0) (0 1))
;  ((7 35) (32 7))
;  ((30 21) (46 30))
;  ((11 58) (9 11))
;  ((57 54) (13 57))
;  ((50 28) (39 50))
;  ((40 3) (64 40))
;  ((41 14) (53 41))
;  ((65 59) (8 65))
;  ((65 8) (59 65))
;  ((41 53) (14 41))
;  ((40 64) (3 40))
;  ((50 39) (28 50))
;  ((57 13) (54 57))
;  ((11 9) (58 11))
;  ((30 46) (21 30))
;  ((7 32) (35 7))
;  ((1 0) (0 66))
;  ((30 46) (46 37))
;  ((57 13) (13 10))
;  ((40 64) (64 27))
;  ((65 8) (8 2))
;  ((41 14) (14 26))
;  ((50 28) (28 17))
;  ((11 58) (58 56))
;  ((7 35) (35 60))
;  ((7 32) (32 60))
;  ((11 9) (9 56))
;  ((50 39) (39 17))
;  ((41 53) (53 26))
;  ((65 59) (59 2))
;  ((40 3) (3 27))
;  ((57 54) (54 10))
;  ((30 21) (21 37)))

; now would like to embed dN in automorphisms on Z/nZ
(define (fxn-rot k n) (lambda (x) (modulo (+ k x) n)))
(define (fxn-vflip k n) (lambda (x) (modulo (- (* 2 k) x) n)))
(define (fxn-fflip k n) (lambda (x) (modulo (- (+ (* 2 k) 1) x) n)))
(define (automorphs n)
  (if (= 0 (modulo n 2))
      (append (map (app fxn-rot _ n) (iota n))
              (map (app fxn-vflip _ n) (iota (/ n 2)))
              (map (app fxn-fflip _ n) (iota (/ n 2))))
      (append (map (app fxn-rot _ n) (iota n))
              (map (app fxn-vflip _ n) (iota n)))))
(define (fxn-eq f1 f2 n) (equal? (map f1 (iota n)) (map f2 (iota n))))
(define (fxn-cayley n)
  (create-operation-table (automorphs n) compose (app fxn-eq _ _ n)))
; (m= (dihedral-cayley 8) (fxn-cayley 8)) ;8

; so what really is sqrt 2?
; it is a spec of fxns that when applied twice, multiplies each element in Z/nZ by 2

(define (map-and-show f l) (map cons l (map f l)))
;(map-and-show (partial * 2) (range 2 5)) ;'((2 . 4) (3 . 6) (4 . 8))

(define (fxn-extention f n)
  ;(fxn-extention (partial * 2) 3) ;'((0 . 0) (1 . 2) (2 . 1))
  (map-and-show (compose (lambda (x) (modulo x n)) f) (iota n)))

(define (list-rotate l) (append (cdr l) (list (car l))))
(define (list-rectify l)
  (if (eq? (car l) (apply min l)) l (list-rectify (list-rotate l))))

(define (cycle-starting-at ext k)
    (define (cycle-starting-at-aux k seen-before)
      (if (< 1000 (length seen-before)) 'timeout
          (let ([next (apply-cycle ext k)])
            (if (member next seen-before)
                seen-before
                (cycle-starting-at-aux next (cons next seen-before))))))
  (list-rectify (reverse (cycle-starting-at-aux k '()))))

(define (extention-to-cycles ext)
  ;(extention-to-cycles (fxn-extention (partial * 2) 3)) ;'((0) (1 2))
  (define (extention-to-cycles-aux cycles uncovered)
    (if (member 'timeout cycles) 'timeout
        (if (set-empty? uncovered) cycles
            (let ([next (cycle-starting-at ext (set-first uncovered))])
              (extention-to-cycles-aux
               (cons next cycles)
               (set-subtract uncovered (list->set next)))))))
  (sort (extention-to-cycles-aux '() (list->set (map car ext)))
        (lambda (x y) (< (car x) (car y)))))

(define (same-residue total-count modulus residue)
  (iota total-count residue modulus))
(define (odds n) (same-residue n 2 1))

(map-and-show
 (lambda (n) (extention-to-cycles (fxn-extention (partial * 2) n)))
 (odds 10))
;'((1 (0))
;  (3 (1 2) (0))
;  (5 (1 3 4 2) (0))
;  (7 (1 4 2) (5 6 3) (0))
;  (9 (1 5 7 8 4 2) (3 6) (0))
;  (11 (1 6 3 7 9 10 5 8 4 2) (0))
;  (13 (1 7 10 5 9 11 12 6 3 8 4 2) (0))
;  (15 (1 8 4 2) (5 10) (9 12 6 3) (13 14 7 11) (0))
;  (17 (1 9 13 15 16 8 4 2) (5 11 14 7 12 6 3 10) (0))
;  (19 (1 10 5 12 6 3 11 15 17 18 9 14 7 13 16 8 4 2) (0)))

; primes give equal length cycles (besides 0)
; what causes the smaller lengths for non prime Z/nZ

(define (get-mult-cycles n k)
  (map (lambda (x) x) (extention-to-cycles (fxn-extention (partial * k) n))))

(map-and-show
 (lambda (n)
   (map (partial get-mult-cycles n) '(2 3 6)))
 (cddr (primes-up-to 20)))

(define (gcd a b) (if (= b 0) a (gcd b (modulo a b))))
(define (coprime? a b) (= 1 (gcd a b)))

(map-and-show (partial coprime? 5) (iota 10 3))
;'((3 . #t)
;  (4 . #t)
;  (5 . #f)
;  (6 . #t)
;  (7 . #t)
;  (8 . #t)
;  (9 . #t)
;  (10 . #f)
;  (11 . #t)
;  (12 . #t))
(define (h- n) (/ (- n 1) 2))
(define (h+ n) (/ (+ n 1) 2))
;(all (map (lambda (n) (coprime? n (/ (+ n 1) 2))) (cdr (odds 100)))) ;#t
(define (q- n) ; assuming prime
  (if (= 1 (modulo n 4)) (/ (- n 1) 4) (/ (- (* 3 n) 1) 4)))
(define (q+ n) ; assuming prime
  (if (= 1 (modulo n 4)) (/ (+ (* 3 n) 1) 4) (/ (+ n 1) 4)))

(define (thirds n)
  (list (/ (- n 1) 3) (/ (+ n 2) 3) (/ (+ (* 2 n) 1) 3) (/ (- (* 2 n) 2) 3)))

(define (binary-to-num l)
  (define (binary-to-num-aux l)
    (if (null? l) 0 (+ (car l) (* 2 (binary-to-num-aux (cdr l))))))
  (binary-to-num-aux (reverse l)))

(define nums
  (map (compose binary-to-num (app make-list _ 1)) (iota 10 2)))
(map (lambda (x) (length (cadr (get-mult-cycles x 2)))) nums)
;'(2 3 4 5 6 7 8 9 10 11)
; conjecture correct!
