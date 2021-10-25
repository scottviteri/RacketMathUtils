#lang racket

(require srfi/1)
(require (only-in racket/list remove-duplicates cartesian-product index-of))
(require racket/set)
(require (only-in relation partial app curry andf onto))
(require racket/match)
(require racket/stream)
(require plot)

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

(define (det2by2 m)
  (match m [(list (list a b) (list c d)) (- (* a d) (* b c))]))

(define (invert2by2 m)
  (match m [(list (list a b) (list c d))
            (s* (/ 1 (det2by2 m))
                (list (list d (- b)) (list (- c) a)))]))

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

(define (make-mat dim l) (split l dim))
; (define m (make-mat 2 '(1 2 3 4)))

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

(define (map-mod n)
  (lambda (f l) (map (compose (app modulo _ n) f) l)))

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
(define (get-coprimes a) (filter (partial coprime? a) (range 2 a)))

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
;(map (lambda (x) (length (cadr (get-mult-cycles x 2)))) nums)
;'(2 3 4 5 6 7 8 9 10 11)
; conjecture correct!
(define (find-index f l) (car (findf (compose f cadr) (enumerate l))))

(define (get-frac-mod numer denom field-size)
  (find-index (partial = numer)
              ((map-mod field-size) (partial * denom) (iota field-size))))

; has to do with coprime functions
; want 1/denom mod field-size
; 1/denom = (k*field-size + 1)/denom where k*field-size = -1 mod denom
; so need k = -1/field-size mod denom
; k = (k2*denom - 1)/field-size where k2*denom = 1 mod field-size
; so need k2 = 1/denom mod field-size <- cycle
; so this is not a method to compute
;  just says that (1/denom mod field-size) and (-1/field-size mod denom)
;  have the same information

(define (check-flippy-property denom field-size)
  (let ([k2 (get-frac-mod 1 denom field-size)]
        [k (get-frac-mod (- denom 1) field-size denom)])
    (and
     (eq? k (/ (- (* k2 denom) 1) field-size))
     (eq? k2 (/ (+ (* k field-size) 1) denom)))))

;(let ([field-size 10])
;  (all (map (app check-flippy-property _ field-size)
;            (get-coprimes field-size)))) ;#t
; so instead of finding  1/16 mod 9, can find -1/9 mod 16

; what is the deal with euclidian domains, and is Z/nZ one?
; can make an ordering on it based on cycle structure of *k
;  namely use denominators as an ordering

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; thinking about sqrt(2) again
;  how to quickly compute it in bitvectors?
;  how to quickly compute in general when it has an exact soln?

; simple frac or newton's method w/ x^2 - 2

(define (simple-cont-frac coeffs)
  ;(simple-cont-frac '(1 2 2 2 2)) ; 41/29
  ; but this does not work on a stream
  (define (simple-cont-frac-aux coeffs result)
    ;(display (if (not (= 0 (caadr result))) (/ (caar result) (caadr result)) result)) (newline)
    (if (null? coeffs) result
        (let ([m (make-mat 2 (list (car coeffs) 1 1 0))])
          (simple-cont-frac-aux (cdr coeffs) (m* m result)))))
  (match (simple-cont-frac-aux (reverse coeffs) (vec 1 0))
    [(list (list n) (list d)) (/ n d)]))

(define (frac-to-cont-frac frac)
  ; (equal? (/ 113 17) (simple-cont-frac (frac-to-cont-frac (/ 113 17)))) ;#t
  ;(display frac) (newline)
  (if (or (< frac 1) (integer? frac)) (list frac)
      (cons (floor frac) (frac-to-cont-frac (/ 1 (- frac (floor frac)))))))

(define (simple-frac-compute-in-order next-coeff) ; yeah this is totally wrong
  (define (f-aux next-coeff s-1 s-2 s-3)
    (if (not s-1) (let ([result (vec next-coeff 1)])
                    (cons result (app f-aux _ result #f #f)))
    (if (not s-2) (letrec ([prev-coeff (caar s-1)]
                           [result (vec (+ 1 (* prev-coeff next-coeff)) next-coeff)])
                    (cons result (app f-aux _ result s-1 #f)))
    (if (not s-3)
        (match-let ([(list (list a) _) s-2]
                    [(list _ (list b)) s-1]
                    [c next-coeff])
          (let ([result (vec (+ (* a b c) a c) (+ 1 (* b c)))])
            (cons result (app f-aux _ result s-1 s-2))))
    (match-let ([(list (list n-1) (list d-1)) s-1]
                [(list (list n-2) (list d-2)) s-2]
                [(list (list n-3) (list d-3)) s-3])
      (letrec ([n (+ (* next-coeff n-1) (/ (* n-2 d-1) d-2))]
               [d (+ d-3 (* next-coeff d-1))]
               [m (make-mat 2 (list next-coeff (/ n-1 d) (/ d-2 n) next-coeff))]
               [result (m* m s-1)])
        (cons result (app f-aux _ result s-1 s-2))))))))
  (f-aux next-coeff #f #f #f))

(define (apply-stream f coeffs)
  (if (null? coeffs) '()
      (match-let ([(cons c new-f) (f (car coeffs))])
        (cons c (apply-stream new-f (cdr coeffs))))))

(define (get-m coeff) (make-mat 2 (list 0 1 1 (- coeff))))
(define tsra (function (lambda (x) (/ 1 (- x 1))) -1 3))

(define (stat-diff f)
  (lambda (x) (let ([dx .001]) (/ (- (f (+ x dx)) (f x)) dx))))

(define test-poly '((0 . 2) (3 . 4))) ; 2 + 4x^3
(define dec (app - _ 1))
(define inc (app + _ 1))

(define (diff poly)
  ; (diff p) ; 12x^2
  (filter-map (match-lambda ((cons power coeff)
                             (if (= 0 power) #f (cons (dec power) (* power coeff)))))
              poly))

(define (decrement-power poly)
  (filter-map (match-lambda ((cons power coeff)
                             (if (= 0 power) #f (cons (dec power) coeff))))
              poly))

(define (increment-power poly)
  (filter-map (match-lambda ((cons power coeff)
                             (if (= 0 power) #f (cons (inc power) coeff))))
              poly))

(define (k-increment-power poly k)
  (filter-map (match-lambda ((cons power coeff)
                             (if (= 0 power) #f (cons (+ k power) coeff))))
              poly))


(define (apply-poly poly x)
  ;(apply-poly p 1) ;6
  (if (null? poly) 0
        (let ([constant (assoc 0 poly)]
              [lowered-poly (decrement-power poly)])
          (+ (if constant (cdr constant) 0)
             (* x (apply-poly lowered-poly x))))))

(define (repeat f k)
  (lambda (x) (if (= k 1) (f x) (f ((repeat f (dec k)) x)))))

(define (k-diff poly k) ((repeat diff k) poly))
(define (k-stat-diff f k) ((repeat stat-diff k) f))
;((k-stat-diff (app expt _ 2) 1) 3) ;6.000999999999479
;((k-stat-diff (app expt _ 2) 2) 3) ;2.000000000279556

; compare convergents to newton's to 2nd order deriv
(define (close x y)
  (< (magnitude (- x y)) .001))

(define (find-fixed-pt f start [verbose #f] [fuel #f])
  ;(close (+ 1 (sqrt 2)) (find-fixed-pt (lambda (x) (+ 2 (/ 1 x))) 1)) ;#t
  ;(close (- 1 (sqrt 2)) (find-fixed-pt (lambda (x) (/ 1 (- x 2))) 1)) ;#t
  (define (find-fixed-pt-aux prev fuel)
    (if (and (integer? fuel) (= 0 fuel)) prev
        (begin (if verbose (begin (display prev) (newline)) 1)
               (let ([next (f prev)])
                 (if (close next prev) next
                     (find-fixed-pt-aux next (if fuel (dec fuel) fuel)))))))
  (exact->inexact (find-fixed-pt-aux start fuel)))

(define (is-stable-pt? f x)
  ;(is-stable-pt? (lambda (x) (+ 2 (/ 1 x))) (+ 1 (sqrt 2))) ;t
  (let ([df (stat-diff f)])
    (and (close x (f x)) (< (abs (df x)) 1))))

(define (solve-quad poly)
  ; require max degree = 2
  ; (solve-quad '((2 . 1) (0 . 1))) ;'(0+1i 0-1i)
  (let ([a (if (assoc 2 poly) (cdr (assoc 2 poly)) 0)]
        [b (if (assoc 1 poly) (cdr (assoc 1 poly)) 0)]
        [c (if (assoc 0 poly) (cdr (assoc 0 poly)) 0)])
    (list
     (/ (+ (- b) (sqrt (- (expt b 2) (* 4 a c)))) (* 2 a))
     (/ (- (- b) (sqrt (- (expt b 2) (* 4 a c)))) (* 2 a)))))

; can do symbolically or numerically
(define (newtons-method-stat f start)
  ; (close (sqrt 2) (newtons-method-stat (lambda (x) (- (* x x) 2)) 1)) ;#t
  (let ([df (stat-diff f)])
    (find-fixed-pt (lambda (x) (- x (/ (f x) (df x)))) start)))

(define (newtons-method poly start)
  ; (close (sqrt 2) (newtons-method '((2 . 1) (0 . -2)) 1)) ;#t
  (let ([df (diff poly)])
    (find-fixed-pt (lambda (x) (- x (/ (apply-poly poly x) (apply-poly df x)))) start)))

; newton's sqrt 2
(define (cont-frac-sqrt2 x) (/ (+ 2 x) (+ 1 x)))

; (close (sqrt 2) (find-fixed-pt cont-frac-sqrt2 1)) ;t
(define (cont-frac-neg-sqrt2 x) (+ -1 (/ 1 (+ -1 x))))

(define (newton-sqrt2 x) (/ (+ (* x x) 2) (* 2 x)))
(plot (list (function (lambda (x) x) -2 2)
            (function cont-frac-sqrt2 -2 2)
            (function cont-frac-neg-sqrt2 -2 2)
            (function newton-sqrt2 -2 2))
      #:y-min -2 #:y-max 2)

(define (scalar*poly s p)
  (map (match-lambda ((cons pow coeff) (cons pow (* s coeff)))) p))
(define (get-keys alst) (list->set (map car alst)))

(define (poly+ p1 p2)
  (set->list (set-map (set-union (get-keys p1) (get-keys p2))
                      (lambda (k) (cons k (let ([m1 (assoc k p1)] [m2 (assoc k p2)])
                                            (if (not m1) (cdr m2)
                                            (if (not m2) (cdr m1)
                                            (+ (cdr m1) (cdr m2))))))))))

(define (poly* p1 p2)
  (fold poly+ '()
        (map (match-lambda
               ((cons pow coeff) (k-increment-power (scalar*poly coeff p2) pow)))
             p1)))


(define (factorial n) (if (= n 0) 1 (* n (factorial (- n 1)))))
(define (choose n k) (/ (factorial n) (* (factorial k) (factorial (- n k)))))
(define (binomial-poly c n)
  (map (lambda (k) (cons k (* (choose n k) (expt (- c) (- n k)))))
       (range (inc n))))

(define (poly-shift poly c)
  (fold poly+ '()
        (map (match-lambda ((cons power coeff)
                            (scalar*poly coeff (binomial-poly c power))))
             poly)))

(define (poly-lift n) (list (cons 0 n)))

; in newton's both positive and negative roots are stable
; in cont-frac, only positive is stable, though can be rewritten to make neg stable
(define (quadratic-newtons-method poly pt)
  (letrec ([dp (diff poly)]
           [d2p (diff dp)]
           [fx (apply-poly poly pt)])
    (letrec ([taylor (list (cons 0 fx)
                           (cons 1 (apply-poly dp pt))
                           (cons 2 (/ (apply-poly d2p pt) 2)))]
             [shifted-taylor (poly-shift taylor pt)]
             [new-zeros (solve-quad shifted-taylor)])
      (car new-zeros))))

(define sqrt2-poly '((2 . 1) (0 . -2)))
(define cubrt2-poly '((3 . 1) (0 . -2)))
(define crazy-poly '((7 . 1) (5 . -5) (4 . 5/2) (3 . 1) (2 . -2) (0 . 9)))
;(close (find-fixed-pt (partial newtons-method crazy-poly) 2)
;       (find-fixed-pt (partial quadratic-newtons-method crazy-poly) 2))

(define (quadratic-minimizing-newtons-method poly pt)
  ;(find-fixed-pt (partial quadratic-minimizing-newtons-method '((4 . 1) (0 . -2))) 9 #t 20)
  ; currently not converging
  (letrec ([dp (diff poly)]
           [d2p (diff dp)]
           [fx (apply-poly poly pt)])
    (letrec ([taylor (list (cons 0 fx)
                           (cons 1 (apply-poly dp pt))
                           (cons 2 (/ (apply-poly d2p pt) 2)))]
             [shifted-taylor (poly-shift taylor pt)])
      (match shifted-taylor
        ((list (cons 2 a) (cons 1 b) (cons 0 c) ...)
         (exact->inexact (- (/ b (* 2 a)))))))))
