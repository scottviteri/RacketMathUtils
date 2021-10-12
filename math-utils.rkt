(require srfi/1)
(require racket/list)
(require racket/set)

(define m '((1 2) (3 4)))
(define (mat-row m j) (list-ref m j))

(define (mat-col m i) (map car m))
(define (mat-ind m j i) (list-ref (mat-row m j) i))
(define (curry f) (lambda (x) (apply f x)))
(define sum (curry +))
(define mul (curry *))

(define (inner-prod v1 v2) (sum (map mul (zip v1 v2))))
(define transpose (curry zip))

(define (m* m1 m2)
  (let ([m2t (transpose m2)])
    (map (lambda (left-vec)
           (map (lambda (right-vec) (inner-prod left-vec right-vec)) m2t))
         m1)))

(define (vec . l) (map list l))

(define (v+ v1 v2) (map sum (zip v1 v2)))
(define (m+ m1 m2)
  (map (curry v+) (zip m1 m2)))

(define (deep-apply f m)
  (map (lambda (row) (map f row)) m))

(define (s* k m)
  (deep-apply (lambda (x) (* k x)) m))

(define (impulse i len) (map (lambda (x) (if (= x i) 1 0)) (iota len)))

(define (id dim)
  (map (lambda (i) (impulse i dim)) (iota dim)))

(define v= equal?)
(define (all l) (fold (lambda (x y) (and x y)) #t l))

(define (m= m1 m2)
  (and (eq? (length m1) (length m2))
       (all (map (curry v=) (zip m1 m2)))))

(define (square m) (m* m m))

(define (m-pow m n)
  (define (odd? n) (= 1 (modulo n 2)))
  (if (= n 0) (id (length m))
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
  (let ([target (id dim)]
        [ms (all-matrices dim top)])
    (filter (condition m target) ms)))

;(test square 3)
(define (count-zeros m)
  (sum (map (lambda (row) (count (lambda (x) (= x 0)) row)) m)))

(define (perm l)
  ;input must be set= (iota (length l))
  (map (lambda (i) (impulse i (length l))) l))

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

(define (sqrts5 n)
  (filter (lambda (x) (= 5 (modulo (* x x) n))) (iota n)))

(define (quats n)
  (filter (lambda (x) (= 1 (modulo (* x x x x) n))) (iota n)))

(define (enumerate l) (zip (iota (length l)) l))
(define (count-sqrts n) (enumerate (map (compose length sqrts) (iota n))))
(define (is-prime n)
  (all (map (lambda (d) (not (= 0 (modulo n d))))
            (iota (- n 2) 2))))
(define (primes-up-to n)
  (filter is-prime (iota (- n 1) 2)))

(define (pow1 x n)
  (if (= x 0) 0
      (let ([l (filter (lambda (k) (= 1 (modulo (expt x k) n)))
                       (iota (- n 1) 1))])
        (if (null? l) n (car l)))))

(define (periodicities n)
  (map (lambda (x) (pow1 x n)) (iota n)))

(define (check m) (and (= (caar m) (caadr m)) (= (cadar m) (- 5 (cadadr m)))))

(define (m-pows m k mod) (map (lambda (x) (m-pow-mod m x mod)) (iota k)))

(define (m-per m mod)
  (define (m-per-aux m orig cnt)
    (if (> cnt 100) 10
      (let ([meq (m= (id 2) m)])
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
  (letrec ([d1 (list->set (map car f))]
           [d2 (list->set (map car g))]
           [domain (set-union d1 d2)])
    (normalize
     (set->list (set-map domain (lambda (x) (cons x (apply-cycle f (apply-cycle g x)))))))))

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

; now want to create matrices for a given dihedral algebra
;  first just create matrices for D8, precomputed

(define finite-field-size 7)
(define num-polygon-sides 8)
(define sqrt-half 2)

(define r `((,sqrt-half ,(- finite-field-size sqrt-half)) (,sqrt-half ,sqrt-half)))
(define rots (m-pows r num-polygon-sides finite-field-size))
(define vflips
  (map (lambda (m) (m-mod m finite-field-size))
       '(((1 0) (0 -1))
         ((0 1) (1 0))
         ((-1 0) (0 1))
         ((0 -1) (-1 0)))))
(define fflips
  (let ([x sqrt-half]
        [negx (- finite-field-size sqrt-half)])
    `(((,x ,x) (,x ,negx))
      ((,negx ,x) (,x ,x))
      ((,negx ,negx) (,negx ,x))
      ((,x ,negx) (,negx ,negx)))))
(define mats (append rots vflips fflips))
; (check-matrix-rep-mod (get-dihedral-symmetries 8) mats 7) #t
; now want to do more automatically

; could make this faster via squares
(define (m-mod-period m n)
  (define (m-mod-period-aux curr-m curr-pow)
    (if (m= curr-m (id 2)) curr-pow
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
