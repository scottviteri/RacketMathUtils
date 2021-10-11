(require srfi/1)
(require racket/list)

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

(define (sqrt-half n)
  (let ([half (div 1 2 n)])
    (if half ())))

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

;(define (rot n) (lambda (x) (modulo (+ x 1) n)))
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

;(define (repeat f n)
;  (define (repeat-aux n x)
;    (if (= n 0) x (repeat-aux (- n 1) (f x))))
;  (lambda (x) (repeat-aux n x)))

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
;(define (cycle-apply-eq? n)
;  (lambda (c1 c2) (all (map (lambda (x) (= (apply-cycle c1 x) (apply-cycle c1 x)))
;                            (iota n)))))

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

(define my-d4
  (let ([pos-half
         (list (rot 4 0) (rot 4 1) (face-flip 4 0) (vertex-flip 4 0))]
        [negate (lambda (x) (compose-cycles (rot 4 2) x))])
    (append pos-half (map negate pos-half))))


; now want to check that my proposed matrices form d8
; by checking their symmetries
; and seeing that they create the same symmetry table
; but the symmetry table would look different with a diff order of symmetries
;  maybe can get cycle structure form

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
  (m= (cayley-table symms)
      (m-mod-cayley mats k)))


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
