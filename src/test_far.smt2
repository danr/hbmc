(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun g (U) U)
(declare-fun h (U) U)

(declare-datatypes () ((AB (A) (B))))
(declare-datatypes () ((CD (C) (D))))

(define-fun-rec
  test_near ((s AB) (t CD) (x U) (y U)) U
  (match s
    (case A (g x))
    (case B
      (match t
        (case C (f x))
        (case D (g y))))))

(define-fun-rec
  test_far ((s AB) (t CD) (x U) (y U)) U
  (match s
    (case A (f x))
    (case B
      (match t
        (case C (g x))
        (case D (g y))))))

(check-sat)
