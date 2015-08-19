
(declare-datatypes () ((AB (A) (B))))
(declare-datatypes () ((CD (C) (D))))

(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun g (U) CD)
(declare-fun h (U) U)

(define-fun-rec
  test_match ((s AB) (t CD) (x U) (y U)) CD
  (match s
    (case A (g x))
    (case B
      (match (g y)
        (case C C)
        (case D D)))))

(check-sat)
