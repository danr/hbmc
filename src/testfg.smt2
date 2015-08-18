(declare-sort A 0)
(declare-fun f (A) A)
(declare-fun g (A) A)

(define-fun-rec
  test
    ((b Bool) (x A))
    A
    (ite b (f (g x))
           (g (f x))))

(check-sat)

