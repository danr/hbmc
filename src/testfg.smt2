(declare-sort A 0)
(declare-fun f (A) A)
(declare-fun g (A) A)

(define-fun-rec
  test
    ((b Bool) (u A))
    A
    (ite b (f (g u))
           (g (f u))))

(check-sat)

