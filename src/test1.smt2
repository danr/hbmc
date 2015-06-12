(declare-sort A 0)
(declare-fun f (A) A)
(declare-fun g (A) A)
(declare-fun h (A) A)

; best is to lift out g twice

(define-funs-rec
  ((test ((b Bool) (x A)) A))
  ((ite b (f (g (g (h x))))
          (h (g (g (f x)))))))

(check-sat)
