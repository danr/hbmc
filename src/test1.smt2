(declare-sort A 0)
(declare-fun f (A) A)
(declare-fun g (A) A)
(declare-fun h (A) A)

(declare-datatypes () ((bool (True) (False))))

; best is to lift out g twice

(define-funs-rec
  ((test ((b Bool) (u A)) A))
  ((ite b (f (g (g (h u))))
          (h (g (g (f u)))))))


(check-sat)
