(declare-sort A 0)
(declare-fun f (A A) A)
(declare-fun g (A) A)
(declare-fun h (A) A)

; here, we should just lift out the arguments to f
(define-funs-rec
  ((test ((b Bool) (x A)) A))
  ((ite b (f (g x) (h x))
          (f (h x) (g x)))))

(check-sat)
