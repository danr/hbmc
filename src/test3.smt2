(declare-sort A 0)
(declare-fun f (A A) A)
(declare-fun g (A) A)
(declare-fun h (A) A)

; don't want to duplicate the work of h here

(define-funs-rec
  ((test ((b Bool) (x A)) A))
  ((ite b (let ((y (h x))) (f (g y) y))
          (g x))))

(check-sat)
