(declare-sort A 0)
(declare-fun f (A A) A)
(declare-fun g (A) A)
(declare-datatypes () ((Tri (X) (Y) (Z))))

; best: memoize g and lift out f's arguments f x and g x.

(define-funs-rec
  ((test ((b Tri) (x A)) A))
  ((match b
     (case X (f (f x)))
     (case Y (f (g x)))
     (case Z (g (g x))))))

(check-sat)
