(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun g (U) U)
(declare-fun h (U) U)

(declare-datatypes () ((Tri (A) (B) (C))))

(define-fun-rec
  testA ((t Tri) (x U)) U
  (match t
     (case A (f (g (h x))))
     (case B (g (f (h x))))
     (case C (h (f (g x))))))

(define-fun-rec
  testB ((t Tri) (x U)) U
  (match t
     (case A (f (g (h x))))
     (case B (g (h (f x))))
     (case C (h (f (g x))))))

(check-sat)

