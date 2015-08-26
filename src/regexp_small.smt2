; Regular expressions using Brzozowski derivatives (see the step function)
; The plus and seq functions are smart constructors.
(declare-datatypes (a)
  ((list (nil) (cons (head a) (tail (list a))))))
(declare-datatypes () ((A (X) (Y))))
(declare-datatypes ()
  ((R (Nil)
     (Eps)
     (Seq (Seq_0 R) (Seq_1 R)) (Star (Star_0 R)))))
(define-funs-rec ((seq ((x R) (y R)) R)) ((match x (case default (Seq x y)) (case Nil Nil))))
(define-funs-rec ((epsR ((x R)) R)) ((ite (is-Eps x) Eps Nil)))
(define-funs-rec
  ((step ((x R) (y A)) R))
  ((match x
     (case default Nil)
     (case (Seq p2 q2)
       (Seq q2 (seq (epsR p2) q2)))
     (case (Star p3) (seq p3 x)))))
(check-sat)
