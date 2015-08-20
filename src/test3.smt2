(declare-sort A 0)

(declare-fun f (A A) A)
(declare-fun g (A) A)
(declare-fun h (A) A)

(declare-datatypes () ((AA (C (cproj A)) (D (dproj A)))))

; don't want to duplicate the work of h here

(define-fun-rec
  test ((u AA)) A
  (match u
     (case (C a) (let ((b (h a))) (f (g b) b)))
     (case (D a) (g a))))

(define-fun-rec
  test2 ((u AA)) A
  (match u
     (case (C a1) (let ((b1 (h a1))) (f (g b1) b1)))
     (case (D a2) (let ((b2 (h a2))) (f (g b2) b2)))))

(define-fun-rec
  test3 ((u AA)) A
  (match u
     (case (C a1) (let ((b1 (h a1))) (f b1 b1)))
     (case (D a2) (let ((b2 (h a2))) (f b2 b2)))))

(check-sat)
