(declare-datatypes (a)
  ((list (nil) (cons (head a) (tail (list a))))))
(declare-datatypes () ((T (A) (B) (C))))
(declare-datatypes (a)
  ((R (Nil)
     (Eps) (Atom (Atom_0 a)) (+2 (+_0 (R a)) (+_1 (R a)))
     (& (&_0 (R a)) (&_1 (R a))) (>2 (>_0 (R a)) (>_1 (R a)))
     (Star (Star_0 (R a))))))
(define-fun
  eqT
    ((x T) (y T)) Bool
    (match x
      (case A
        (match y
          (case default false)
          (case A true)))
      (case B
        (match y
          (case default false)
          (case B true)))
      (case C
        (match y
          (case default false)
          (case C true)))))
(define-fun-rec
  eps
    ((x (R T))) Bool
    (match x
      (case default false)
      (case Eps true)
      (case (+2 p q) (or (eps p) (eps q)))
      (case (& p2 q2) (and (eps p2) (eps q2)))
      (case (>2 p3 q3) (and (eps p3) (eps q3)))
      (case (Star y) true)))
(define-fun-rec
  step
    ((x (R T)) (y T)) (R T)
    (match x
      (case default (as Nil (R T)))
      (case (Atom b) (ite (eqT b y) (as Eps (R T)) (as Nil (R T))))
      (case (+2 p q) (+2 (step p y) (step q y)))
      (case (& p2 q2) (& (step p2 y) (step q2 y)))
      (case (>2 p3 q3)
        (ite
          (eps p3) (+2 (>2 (step p3 y) q3) (step q3 y))
          (+2 (>2 (step p3 y) q3) (as Nil (R T)))))
      (case (Star p4) (>2 (step p4 y) x))))
(define-fun-rec
  rec
    ((x (R T)) (y (list T))) Bool
    (match y
      (case nil (eps x))
      (case (cons z xs) (rec (step x z) xs))))
(assert-not
  (forall ((p (R T)) (q (R T)) (a T) (b T))
    (=> (rec (Star (+2 p q)) (cons a (cons b (as nil (list T)))))
      (rec (+2 (Star p) (Star q)) (cons a (cons b (as nil (list T))))))))
(check-sat)
