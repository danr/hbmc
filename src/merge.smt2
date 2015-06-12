(declare-datatypes (a)
  ((list (nil) (cons (head a) (tail (list a))))))
(declare-datatypes (a b) ((Pair (Pair2 (first a) (second b)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(define-funs-rec
  ((par (a)
     (splitAt ((x Nat) (y (list a))) (Pair (list a) (list a)))))
  ((match x
     (case Z (Pair2 (as nil (list a)) y))
     (case (S n)
       (match y
         (case nil (Pair2 (as nil (list a)) (as nil (list a))))
         (case (cons z xs)
           (match (splitAt n xs)
             (case (Pair2 l r) (Pair2 (cons z l) r)))))))))
(define-funs-rec ((n1 () Nat)) ((S Z)))
(define-funs-rec ((n2 () Nat)) ((S n1)))
(define-funs-rec ((n3 () Nat)) ((S n2)))
(define-funs-rec ((n4 () Nat)) ((S n3)))
(define-funs-rec ((n5 () Nat)) ((S n4)))
(define-funs-rec
  ((par (a) (length ((x (list a))) Nat)))
  ((match x
     (case nil Z)
     (case (cons y xs) (S (length xs))))))
(define-funs-rec
  ((le ((x Nat) (y Nat)) Bool))
  ((match x
     (case Z true)
     (case (S z)
       (match y
         (case Z false)
         (case (S y2) (le z y2)))))))
(define-funs-rec
  ((merge ((x (list Nat)) (y (list Nat))) (list Nat)))
  ((match x
     (case nil
       (match y
         (case nil (as nil (list Nat)))
         (case (cons z x2) y)))
     (case (cons x3 xs)
       (match y
         (case nil x)
         (case (cons y2 ys)
           (ite
             (le x3 y2) (cons x3 (merge xs y)) (cons y2 (merge x ys)))))))))
(define-funs-rec
  ((half ((x Nat)) Nat))
  ((match x
     (case Z Z)
     (case (S y)
       (match y
         (case Z Z)
         (case (S n) (S (half n))))))))
(define-funs-rec
  ((msort ((x (list Nat))) (list Nat)))
  ((match x
     (case nil (as nil (list Nat)))
     (case (cons y z)
       (match z
         (case nil (cons y (as nil (list Nat))))
         (case (cons x2 x3)
           (match (splitAt (half (length x)) x)
             (case (Pair2 ys zs) (merge (msort ys) (msort zs))))))))))
(assert-not
  (forall ((xs (list Nat)) (ys (list Nat)))
    (=> (= (msort xs) (msort ys))
      (=> (not (le (length xs) n5)) (= xs ys)))))
(check-sat)
