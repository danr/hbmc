(declare-datatypes (a)
  ((list (nil) (cons (head a) (tail (list a))))))
(declare-datatypes () ((Ty (arr (arr_0 Ty) (arr_1 Ty)) (A) (B) (C))))
(declare-datatypes () ((Nat (S (p Nat)) (Z))))
(declare-datatypes (a) ((Maybe (Nothing) (Just (Just_0 a)))))
(declare-datatypes ()
  ((Expr (App (App_0 Expr) (App_1 Expr) (App_2 Ty))
     (Lam (Lam_0 Expr)) (Var (Var_0 Nat)))))
(define-fun-rec
  (par (a)
    (index
       ((x (list a)) (y Nat)) (Maybe a)
       (match x
         (case nil (as Nothing (Maybe a)))
         (case (cons z xs)
           (match y
             (case (S n) (index xs n))
             (case Z (Just z))))))))
(define-fun-rec
  eqType
    ((x Ty) (y Ty)) Bool
    (match x
      (case (arr a z)
        (match y
          (case default false)
          (case (arr b y2) (and (eqType a b) (eqType z y2)))))
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
  tc2
    ((x (list Ty)) (y Expr) (z Ty)) Bool
    (match y
      (case (App f x2 tx) (and (tc2 x x2 tx) (tc2 x f (arr tx z))))
      (case (Lam e)
        (match z
          (case default false)
          (case (arr tx2 t) (tc2 (cons tx2 x) e t))))
      (case (Var x3)
        (match (index x x3)
          (case Nothing false)
          (case (Just tx3) (eqType tx3 z))))))
(assert-not
  (forall ((e Expr))
    (not
      (tc2 (as nil (list Ty)) e (arr (arr B C) (arr (arr A B) (arr A C)))))))
(check-sat)
