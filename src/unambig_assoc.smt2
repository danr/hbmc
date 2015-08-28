(declare-datatypes (a)
  ((list (nil) (cons (head a) (tail (list a))))))
(declare-datatypes () ((Tok (C) (D) (X) (Y) (Plus) (Mul))))
(declare-datatypes ()
  ((E (+2 (+_0 E) (+_1 E)) (*2 (*_0 E) (*_1 E)) (EX) (EY))))
(define-fun-rec
  assoc
    ((x E)) E
    (match x
      (case default x)
      (case (+2 y c)
        (match y
          (case default (+2 (assoc y) (assoc c)))
          (case (+2 a b) (assoc (+2 a (+2 b c))))))
      (case (*2 a2 b2) (*2 (assoc a2) (assoc b2)))))
(define-fun-rec
  (par (a)
    (append
       ((x (list a)) (y (list a))) (list a)
       (match x
         (case nil y)
         (case (cons z xs) (cons z (append xs y)))))))
(define-funs-rec
  ((linTerm ((x E)) (list Tok))
   (lin ((x E)) (list Tok)))
  ((match x
     (case default (lin x))
     (case (*2 a b)
       (append (append (cons C (as nil (list Tok))) (lin (+2 a b)))
         (cons D (as nil (list Tok))))))
   (match x
     (case (+2 a b)
       (append (append (linTerm a) (cons Plus (as nil (list Tok))))
         (linTerm b)))
     (case (*2 a3 b2)
       (append (append (lin a3) (cons Mul (as nil (list Tok)))) (lin b2)))
     (case EX (cons X (as nil (list Tok))))
     (case EY (cons Y (as nil (list Tok)))))))
(assert-not
  (forall ((u E) (v E))
    (=> (= (lin u) (lin v)) (= (assoc u) (assoc v)))))
(check-sat)
