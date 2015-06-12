(declare-sort A 0)
(declare-fun f (A A) A)
(declare-fun g (A) A)
(declare-datatypes () ((Tri (X) (Y) (Z))))

; best:
; first lift out g a & g b
; then lift out arguments to f

; if you start with lifting out f, then g cannot be lifted

(define-funs-rec
  ((test ((t Tri) (a A) (b A) (c A)) A))
  ((match t
     (case X (f (g a)))
     (case Y (g b))
     (case Z (f c)))))

(check-sat)
