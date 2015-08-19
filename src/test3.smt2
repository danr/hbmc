(declare-sort A 0)
(declare-fun f (A A) A)
(declare-fun g (A) A)
(declare-fun h (A) A)

; don't want to duplicate the work of h here


(define-funs-rec
  ((test ((b Bool) (x A)) A))
  ((ite b (let ((y (h x))) (f (g y) y))
          (g x))))

; this does not currently work.
;
; one way to do this is to make y magical and pull it like this:
;
; let *y = if b then Just (h x) else Nothing
; in  if b then f (g y) y else g x
;
; can we always make the initial lets magical and pull them as far
; as possible before starting?

(check-sat)
