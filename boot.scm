;; For debugging only

;(define d +)
;(define one 1)
;(define two 2)

;(+ one two)

;(define f
;  (lambda (n)
;    (display n "\n")
;    (+ n 1)))

(define e
  (lambda (n a b)
    ((if n + *) a b)))

(define fib
  (lambda (n)
    (if (> n 2)
    (+ (fib (- n 1)) (fib (- n 2)))
    n)))
