;; Jason Hemann and Dan Friedman
;; microKanren, final implementation from paper

;; Modified by Adam Solove to support tracing

(define (var c) (vector c))
(define (var? x) (vector? x))
(define (var=? x1 x2) (= (vector-ref x1 0) (vector-ref x2 0)))

(define (walk u s)
  (let ((pr (and (var? u) (assp (lambda (v) (var=? u v)) s))))
    (if pr (walk (cdr pr) s) u)))

(define (ext-s x v s) `((,x . ,v) . ,s))

(define (== u v)
  (lambda (s/t)
    (let ((s (unify u v (car s/t))))
      (if s (unit `(,s . ,(cdr s/t))) mzero))))

(define (unit s/t) (cons s/t mzero))
(define mzero '())

(define (unify u v s)
  (let ((u (walk u s)) (v (walk v s)))
    (cond
      ((and (var? u) (var? v) (var=? u v)) s)
      ((var? u) (ext-s u v s))
      ((var? v) (ext-s v u s))
      ((and (pair? u) (pair? v))
       (let ((s (unify (car u) (car v) s)))
         (and s (unify (cdr u) (cdr v) s))))
      (else (and (eqv? u v) s)))))

(define (call/fresh f)
  (lambda (s/t)
    (let* ((t (cdr s/t))
           (c (car t)))
      ((f (var c)) `(,(car s/t) . ,(cons (+ c 1) (cdr t)))))))

(define (disj g1 g2) (lambda (s/t) (mplus (g1 s/t) (g2 s/t))))
(define (conj g1 g2) (lambda (s/t) (bind (g1 s/t) g2)))

(define (mplus $1 $2)
  (cond
    ((null? $1) $2)
    ((procedure? $1) (lambda () (mplus $2 ($1))))
    (else (cons (car $1) (mplus (cdr $1) $2)))))

(define (bind $ g)
  (cond
    ((null? $) mzero)
    ((procedure? $) (lambda () (bind ($) g)))
    (else (mplus (g (car $)) (bind (cdr $) g)))))

;;;; How to make a simple miniKanren (substitution only)

(define-syntax Zzz
  (syntax-rules ()
    ((_ g) (lambda (s/t) (lambda () (g s/t))))))

(define-syntax conj+
  (syntax-rules ()
    ((_ g) (Zzz g))
    ((_ g0 g ...) (conj (Zzz g0) (conj+ g ...)))))

(define-syntax disj+
  (syntax-rules ()
    ((_ g) (Zzz g))
    ((_ g0 g ...) (disj (Zzz g0) (disj+ g ...)))))

(define-syntax fresh
  (syntax-rules ()
    ((_ () g0 g ...) (conj+ g0 g ...))
    ((_ (x0 x ...) g0 g ...)
     (call/fresh
      (lambda (x0)
        (fresh (x ...) g0 g ...))))))

(define-syntax conde
  (syntax-rules ()
    ((_ (g0 g ...) ...) (disj+ (conj+ g0 g ...) ...))))

(define-syntax run
  (syntax-rules ()
    ((_ n (x ...) g0 g ...)
     (map reify-1st (take n (call/goal (fresh (x ...) g0 g ...)))))))

(define-syntax run*
  (syntax-rules ()
    ((_ (x ...) g0 g ...)
     (map reify-1st (take-all (call/goal (fresh (x ...) g0 g ...)))))))

(define empty-state '(() . (0)))

(define (call/goal g) (g empty-state))

(define (pull $)
  (if (procedure? $) (pull ($)) $))

(define (take-all $)
  (let (($ (pull $)))
    (if (null? $) '() (cons (car $) (take-all (cdr $))))))

(define (take n $)
  (if (zero? n) '()
    (let (($ (pull $)))
      (if (null? $) '() (cons (car $) (take (- n 1) (cdr $)))))))

(define (reify-1st s/t)
  (let ((v (walk* (var 0) (car s/t))))
    (walk* v (reify-s v '()))))

(define (walk* v s)
  (let ((v (walk v s)))
    (cond
      ((var? v) v)
      ((pair? v) (cons (walk* (car v) s)
                   (walk* (cdr v) s)))
      (else  v))))

(define (reify-s v s)
  (let ((v (walk v s)))
    (cond
      ((var? v)
       (let  ((n (reify-name (length s))))
         (cons `(,v . ,n) s)))
      ((pair? v) (reify-s (cdr v) (reify-s (car v) s)))
      (else s))))

(define (reify-name n)
  (string->symbol
    (string-append "_" "." (number->string n))))

(define (fresh/nf n f)
  (letrec
    ((app-f/v*
       (lambda (n v*)
         (cond
           ((zero? n) (apply f (reverse v*)))
           (else (call/fresh
                   (lambda (x)
                     (app-f/v* (- n 1) (cons x v*)))))))))
     (app-f/v* n '())))

;;; Trace

(define (trace g)
  (lambda (s/t)
    (trace-stream s/t (g s/t))))

(define (trace-stream s/t r)
  (cond
    ((null? r) r)
    ((procedure? r)
      (lambda () (trace-stream s/t (r))))
    (else
      (let* ((s/t2 (car r))
             (thunk (cdr r))
             (s/t3 (cons (car s/t2)
                         (cons (car (cdr s/t2))
                               (cons (cons (car s/t) (car s/t2)) (cdr (cdr s/t2)))))))
        (cons s/t3 thunk)))))

;;; Test programs

(define-syntax test-check
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (printf "Testing ~s\n" title)
       (let* ((expected expected-result)
              (produced tested-expression))
         (or (equal? expected produced)
             (errorf 'test-check
               "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
               'tested-expression expected produced)))))))

(define (appendo l s out)
  (conde
    ((== '() l) (== s out))
    ((fresh (a d res)
       (trace (== `(,a . ,d) l))
       (trace (== `(,a . ,res) out))
       (trace (appendo d s res))))))

(test-check 'run*
  (run* (q) (fresh (x y) (== `(,x ,y) q) (appendo x y '(1 2 3 4 5))))
  '((() (1 2 3 4 5))
    ((1) (2 3 4 5))
    ((1 2) (3 4 5))
    ((1 2 3) (4 5))
    ((1 2 3 4) (5))
    ((1 2 3 4 5) ())))

(test-check 'run*2
  (run* (q x y) (== `(,x ,y) q) (appendo x y '(1 2 3 4 5)))
  '((() (1 2 3 4 5))
    ((1) (2 3 4 5))
    ((1 2) (3 4 5))
    ((1 2 3) (4 5))
    ((1 2 3 4) (5))
    ((1 2 3 4 5) ())))
  
(test-check 'rember*o
  (letrec
      ((rember*o (lambda (tr o)
                   (conde
                     ((== '() tr) (== '() o))
                     ((fresh (a d)
                        (== `(,a . ,d) tr)
                        (conde
                          ((fresh (aa da)
                             (== `(,aa . ,da) a)
                             (fresh (a^ d^)
                               (rember*o a a^)
                               (rember*o d d^)
                               (== `(,a^ . ,d^) o))))
                          ((== a 8) (rember*o d o))
                          ((fresh (d^)
                             (rember*o d d^)
                             (== `(,a . ,d^) o))))))))))
       (run 8 (q) (rember*o q '(1 2 8 3 4 5))))
    '((1 2 8 3 4 5)
      (1 2 8 3 4 5 8)
      (1 2 8 3 4 8 5)
      (1 2 8 3 8 4 5)
      (1 2 8 8 3 4 5)
      (1 2 8 8 3 4 5)
      (1 8 2 8 3 4 5)
      (8 1 2 8 3 4 5)))

(test-check 'rember*o
  (letrec
      ((rember*o (lambda (tr o)
                   (conde
                     ((== '() tr) (== '() o))
                     ((fresh (a d)
                        (== `(,a . ,d) tr)
                        (conde
                          ((fresh (aa da)
                             (== `(,aa . ,da) a)
                             (fresh (a^ d^)
                               (== `(,a^ . ,d^) o)
                               (rember*o d d^)
                               (rember*o a a^))))
                          ((== a 8) (rember*o d o))
                          ((fresh (d^)
                             (== `(,a . ,d^) o)
                             (rember*o d d^))))))))))
       (run 9 (q) (rember*o q '(1 (2 8 3 4) 5))))
    '((1 (2 8 3 4) 5)
      (1 (2 8 3 4) 5 8)
      (1 (2 8 3 4) 5 8 8)
      (1 (2 8 3 4) 8 5)
      (1 8 (2 8 3 4) 5)
      (8 1 (2 8 3 4) 5)
      (1 (2 8 3 4) 5 8 8 8)
      (1 (2 8 3 4) 5 8 8 8 8)
      (1 (2 8 3 4) 5 8 8 8 8 8)))

;;; Example debug output

(define-syntax debug
  (syntax-rules ()
    ((_ n (x ...) g0 g ...)
     (map reify-1st (take n (call/goal (fresh (x ...) g0 g ...)))))))

(define appendo-output
  (take 8
    (call/goal
      (fresh (q)
        (fresh (x y)
          (== `(,x ,y) q)
          (appendo x y '(1 2)))))))

(define (debug-answer answer)
  (display "Found answer ")
  (display (reify-1st answer))
  (display " by passing through ")
  (map (lambda (frame)
    (let ((out (cdr frame)))
      (display "\n\t")
      (display (reify-1st frame))
      (display " => ")
      (display (reify-1st (cons out '())))))
    (cddr answer))
  (display "\n"))

(map debug-answer appendo-output)