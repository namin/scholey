;;; scholey.scm — staged execution from Scheme to SMT
;;; A minimal implementation of the Holey technique in Scheme.

;;;; 1. SMT representation

;; Symbolic values: (smt . "expr-string")
;; Symbolic booleans: (smt-bool . "expr-string")

(define (make-smt expr) (cons 'smt expr))
(define (smt? x) (and (pair? x) (eq? (car x) 'smt)))
(define (smt-expr x) (cdr x))

(define (make-smt-bool expr) (cons 'smt-bool expr))
(define (smt-bool? x) (and (pair? x) (eq? (car x) 'smt-bool)))
(define (smt-bool-expr x) (cdr x))

(define (smt-repr x)
  (cond ((smt? x) (smt-expr x))
        ((smt-bool? x) (smt-bool-expr x))
        ((integer? x) (number->string x))
        ((number? x)
         (let ((s (number->string (exact->inexact x))))
           (if (and (not (string-contains "." s))
                    (not (string-contains "e" s)))
               (string-append s ".0")
               s)))
        ((boolean? x) (if x "true" "false"))
        (else (error 'smt-repr "unsupported value" x))))

(define (string-contains sub str)
  (let ((sublen (string-length sub))
        (strlen (string-length str)))
    (let loop ((i 0))
      (cond ((> (+ i sublen) strlen) #f)
            ((string=? sub (substring str i (+ i sublen))) #t)
            (else (loop (+ i 1)))))))

;;;; 2. Global state

(define *constraints* '())
(define *decls* '())
(define *decl-names* '())
(define *path-conditions* '())
(define *branch-queue* '())
(define *current-choices* '())
(define *choice-index* 0)

;;;; 3. Operator overloading

(define orig+ (eval '+ (scheme-environment)))
(define orig- (eval '- (scheme-environment)))
(define orig* (eval '* (scheme-environment)))
(define orig< (eval '< (scheme-environment)))
(define orig> (eval '> (scheme-environment)))
(define orig<= (eval '<= (scheme-environment)))
(define orig>= (eval '>= (scheme-environment)))
(define orig= (eval '= (scheme-environment)))

(define (symbolic? x) (or (smt? x) (smt-bool? x)))

(define (smt-binop op x y)
  (make-smt (string-append "(" op " " (smt-repr x) " " (smt-repr y) ")")))

(define (smt-cmpop op x y)
  (make-smt-bool (string-append "(" op " " (smt-repr x) " " (smt-repr y) ")")))

(define (generic-arith op orig)
  (lambda args
    (if (exists symbolic? args)
        (fold-left (lambda (a b) (smt-binop op a b))
                   (car args) (cdr args))
        (apply orig args))))

(define (generic-cmp op orig)
  (lambda (x y)
    (if (or (symbolic? x) (symbolic? y))
        (smt-cmpop op x y)
        (orig x y))))

(define + (generic-arith "+" orig+))
(define - (generic-arith "-" orig-))
(define * (generic-arith "*" orig*))
(define < (generic-cmp "<" orig<))
(define > (generic-cmp ">" orig>))
(define <= (generic-cmp "<=" orig<=))
(define >= (generic-cmp ">=" orig>=))
(define = (generic-cmp "=" orig=))

(define (smt-mod x y) (smt-binop "mod" x y))
(define (smt-div x y) (smt-binop "div" x y))
(define (smt-not x)
  (if (smt-bool? x)
      (make-smt-bool (string-append "(not " (smt-bool-expr x) ")"))
      (not x)))
(define (smt-and . args)
  (make-smt-bool
   (string-append "(and " (string-join (map smt-repr args) " ") ")")))
(define (smt-or . args)
  (make-smt-bool
   (string-append "(or " (string-join (map smt-repr args) " ") ")")))

;;;; 4. Branch exploration

(define (branch! condition-expr)
  ;; condition-expr is a string like "(> x 5)"
  (if (orig< *choice-index* (length *current-choices*))
      ;; Replaying a recorded choice
      (let ((choice (list-ref *current-choices* *choice-index*)))
        (set! *choice-index* (orig+ *choice-index* 1))
        (set! *path-conditions*
              (cons (if choice
                        condition-expr
                        (string-append "(not " condition-expr ")"))
                    *path-conditions*))
        choice)
      ;; New choice: take #t, queue #f
      (begin
        (set! *branch-queue*
              (cons (append *current-choices* (list #f))
                    *branch-queue*))
        (set! *current-choices*
              (append *current-choices* (list #t)))
        (set! *choice-index* (orig+ *choice-index* 1))
        (set! *path-conditions*
              (cons condition-expr *path-conditions*))
        #t)))

(define-syntax sif
  (syntax-rules ()
    ((_ test then else)
     (let ((t test))
       (if (smt-bool? t)
           (if (branch! (smt-bool-expr t)) then else)
           (if t then else))))))

;;;; 5. Constraint emission

(define (assert! c)
  (let ((expr (cond ((smt-bool? c) (smt-bool-expr c))
                    ((boolean? c) (if c "true" "false"))
                    (else (error 'assert! "not a constraint" c)))))
    (if (null? *path-conditions*)
        (set! *constraints*
              (cons (string-append "(assert " expr ")")
                    *constraints*))
        (set! *constraints*
              (cons (string-append
                     "(assert (=> "
                     (if (null? (cdr *path-conditions*))
                         (car *path-conditions*)
                         (string-append "(and "
                                        (string-join (reverse *path-conditions*) " ")
                                        ")"))
                     " " expr "))")
                    *constraints*)))))

;;;; 6. SMT-LIB generation and Z3 invocation

(define (string-join strs sep)
  (if (null? strs) ""
      (let loop ((rest (cdr strs)) (acc (car strs)))
        (if (null? rest) acc
            (loop (cdr rest) (string-append acc sep (car rest)))))))

(define (declare-smt! name . type)
  (let ((t (if (null? type) "Int" (symbol->string (car type)))))
    (set! *decl-names* (cons name *decl-names*))
    (set! *decls*
          (cons (string-append "(declare-const " (symbol->string name) " " t ")")
                *decls*))))

(define (generate-smtlib2)
  (let ((logic (if (exists (lambda (d) (string-contains "Real" d)) *decls*)
                   "QF_NRA" "QF_LIA")))
    (string-append
     "(set-logic " logic ")\n"
     (string-join (reverse *decls*) "\n") "\n"
     (string-join (reverse *constraints*) "\n") "\n"
     "(check-sat)\n(get-model)\n")))

(define (write-to-file filename content)
  (call-with-output-file filename
    (lambda (port) (display content port))
    'replace))

(define (run-z3 file)
  (let ((cmd (string-append "z3 -T:5 " file " > z3.out 2>&1")))
    (system cmd)))

(define (read-model-sexp filename)
  (call-with-input-file filename
    (lambda (port)
      (let ((first (read port)))
        (if (eq? first 'sat)
            (read port)
            first)))))

(define (parse-model sexp)
  (if (or (eq? sexp 'unsat) (eq? sexp 'unknown) (eof-object? sexp))
      sexp
      (filter (lambda (x) x)
              (map (lambda (def)
                     (let ((name (cadr def))
                           (value (list-ref def 4)))
                       (if (memq name *decl-names*)
                           (cons name value)
                           #f)))
                   sexp))))

;;;; 7. Top-level solve

(define (solve thunk)
  (set! *constraints* '())
  (set! *branch-queue* (list '()))

  (let loop ()
    (cond
     ((null? *branch-queue*)
      ;; All paths explored — invoke solver
      (let ((smtlib (generate-smtlib2)))
        (write-to-file "constraints.smt2" smtlib)
        (run-z3 "constraints.smt2")
        (let ((model (read-model-sexp "z3.out")))
          (parse-model model))))
     (else
      ;; Explore next path
      (set! *current-choices* (car *branch-queue*))
      (set! *branch-queue* (cdr *branch-queue*))
      (set! *choice-index* 0)
      (set! *path-conditions* '())
      (let ((result (thunk)))
        (cond ((smt-bool? result) (assert! result))
              ((boolean? result) (assert! result))))
      (loop)))))

;;;; Examples

;; Example 1: Simple arithmetic
;; Find x, y such that x + 2y < 10 and x = y + 3
(define (example-arithmetic)
  (let ((x (make-smt "x"))
        (y (make-smt "y")))
    (set! *decls* '())
    (set! *decl-names* '())
    (declare-smt! 'x)
    (declare-smt! 'y)
    (solve (lambda ()
             (assert! (< (+ x (* 2 y)) 10))
             (assert! (= x (+ y 3)))))))

;; Example 2: Branching
;; Find x such that: if x > 5 then x < 10 else x = 0
(define (example-branching)
  (let ((x (make-smt "x")))
    (set! *decls* '())
    (set! *decl-names* '())
    (declare-smt! 'x)
    (solve (lambda ()
             (sif (> x 5)
                  (assert! (< x 10))
                  (assert! (= x 0)))))))

;; Example 3: Monkey and Coconut puzzle
;; Five sailors, each takes 1 coconut for monkey, divides rest by 5, hides 1 pile.
;; Morning: remaining divides by 5 (plus 1 for monkey).
(define (example-monkey)
  (let ((n (make-smt "n")))
    (set! *decls* '())
    (set! *decl-names* '())
    (declare-smt! 'n)
    (solve (lambda ()
             (let loop ((i 0) (n n))
               (if (orig< i 5)
                   (begin
                     (assert! (= (smt-mod n 5) 1))
                     (loop (orig+ i 1) (- n (+ 1 (smt-div (- n 1) 5)))))
                   (begin
                     (assert! (> n 0))
                     (assert! (= (smt-mod n 5) 1)))))))))

;; Run examples
(display "=== Example 1: Arithmetic ===") (newline)
(display (example-arithmetic)) (newline)
(newline)
(display "=== Example 2: Branching ===") (newline)
(display (example-branching)) (newline)
(newline)
(display "=== Example 3: Monkey and Coconut ===") (newline)
(display (example-monkey)) (newline)
