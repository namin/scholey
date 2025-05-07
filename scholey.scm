;;; scholey.scm — multi-stage programming from Scheme to SMT

;;;; SMT data and tagging

(define (make-smt name)
  (cons 'smt name))

(define (smt? x)
  (and (pair? x) (eq? (car x) 'smt)))

(define (smt-name x)
  (cdr x))

(define (smt-repr x)
  (cond ((smt? x) (symbol->string (smt-name x)))
        ((number? x) (number->string x))
        ((symbol? x) (symbol->string x))
        (else (error "Unsupported SMT value" x))))

;;;; Global constraint state

(define *smt-constraints* '())
(define *smt-decls* '())

(define (emit-smt s)
  (set! *smt-constraints* (cons s *smt-constraints*)))

(define (declare-smt name)
  (let ((decl (string-append "(declare-const " (symbol->string name) " Real)")))
    (set! *smt-decls* (cons decl *smt-decls*))))

(define fresh-smt-counter 0)

(define (fresh-smt-name)
  (let* ((n fresh-smt-counter)
         (name (string->symbol (string-append "v" (number->string n)))))
    (set! fresh-smt-counter (+ fresh-smt-counter 1))
    name))

;;;; Binary op and comparison overloads

(define (smt-binop op x y)
  (let* ((rx (smt-repr x))
         (ry (smt-repr y))
         (rname (fresh-smt-name)))
    (declare-smt rname)
    (emit-smt (string-append
               "(assert (= " (symbol->string rname) " (" op " " rx " " ry ")))"))
    (make-smt rname)))

(define (smt-cmpop op x y)
  (let ((rx (smt-repr x))
        (ry (smt-repr y)))
    (emit-smt (string-append
               "(assert (" op " " rx " " ry "))"))))

;;;; Generic operators and overloads

(define original-+ (eval '+ (scheme-environment)))
(define original-- (eval '- (scheme-environment)))
(define original-* (eval '* (scheme-environment)))
(define original-< (eval '< (scheme-environment)))
(define original-= (eval '= (scheme-environment)))

(define (generic+ x y) (if (or (smt? x) (smt? y)) (smt-binop "+" x y) (original-+ x y)))
(define (generic- x y) (if (or (smt? x) (smt? y)) (smt-binop "-" x y) (original-- x y)))
(define (generic* x y) (if (or (smt? x) (smt? y)) (smt-binop "*" x y) (original-* x y)))
(define (generic< x y) (if (or (smt? x) (smt? y)) (smt-cmpop "<" x y) (original-< x y)))
(define (generic= x y) (if (or (smt? x) (smt? y)) (smt-cmpop "=" x y) (original-= x y)))

(define + generic+)
(define - generic-)
(define * generic*)
(define < generic<)
(define = generic=)

;;;; SMTLIB2 serialization

(define (string-join strs sep)
  (if (null? strs)
      ""
      (let loop ((rest (cdr strs)) (acc (car strs)))
        (if (null? rest)
            acc
            (loop (cdr rest) (string-append acc sep (car rest)))))))

(define (generate-smtlib2)
  (string-append
   "(set-logic QF_NRA)\n"
   (string-join (reverse *smt-decls*) "\n")
   "\n"
   (string-join (reverse *smt-constraints*) "\n")
   "\n(check-sat)\n(get-model)\n"))

(define (write-to-file filename content)
  (call-with-output-file filename
    (lambda (port) (display content port))
    'replace))

;;;; Z3 process interaction

(define (read-line port)
  (let loop ((chars '()))
    (let ((c (read-char port)))
      (cond
        ((eof-object? c)
         (if (null? chars) c (list->string (reverse chars))))
        ((char=? c #\newline)
         (list->string (reverse chars)))
        (else
         (loop (cons c chars)))))))

(define (run-z3-on file)
  (let ((cmd (string-append "timeout 5 z3 " file " > z3.out")))
    (if (= (system cmd) 0)
        'ok
        'z3-failed)))

(define (read-model-sexp filename)
  (call-with-input-file filename
    (lambda (port)
      ;; Skip "sat"
      (let ((first (read port)))
        (if (eq? first 'unsat)
            'unsat
            (read port))))))

(define (filter-map f lst)
  (cond
    ((null? lst) '())
    (else
     (let ((val (f (car lst))))
       (if val
           (cons val (filter-map f (cdr lst)))
           (filter-map f (cdr lst)))))))

(define (string-prefix? prefix s)
  (let ((n (string-length prefix)))
    (and (<= n (string-length s))
         (string=? prefix (substring s 0 n)))))

(define (parse-model-sexp sexp)
  (define (is-user-var? name)
    ;; Filter out auto-generated vars like v0, v1, etc.
    (not (string-prefix? "v" (symbol->string name))))

  (define (extract-binding def)
    ;; Each definition looks like: (define-fun x () Real 5.0)
    (let ((name (cadr def))
          (value (list-ref def 4)))
      (if (is-user-var? name)
          (cons name value)
          #f)))

  (filter-map extract-binding sexp))

;;;; Main entry: build and solve a constraint

(define (synthesize-inputs)
  (set! *smt-constraints* '())
  (set! *smt-decls* '())

  (let ((x (make-smt 'x))
        (y (make-smt 'y)))
    (declare-smt 'x)
    (declare-smt 'y)

    ;; Constraints: x + 2y < 10 and x = y + 3
    (< (+ x (* 2 y)) 10)
    (= x (+ y 3))

    (let* ((smtlib (generate-smtlib2))
           (tmpfile "constraints.smt2"))
      (write-to-file tmpfile smtlib)
      (run-z3-on tmpfile))))

(define (solve-and-parse)
  (let ((lines (synthesize-inputs)))
    (let ((sexp (read-model-sexp "z3.out")))
      (if (eq? sexp 'unsat)
          'unsat
          (parse-model-sexp sexp)))))

;;;; Example run
(display (solve-and-parse)) (newline)
