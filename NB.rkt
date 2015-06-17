#lang racket

(require rackunit)
(require redex)

(define true #t)
(define false #f)

;; Boolean Syntax
(define-language B-untyped-syntax
  (Term Bool
        (if Term then Term else Term))
  (Bool true
        false))

;; Contexts for evaluating if-else
(define-extended-language B-untyped
  B-untyped-syntax
  (C (if C then Term else Term)
     hole))

;; Semantics of if-else
(define B-untyped-red
  (reduction-relation
   B-untyped
   (--> (in-hole C (if true then Term else _))
        (in-hole C Term))
   (--> (in-hole C (if false then _ else Term))
        (in-hole C Term))))

;; Test reduction of if-else
(define if-else-test1
  (term (if false then false else true)))  ;; t
(define if-else-test2
  (term (if true then false else true)))   ;; f
(define if-else-test3
  (term (if ,if-else-test1
            then ,if-else-test2
            else true)))

(define (bool-test-suite reduction)
  (test-->> reduction if-else-test1 (term true))
  (test-->> reduction if-else-test3 (term false)))

(bool-test-suite B-untyped-red)

;; Add syntax for Numerals
(define-extended-language NB-untyped-syntax
  B-untyped
  (Term ....
        Num
        (pred Term)
        (iszero Term))
  (Val Bool
       Num)
  (Num 0
       (succ Num)))

;; Add contexts to evaluate the terms associated with numerals
(define-extended-language NB-untyped
  NB-untyped-syntax
  (C ....
     (succ C)
     (pred C)
     (iszero C)))

;; Semantics of numerals
(define NB-untyped-red
  (extend-reduction-relation
   B-untyped-red
   NB-untyped
   (--> (in-hole C (pred 0))
        (in-hole C 0))
   (--> (in-hole C (pred (succ Num)))
        (in-hole C Num))
   (--> (in-hole C (iszero 0))
        (in-hole C true))
   (--> (in-hole C (iszero (succ _)))
        (in-hole C false))))

;; Helpers for constructing numerals
(define (num-add num n)
  (if (< n 0)
      (num-add (term (pred ,num)) (+ n 1))
      (if (> n 0)
          (num-add (term (succ ,num)) (- n 1))
          num)))
(define (numeral n) (num-add 0 n))


;; Tests for new numeral semantics
(define (num-test-suite reduction)
  (test-->> reduction
            (term (pred 0))
            (term 0))
  (test-->> reduction
            (term (pred (succ 0)))
            (term 0))
  (test-->> reduction
            (term (iszero 0))
            (term true))
  (test-->> reduction
            (term (pred 0))
            (term 0))
  (test-->> reduction
            (term (pred (succ (succ 0))))
            (term (succ 0)))
  (test-->> reduction
            (term (iszero ,(num-add (num-add (numeral 3) 2) -5)))
            (term true))
  (test-->> reduction
            (term (iszero ,(num-add (numeral 3) -4)))
            (term true)))

(define bad-type-1
  (term (if false then false else 0)))
(define stuck-1
  (term (if (numeral 9) then true else false)))
(define stuck-2
  (term (succ true)))

(define (num-bool-test-suite reduction)
  (bool-test-suite reduction)
  (num-test-suite reduction)
  ;; Test the new combination of booleans and numerals
  (test-->> reduction
            (term (if (iszero 0) then true else false))
            (term true))
  (test-->> reduction
            (term (if true then ,(num-add (numeral 1) -1) else (numeral 1)))
            (term 0))
  (test-->> reduction
            (term (if false then 0 else ,(numeral 1)))
            (term (succ 0)))
  ;; Also we have some stuck terms now
  (test-->> reduction stuck-1 stuck-1)
  (test-->> reduction stuck-2 stuck-2))

(num-bool-test-suite NB-untyped-red)

(test-->> NB-untyped-red bad-type-1 0) ;; This works in untyped version

;; Introduce types and a Typechecker

(define-extended-language NB-typed
  NB-untyped
  (Type 'b
        'nat))

(define-judgment-form
  NB-typed
  #:mode (NB-types I O)
  #:contract (NB-types Term Type)
  
  [------------------
   (NB-types true 'b)]
  [-------------------
   (NB-types false 'b)]
  
  [(NB-types Term_1 'b)
   (NB-types Term_2 Type)
   (NB-types Term_3 Type)
   ---------------------------------------------------
   (NB-types (if Term_1 then Term_2 else Term_3) Type)]
  
  [-----------------
   (NB-types 0 'nat)]
  
  [(NB-types Term_1 'nat)
   -----------------------------
   (NB-types (succ Term_1) 'nat)]
  [(NB-types Term_1 'nat)
   -----------------------------
   (NB-types (pred Term_1) 'nat)]
  
  [(NB-types Term_1 'nat)
   -----------------------------
   (NB-types (iszero Term_1) 'b)])

(define (NB-types? e)
  (not (null? (judgment-holds (NB-types ,e Type) Type))))
                                        
(define (test-NB-typing-rules)
  (check-true (NB-types? (term true)))
  (check-true (NB-types? (term false)))
  (check-true (NB-types? (term (if false then false else false))))
  (check-true (NB-types? (term (if false then 0 else ,(numeral 1)))))
  (check-false (NB-types? bad-type-1))
  (check-true (NB-types? if-else-test3)))

;; Check Progress with our new typechecker

(define-syntax-rule (progress-rule lang lang-red typechecker values)
  (lambda (e)
    (or (not (typechecker e))
        (or (redex-match? lang values e)
            (not (null? (apply-reduction-relation lang-red e)))))))

(define NB-progress-holds?
  (progress-rule NB-untyped NB-untyped-red NB-types? Val))

(redex-check NB-untyped Term (NB-progress-holds? (term Term)))

(test-NB-typing-rules)