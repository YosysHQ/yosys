#lang rosette/safe

(require rosette/lib/smt)

;; Define a function to load SMT-LIB from a file
(define (load-smt-file filepath)
  (define smt-content (file->string filepath))
  (smt->rosette smt-content))

;; Path to your SMT-LIB file
(define smt-file-path "and.smt2")

;; Load the SMT-LIB content
(define smt-formula (load-smt-file smt-file-path))

;; Example: Asserting a simple query
(define (test-smt-formula)
  (define result (verify smt-formula))
  (printf "Result: ~a\n" result))

;; Run the test
(test-smt-formula)