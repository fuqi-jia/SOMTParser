; Authored for SOMTParser, not vendored.
;
; The shape is CHC-COMP's. Every benchmark in that competition declares its
; predicates as QUOTED symbols and applies them unquoted:
;
;     (declare-fun |inv| ( Int Int ) Bool)
;     ...
;     (inv B A)
;
; SMT-LIB 2.6 section 3.1 says those are the same symbol -- enclosing a simple
; symbol in vertical bars does not produce a new one -- and this engine treated
; them as two, so the whole CHC-COMP corpus read as
; `Unknown or unexpected symbol "inv"`. Fixed 2026-08-15; see
; test/regression/test_quoted_symbol_identity.cpp.
;
; The competition files themselves are not vendored because their
; redistribution terms were not established. This file reproduces the construct
; and a linear Horn problem around it, and nothing else.
(set-logic HORN)

(declare-fun |inv| ( Int Int ) Bool)

; initiation: the loop starts at (0, 5000)
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and (= A 5000) (= B 0))
      (inv B A))))

; consecution: one step of the loop preserves the invariant
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) )
    (=>
      (and (|inv| B A) (< B A) (= C (+ B 1)) (= D (- A 1)))
      (inv C D))))

; the query: the invariant must rule out B > A
(assert
  (forall ( (A Int) (B Int) )
    (=>
      (and (inv B A) (> B A))
      false)))

(check-sat)
