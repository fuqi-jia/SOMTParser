; CHC-COMP permits only declare-fun symbols returning Bool. This is a valid
; SMT-LIB declaration but not a CHC-COMP fun_decl.
(set-logic HORN)
(declare-fun x () Int)
(assert (> x 0))
(check-sat)
