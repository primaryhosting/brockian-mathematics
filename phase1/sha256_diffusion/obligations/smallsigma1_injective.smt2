; obligation: SHA-256 small sigma_1 is INJECTIVE (bijection): sigma1(x)=sigma1(y) -> x=y.
; negation asserts a collision with x != y; unsat = injective.
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(define-fun f ((v (_ BitVec 32))) (_ BitVec 32)
  (bvxor (bvxor ((_ rotate_right 17) v) ((_ rotate_right 19) v)) (bvlshr v #x0000000a)))
(assert (and (= (f x) (f y)) (not (= x y))))
(check-sat)
