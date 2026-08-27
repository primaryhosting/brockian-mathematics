; obligation: SHA-256 small sigma_0 is INJECTIVE (bijection): sigma0(x)=sigma0(y) -> x=y.
; negation asserts a collision with x != y; unsat = injective.  A harder SAT instance
; than linearity; discharged by the SMT engines (Z3, cvc5). Kernel-algebra proof: not attempted.
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(define-fun f ((v (_ BitVec 32))) (_ BitVec 32)
  (bvxor (bvxor ((_ rotate_right 7) v) ((_ rotate_right 18) v)) (bvlshr v #x00000003)))
(assert (and (= (f x) (f y)) (not (= x y))))
(check-sat)
