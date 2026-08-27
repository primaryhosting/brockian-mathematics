; obligation: SHA-256 Sigma1 (BIG sigma_1) is GF(2)-linear: Sigma1(x^y)=Sigma1(x)^Sigma1(y)
;   Sigma1(v) = ROTR^6 v ^ ROTR^11 v ^ ROTR^25 v.  unsat of the negation = proved.
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(define-fun f ((v (_ BitVec 32))) (_ BitVec 32)
  (bvxor (bvxor ((_ rotate_right 6) v) ((_ rotate_right 11) v)) ((_ rotate_right 25) v)))
(assert (not (= (f (bvxor x y)) (bvxor (f x) (f y)))))
(check-sat)
