; obligation: SHA-256 Sigma0 (BIG sigma_0) is GF(2)-linear: Sigma0(x^y)=Sigma0(x)^Sigma0(y)
;   Sigma0(v) = ROTR^2 v ^ ROTR^13 v ^ ROTR^22 v.  unsat of the negation = proved.
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(define-fun f ((v (_ BitVec 32))) (_ BitVec 32)
  (bvxor (bvxor ((_ rotate_right 2) v) ((_ rotate_right 13) v)) ((_ rotate_right 22) v)))
(assert (not (= (f (bvxor x y)) (bvxor (f x) (f y)))))
(check-sat)
