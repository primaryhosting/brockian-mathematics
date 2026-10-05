; obligation: SHA-256 small sigma_0 is GF(2)-linear: sigma0(x^y)=sigma0(x)^sigma0(y)
;   sigma0(v) = ROTR^7 v ^ ROTR^18 v ^ SHR^3 v.  unsat of the negation = proved.
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(define-fun f ((v (_ BitVec 32))) (_ BitVec 32)
  (bvxor (bvxor ((_ rotate_right 7) v) ((_ rotate_right 18) v)) (bvlshr v #x00000003)))
(assert (not (= (f (bvxor x y)) (bvxor (f x) (f y)))))
(check-sat)
