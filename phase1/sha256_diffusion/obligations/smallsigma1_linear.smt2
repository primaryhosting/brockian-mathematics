; obligation: SHA-256 small sigma_1 is GF(2)-linear: sigma1(x^y)=sigma1(x)^sigma1(y)
;   sigma1(v) = ROTR^17 v ^ ROTR^19 v ^ SHR^10 v.  unsat of the negation = proved.
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(define-fun f ((v (_ BitVec 32))) (_ BitVec 32)
  (bvxor (bvxor ((_ rotate_right 17) v) ((_ rotate_right 19) v)) (bvlshr v #x0000000a)))
(assert (not (= (f (bvxor x y)) (bvxor (f x) (f y)))))
(check-sat)
