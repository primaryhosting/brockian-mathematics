; obligation: SHA-256 Maj — the FIPS 180-4 "majority" selector.
;   spec (XOR) form  (x&y) ^ (x&z) ^ (y&z)  =  impl (OR) form  (x&y) | (x&z) | (y&z)
; proved by asserting the NEGATION and expecting unsat.
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(declare-const z (_ BitVec 32))
(assert (not (= (bvxor (bvxor (bvand x y) (bvand x z)) (bvand y z))
                (bvor  (bvor  (bvand x y) (bvand x z)) (bvand y z)))))
(check-sat)
