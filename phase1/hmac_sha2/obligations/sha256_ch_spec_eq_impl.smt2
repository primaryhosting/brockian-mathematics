; obligation: SHA-256 Ch — the FIPS 180-4 "choice" selector.
;   spec (XOR) form  (x & y) ^ (~x & z)  =  impl (OR) form  (x & y) | (~x & z)
; proved by asserting the NEGATION and expecting unsat.
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(declare-const z (_ BitVec 32))
(assert (not (= (bvxor (bvand x y) (bvand (bvnot x) z))
                (bvor  (bvand x y) (bvand (bvnot x) z)))))
(check-sat)
