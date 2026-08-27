; obligation: HMAC (RFC 2104 / FIPS 198-1) — the inner and outer padded keys
;   differ by a key-INDEPENDENT constant:  (k ^ ipad) ^ (k ^ opad)  =  ipad ^ opad
; proved by asserting the NEGATION and expecting unsat.
(set-logic QF_BV)
(declare-const k    (_ BitVec 32))
(declare-const ipad (_ BitVec 32))
(declare-const opad (_ BitVec 32))
(assert (not (= (bvxor (bvxor k ipad) (bvxor k opad))
                (bvxor ipad opad))))
(check-sat)
