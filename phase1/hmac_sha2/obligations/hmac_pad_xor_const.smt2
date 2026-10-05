; obligation: HMAC pad constants (ipad = 0x36, opad = 0x5c per byte) XOR to the
;   fixed constant 0x6a per byte:  0x36363636 ^ 0x5c5c5c5c = 0x6a6a6a6a
; proved by asserting the NEGATION and expecting unsat.
(set-logic QF_BV)
(assert (not (= (bvxor #x36363636 #x5c5c5c5c) #x6a6a6a6a)))
(check-sat)
