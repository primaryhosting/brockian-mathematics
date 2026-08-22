; obligation: stream-cipher / one-time-pad involution  (m ^ k) ^ k = m
; proved by asserting the NEGATION and expecting unsat.
(set-logic QF_BV)
(declare-const m (_ BitVec 32))
(declare-const k (_ BitVec 32))
(assert (not (= (bvxor (bvxor m k) k) m)))
(check-sat)
