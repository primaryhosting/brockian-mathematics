; obligation: SHA-256 compression — the round adds are modulo 2^32; folding
;   T1 = h + S1(e) + Ch + Kt + Wt  is well-defined because + is associative:
;   (a + b) + c = a + (b + c)  over BitVec 32 (wrapping add).
; proved by asserting the NEGATION and expecting unsat.
(set-logic QF_BV)
(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))
(declare-const c (_ BitVec 32))
(assert (not (= (bvadd (bvadd a b) c) (bvadd a (bvadd b c)))))
(check-sat)
