; obligation: constant-time select, mask=0 selects b
(set-logic QF_BV)
(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))
(assert (not (= (bvor (bvand #x00000000 a) (bvand (bvnot #x00000000) b)) b)))
(check-sat)
