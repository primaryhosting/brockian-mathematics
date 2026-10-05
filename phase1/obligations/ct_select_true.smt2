; obligation: constant-time select, mask=all-ones selects a
(set-logic QF_BV)
(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))
(assert (not (= (bvor (bvand (bvnot #x00000000) a) (bvand (bvnot (bvnot #x00000000)) b)) a)))
(check-sat)
