; obligation: masking identity  (mask & a) | (~mask & a) = a
(set-logic QF_BV)
(declare-const mask (_ BitVec 32))
(declare-const a (_ BitVec 32))
(assert (not (= (bvor (bvand mask a) (bvand (bvnot mask) a)) a)))
(check-sat)
