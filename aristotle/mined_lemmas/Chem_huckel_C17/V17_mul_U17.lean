import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix

/-- A primitive 17-th root of unity. -/

lemma V17_mul_U17 : V17 * U17 = 1 := mul_eq_one_comm.1 U17_mul_V17

