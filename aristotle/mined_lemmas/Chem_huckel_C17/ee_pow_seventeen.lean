import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix

/-- A primitive 17-th root of unity. -/

lemma ee_pow_seventeen (m : ZMod 17) : (ee m) ^ (17 : ℕ) = 1 := by
  rw [ee, ← pow_mul, mul_comm, pow_mul, isPrimitiveRoot_zeta17.pow_eq_one, one_pow]

