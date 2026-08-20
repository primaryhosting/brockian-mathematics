import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix

/-- A primitive 17-th root of unity. -/

lemma isPrimitiveRoot_zeta17 : IsPrimitiveRoot zeta17 17 := by
  simpa [zeta17] using Complex.isPrimitiveRoot_exp 17 (by norm_num)

/-- The additive character `x ↦ ζ¹⁷ ^ x` on `ZMod 17`. -/
