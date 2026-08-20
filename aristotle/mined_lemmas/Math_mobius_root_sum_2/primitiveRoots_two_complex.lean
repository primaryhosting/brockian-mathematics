/-
# Mobius Root Sum 2
Category: Pure Mathematics
Target: Math.mobius_root_sum_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 2
Category: Pure Mathematics
Target: Math.mobius_root_sum_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The set of primitive `2`-nd roots of unity in `ℂ` is `{-1}`. -/

theorem primitiveRoots_two_complex : primitiveRoots 2 ℂ = {(-1 : ℂ)} := by
  ext x
  simp only [mem_primitiveRoots (by norm_num : 0 < 2), Finset.mem_singleton]
  exact ⟨fun h => h.eq_neg_one_of_two_right,
    fun h => h ▸ IsPrimitiveRoot.neg_one 0 (by norm_num)⟩

/-- The sum of the primitive `2`-nd roots of unity equals `μ 2 = -1`. -/
