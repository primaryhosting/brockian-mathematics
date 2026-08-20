/-
# Mobius Root Sum 2
Category: Pure Mathematics
Target: Math.mobius_root_sum_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring `/-! ... -/`,
-- so the header above is kept verbatim as a plain block comment.)

import Mathlib

namespace Math

/-- The set of primitive `2`-nd roots of unity in `ℂ` is `{-1}`. -/

theorem primitiveRoots_two_complex : primitiveRoots 2 ℂ = {-1} := by
  ext z
  rw [mem_primitiveRoots (by norm_num), Finset.mem_singleton]
  constructor
  · intro h
    have h2 := h.pow_eq_one
    have hfac : (z - 1) * (z + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 hfac with h1 | h1
    · exfalso
      have hz : z = 1 := by linear_combination h1
      have := h.dvd_of_pow_eq_one 1 (by simp [hz])
      omega
    · linear_combination h1
  · rintro rfl
    exact IsPrimitiveRoot.neg_one 0 (by norm_num)

/-- The sum of the primitive `2`-nd roots of unity equals `μ(2) = -1`. -/
