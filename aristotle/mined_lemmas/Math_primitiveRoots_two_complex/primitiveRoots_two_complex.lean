import Mathlib

/-!
# Mobius Root Sum 2
Category: Pure Mathematics
Target: Math.mobius_root_sum_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open Finset

/-- The set of primitive `2`-th roots of unity in `ℂ` is `{-1}`. -/

theorem primitiveRoots_two_complex : primitiveRoots 2 ℂ = {-1} := by
  ext z
  rw [mem_primitiveRoots (by norm_num), Finset.mem_singleton]
  constructor
  · intro h
    have h2 := h.pow_eq_one
    have hne : z ≠ 1 := by
      intro he; subst he; simpa using h.ne_one (by norm_num)
    have hfac : (z - 1) * (z + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 hfac with h3 | h3
    · exact absurd (by linear_combination h3) hne
    · linear_combination h3
  · rintro rfl
    exact IsPrimitiveRoot.neg_one _ (by norm_num)

/-- The sum of the primitive `2`-th roots of unity equals `μ 2`. -/
