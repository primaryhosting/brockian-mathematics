/-
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace Frontier

/-! ## Basic definitions for Boolean functions on the hypercube -/

/-- The character `χ_S(x) = ∏_{i ∈ S} (-1)^{x i}`, valued in `ℤ`. -/

lemma sensitive_of_coeff {n : ℕ} {f : (Fin n → Bool) → Bool} (hdeg : degree f ≤ 1)
    {i : Fin n} (hc : fourierCoeff f {i} ≠ 0) (x : Fin n → Bool) : f (flipAt x i) ≠ f x := by
  intro heq
  have h := flip_diff hdeg x i
  rw [heq, sub_self, mul_zero] at h
  have hs : (if x i then (-1 : ℤ) else 1) ≠ 0 := by cases x i <;> norm_num
  rcases mul_eq_zero.1 h.symm with h1 | h2
  · rcases mul_eq_zero.1 h1 with h3 | h4
    · norm_num at h3
    · exact hc h4
  · exact hs h2

/-- A Boolean function of degree at most one has sensitivity at most one: it is constant
or a (possibly negated) dictator. -/
