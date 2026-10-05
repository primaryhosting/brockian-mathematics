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

lemma coeff_singleton_ne_zero {n : ℕ} {f : (Fin n → Bool) → Bool} (hdeg : degree f ≤ 1)
    {x : Fin n → Bool} {i : Fin n} (hne : f (flipAt x i) ≠ f x) : fourierCoeff f {i} ≠ 0 := by
  intro h0
  have h := coeff_singleton_mul_sign hdeg hne
  rw [h0, zero_mul] at h
  have hpos : (0 : ℤ) < 2 ^ n := by positivity
  cases f x <;> simp at h <;> omega

