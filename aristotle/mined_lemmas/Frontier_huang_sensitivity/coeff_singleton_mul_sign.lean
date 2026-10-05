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

lemma coeff_singleton_mul_sign {n : ℕ} {f : (Fin n → Bool) → Bool} (hdeg : degree f ≤ 1)
    {x : Fin n → Bool} {i : Fin n} (hne : f (flipAt x i) ≠ f x) :
    fourierCoeff f {i} * (if x i then (-1 : ℤ) else 1)
      = 2 ^ n * (if f x then (-1 : ℤ) else 1) := by
  have hg : (if f (flipAt x i) then (-1 : ℤ) else 1) = -(if f x then (-1 : ℤ) else 1) := by
    revert hne; cases f x <;> cases f (flipAt x i) <;> simp
  have h := flip_diff hdeg x i
  rw [hg] at h
  refine mul_left_cancel₀ two_ne_zero ?_
  linarith [h]

