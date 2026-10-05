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

lemma coeff_eq_zero_of_two_le_card {n : ℕ} {f : (Fin n → Bool) → Bool} (hdeg : degree f ≤ 1)
    {S : Finset (Fin n)} (hS : 2 ≤ S.card) : fourierCoeff f S = 0 := by
  by_contra hc
  have hmem : S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => fourierCoeff f S ≠ 0) := by simp [hc]
  have hle : S.card ≤ degree f := Finset.le_sup hmem
  omega

/-- For a function of degree at most one, flipping a coordinate changes the `±1`-valued
version of `f` by exactly twice the corresponding singleton Fourier coefficient. -/
