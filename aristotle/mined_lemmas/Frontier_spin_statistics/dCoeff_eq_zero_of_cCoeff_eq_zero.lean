/-
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate
open scoped InnerProductSpace

namespace Frontier

/-! ## Minkowski geometry -/

/-- The Minkowski bilinear form on `ℝ⁴` with signature `(+,-,-,-)`. -/

theorem dCoeff_eq_zero_of_cCoeff_eq_zero {x : Fin 4 → ℝ} (h : cCoeff x = 0) : dCoeff x = 0 := by
  unfold cCoeff at h
  unfold dCoeff
  by_cases h1 : x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0
  · rw [if_pos h1] at h; norm_num at h
  · by_cases h2 : x 1 = 1 ∧ x 2 = 0 ∧ x 3 = 0
    · rw [if_neg h1, if_pos h2] at h; norm_num at h
    · rw [if_neg h1, if_neg h2]

/-- A nontrivial model of the Wightman-type axioms with `twiceSpin = 1` and Fermi
statistics. -/
