/-
# Noether Conservation
Category: Frontier Physics
Target: Frontier.noether_conservation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- Expansion of a continuous linear functional on `ℝ × ℝ` in the standard basis. -/

lemma clm_prod_apply (f : ℝ × ℝ →L[ℝ] ℝ) (a b : ℝ) :
    f (a, b) = a * f (1, 0) + b * f (0, 1) := by
  have h : ((a, b) : ℝ × ℝ) = a • ((1, 0) : ℝ × ℝ) + b • ((0, 1) : ℝ × ℝ) := by
    simp
  rw [h, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- Infinitesimal invariance of the Lagrangian along the generator
`w = (X x, X' x * u)` forces the directional derivative `dL z w` to vanish. -/
