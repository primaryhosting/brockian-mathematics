/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Real MeasureTheory
open scoped Topology BigOperators Classical

namespace Math2

/-! ## The Sato–Tate distribution -/

/-- The Sato–Tate density `(2/π) sin²θ` on `[0, π]`. -/

lemma integral_UBasis_zero_mul_stDensity :
    (∫ x in (0:ℝ)..π, UBasis 0 x * stDensity x) = 1 := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have : (∫ x in (0:ℝ)..π, UBasis 0 x * stDensity x) = ∫ x in (0:ℝ)..π, stDensity x := by
    simp [UBasis_zero]
  rw [this, integral_stDensity]
  simp [stCDF, Real.sin_two_pi, Real.pi_ne_zero]

/-! ## The span of the Chebyshev functions -/

/-- The `ℝ`-linear span of the functions `x ↦ U_k (cos x)` inside `ℝ → ℝ`. -/
