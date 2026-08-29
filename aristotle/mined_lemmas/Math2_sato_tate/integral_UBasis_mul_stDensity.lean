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

lemma integral_UBasis_mul_stDensity {n : ℕ} (hn : 1 ≤ n) :
    (∫ x in (0:ℝ)..π, UBasis n x * stDensity x) = 0 := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hcongr : (∫ x in (0:ℝ)..π, UBasis n x * stDensity x)
      = ∫ x in (0:ℝ)..π, (2 / π) * (Real.sin (((n : ℝ) + 1) * x) * Real.sin x) := by
    refine intervalIntegral.integral_congr ?_
    intro x _
    have h := UBasis_mul_sin n x
    simp only [stDensity]
    rw [← h]
    ring
  rw [hcongr, intervalIntegral.integral_const_mul, integral_sin_mul_sin hn, mul_zero]

