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

lemma STAverage_smul {θ : ℕ → ℝ} {f : ℝ → ℝ} (c : ℝ)
    (hfa : STAverage θ f) : STAverage θ (c • f) := by
  have hint : (∫ x in (0:ℝ)..π, (c • f) x * stDensity x)
      = c * ∫ x in (0:ℝ)..π, f x * stDensity x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro x _
    simp [mul_assoc]
  rw [STAverage, hint, primeAvg_smul]
  exact hfa.const_mul c

