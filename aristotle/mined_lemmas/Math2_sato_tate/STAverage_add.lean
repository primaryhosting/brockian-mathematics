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

lemma STAverage_add {θ : ℕ → ℝ} {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfa : STAverage θ f) (hga : STAverage θ g) : STAverage θ (f + g) := by
  have hint : (∫ x in (0:ℝ)..π, (f + g) x * stDensity x)
      = (∫ x in (0:ℝ)..π, f x * stDensity x) + ∫ x in (0:ℝ)..π, g x * stDensity x := by
    have hc : (∫ x in (0:ℝ)..π, (f + g) x * stDensity x)
        = ∫ x in (0:ℝ)..π, (f x * stDensity x + g x * stDensity x) := by
      refine intervalIntegral.integral_congr ?_
      intro x _
      simp [add_mul]
    rw [hc]
    exact intervalIntegral.integral_add ((hf.mul continuous_stDensity).intervalIntegrable _ _)
      ((hg.mul continuous_stDensity).intervalIntegrable _ _)
  rw [STAverage, hint, primeAvg_add]
  exact hfa.add hga

