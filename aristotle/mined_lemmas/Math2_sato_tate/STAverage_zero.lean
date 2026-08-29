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

lemma STAverage_zero {θ : ℕ → ℝ} : STAverage θ 0 := by
  have hint : (∫ x in (0:ℝ)..π, (0 : ℝ → ℝ) x * stDensity x) = 0 := by simp
  have havg : primeAvg θ 0 = fun _ => (0:ℝ) := by
    funext X; simp [primeAvg]
  rw [STAverage, hint, havg]
  exact tendsto_const_nhds

