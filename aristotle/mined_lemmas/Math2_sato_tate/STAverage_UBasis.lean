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

lemma STAverage_UBasis {θ : ℕ → ℝ}
    (hmom : ∀ n : ℕ, 1 ≤ n → Tendsto (primeAvg θ (UBasis n)) atTop (𝓝 0)) (k : ℕ) :
    STAverage θ (UBasis k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact STAverage_UBasis_zero
  · rw [STAverage, integral_UBasis_mul_stDensity hk]
    exact hmom k hk

