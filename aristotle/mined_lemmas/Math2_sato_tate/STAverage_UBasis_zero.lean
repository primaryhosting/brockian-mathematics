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

lemma STAverage_UBasis_zero {θ : ℕ → ℝ} : STAverage θ (UBasis 0) := by
  rw [STAverage, integral_UBasis_zero_mul_stDensity]
  refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (1:ℝ)))
  filter_upwards [Filter.eventually_ge_atTop 3] with X hX
  have hpos : 0 < (Nat.primesBelow X).card := primesBelow_card_pos hX
  have hne : ((Nat.primesBelow X).card : ℝ) ≠ 0 := by positivity
  simp only [primeAvg, UBasis_zero]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, div_self hne]

