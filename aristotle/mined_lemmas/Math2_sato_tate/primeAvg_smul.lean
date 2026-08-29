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

lemma primeAvg_smul (θ : ℕ → ℝ) (c : ℝ) (f : ℝ → ℝ) :
    primeAvg θ (c • f) = fun X => c * primeAvg θ f X := by
  funext X
  simp only [primeAvg, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, mul_div_assoc]

