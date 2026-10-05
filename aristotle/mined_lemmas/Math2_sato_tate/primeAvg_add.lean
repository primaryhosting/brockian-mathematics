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

lemma primeAvg_add (θ : ℕ → ℝ) (f g : ℝ → ℝ) :
    primeAvg θ (f + g) = fun X => primeAvg θ f X + primeAvg θ g X := by
  funext X
  simp only [primeAvg, Pi.add_apply]
  rw [Finset.sum_add_distrib, add_div]

