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

def STAverage (θ : ℕ → ℝ) (f : ℝ → ℝ) : Prop :=
  Tendsto (primeAvg θ f) atTop (𝓝 (∫ x in (0:ℝ)..π, f x * stDensity x))

