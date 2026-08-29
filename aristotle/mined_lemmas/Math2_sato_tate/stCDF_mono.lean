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

lemma stCDF_mono : Monotone stCDF := by
  intro u v huv
  have := integral_stDensity u v
  have hint : 0 ≤ ∫ x in u..v, stDensity x :=
    intervalIntegral.integral_nonneg huv (fun x _ => stDensity_nonneg x)
  linarith [this ▸ hint]

