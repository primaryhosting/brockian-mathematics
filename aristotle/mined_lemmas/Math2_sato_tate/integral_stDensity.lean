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

lemma integral_stDensity (u v : ℝ) :
    ∫ x in u..v, stDensity x = stCDF v - stCDF u := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_stCDF x)]
  exact (continuous_stDensity).intervalIntegrable u v

