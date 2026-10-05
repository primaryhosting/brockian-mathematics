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

lemma stCDF_sub_le {u v : ℝ} (huv : u ≤ v) : stCDF v - stCDF u ≤ (2 / π) * (v - u) := by
  have h := integral_stDensity u v
  have hle : (∫ x in u..v, stDensity x) ≤ ∫ _ in u..v, (2 / π : ℝ) :=
    intervalIntegral.integral_mono_on huv
      (continuous_stDensity.intervalIntegrable u v)
      (intervalIntegrable_const) (fun x _ => stDensity_le x)
  rw [h, intervalIntegral.integral_const, smul_eq_mul] at hle
  nlinarith [hle]

/-! ## Trapezoidal test functions -/

/-- A continuous trapezoidal bump: it is `1` on `[c+δ, d-δ]`, `0` outside `(c,d)`,
and takes values in `[0,1]`. -/
