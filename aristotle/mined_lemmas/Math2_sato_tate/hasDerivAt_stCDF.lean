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

lemma hasDerivAt_stCDF (t : ℝ) : HasDerivAt stCDF (stDensity t) t := by
  have hπ : (π:ℝ) ≠ 0 := Real.pi_ne_zero
  have h1 : HasDerivAt (fun t : ℝ => t / π) (1 / π) t := by
    simpa using (hasDerivAt_id t).div_const π
  have h2 : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * t) * 2) t := by
    have : HasDerivAt (fun t : ℝ => 2 * t) 2 t := by
      simpa using (hasDerivAt_id t).const_mul (2:ℝ)
    simpa using (Real.hasDerivAt_sin (2 * t)).comp t this
  have h3 := h1.sub (h2.div_const (2 * π))
  convert h3 using 1
  have hcos : Real.cos (2 * t) = 1 - 2 * Real.sin t ^ 2 := by
    rw [Real.cos_two_mul']
    nlinarith [Real.sin_sq_add_cos_sq t]
  rw [hcos]
  unfold stDensity
  field_simp
  ring

