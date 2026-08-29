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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open MeasureTheory Filter Topology Set

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

theorem satoTate_second_moment : ∫ t, (2 * Real.cos t) ^ 2 ∂satoTateMeasure = 1 := by
  rw [satoTate_integral]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t / Real.pi - Real.sin (4 * t) / (4 * Real.pi))
      (satoTateDensity t * (2 * Real.cos t) ^ 2) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => t / Real.pi) (1 / Real.pi) t := by
      simpa using (hasDerivAt_id t).div_const Real.pi
    have h2 : HasDerivAt (fun t : ℝ => Real.sin (4 * t) / (4 * Real.pi))
        (4 * Real.cos (4 * t) / (4 * Real.pi)) t := by
      have := ((Real.hasDerivAt_sin (4 * t)).comp t ((hasDerivAt_id t).const_mul 4)).div_const
        (4 * Real.pi)
      simpa [mul_comm] using this
    have h3 := h1.sub h2
    have hc : Real.cos (4 * t) = 1 - 8 * (Real.sin t ^ 2 * Real.cos t ^ 2) := by
      have h4 : (4 : ℝ) * t = 2 * (2 * t) := by ring
      rw [h4, Real.cos_two_mul, Real.cos_two_mul, Real.sin_sq]
      ring
    convert h3 using 1
    rw [hc]
    unfold satoTateDensity
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => h t)
    (by unfold satoTateDensity; apply Continuous.intervalIntegrable; fun_prop)]
  have hs : Real.sin (4 * Real.pi) = 0 := by
    have h4 : (4:ℝ) * Real.pi = 2 * (2 * Real.pi) := by ring
    rw [h4]
    simp [Real.sin_two_mul]
  rw [hs]
  field_simp
  norm_num

/-- The bounded continuous function `θ ↦ 2 cos θ`. -/
