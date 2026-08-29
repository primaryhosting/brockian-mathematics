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

theorem satoTate_first_moment : ∫ t, 2 * Real.cos t ∂satoTateMeasure = 0 := by
  rw [satoTate_integral]
  have h : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (4 / Real.pi) * Real.sin t ^ 3 / 3)
      (satoTateDensity t * (2 * Real.cos t)) t := by
    intro t
    have hs : HasDerivAt (fun t : ℝ => Real.sin t ^ 3) (3 * Real.sin t ^ 2 * Real.cos t) t := by
      simpa using ((Real.hasDerivAt_sin t).pow 3)
    have h2 := (hs.const_mul (4 / Real.pi)).div_const 3
    convert h2 using 1
    unfold satoTateDensity
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => h t)
    (by unfold satoTateDensity; apply Continuous.intervalIntegrable; fun_prop)]
  simp

/-- The second moment of the Sato–Tate distribution is `1`: `∫ (2cos θ)² dμ_ST = 1`. -/
