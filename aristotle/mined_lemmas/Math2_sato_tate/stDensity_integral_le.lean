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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open Filter Topology Set Polynomial

/-- The Sato–Tate density `(2/π) sin²θ` on the interval `[0, π]`. -/

lemma stDensity_integral_le {x y : ℝ} (hxy : x ≤ y) :
    (∫ t in x..y, stDensity t) ≤ (2 / π) * (y - x) := by
  have h : (∫ t in x..y, stDensity t) ≤ ∫ _t in x..y, (2 / π : ℝ) := by
    apply intervalIntegral.integral_mono_on hxy
      (continuous_stDensity.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
    exact fun t _ => stDensity_le t
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  linarith [h]

/-- A continuous trapezoidal function which is `1` on `[α, β]`, `0` outside `[α-δ, β+δ]`. -/
