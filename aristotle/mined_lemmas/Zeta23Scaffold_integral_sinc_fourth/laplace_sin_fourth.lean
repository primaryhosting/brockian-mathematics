/-
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
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

namespace Zeta23Scaffold

open MeasureTheory Set Real Filter Topology

/-! ### Laplace transform of `cos (a * x)` on `(0, ∞)` -/

/-- The function `x ↦ e^{-t x} cos (a x)` is integrable on `(0, ∞)` when `t > 0`. -/

theorem laplace_sin_fourth (t : ℝ) (ht : 0 < t) :
    ∫ x in Ioi (0 : ℝ), Real.sin x ^ 4 * Real.exp (-(t * x))
      = 3 / (8 * t) - t / (2 * (t ^ 2 + 4)) + t / (8 * (t ^ 2 + 16)) := by
  have key : ∀ x : ℝ, Real.sin x ^ 4 * Real.exp (-(t * x))
      = (3 / 8 * (Real.exp (-(t * x)) * Real.cos (0 * x))
          - 1 / 2 * (Real.exp (-(t * x)) * Real.cos (2 * x)))
        + 1 / 8 * (Real.exp (-(t * x)) * Real.cos (4 * x)) := by
    intro x
    have h4 : (4 : ℝ) * x = 2 * (2 * x) := by ring
    rw [h4]
    simp only [Real.cos_two_mul, zero_mul, Real.cos_zero]
    have hs : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
      have := Real.sin_sq_add_cos_sq x; linarith
    rw [show Real.sin x ^ 4 = (Real.sin x ^ 2) ^ 2 by ring, hs]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x _ => key x)]
  have hI1 : IntegrableOn
      (fun x : ℝ => 3 / 8 * (Real.exp (-(t * x)) * Real.cos (0 * x))) (Ioi 0) :=
    (laplace_cos_integrableOn t 0 ht).const_mul _
  have hI2 : IntegrableOn
      (fun x : ℝ => 1 / 2 * (Real.exp (-(t * x)) * Real.cos (2 * x))) (Ioi 0) :=
    (laplace_cos_integrableOn t 2 ht).const_mul _
  have hI3 : IntegrableOn
      (fun x : ℝ => 1 / 8 * (Real.exp (-(t * x)) * Real.cos (4 * x))) (Ioi 0) :=
    (laplace_cos_integrableOn t 4 ht).const_mul _
  have hI12 : IntegrableOn (fun x : ℝ => 3 / 8 * (Real.exp (-(t * x)) * Real.cos (0 * x))
      - 1 / 2 * (Real.exp (-(t * x)) * Real.cos (2 * x))) (Ioi 0) := hI1.sub hI2
  rw [MeasureTheory.integral_add hI12 hI3, MeasureTheory.integral_sub hI1 hI2,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul,
    laplace_cos t 0 ht, laplace_cos t 2 ht, laplace_cos t 4 ht]
  have h1 : t ^ 2 + (0 : ℝ) ^ 2 = t ^ 2 := by ring
  have h2 : t ^ 2 + (2 : ℝ) ^ 2 = t ^ 2 + 4 := by ring
  have h3 : t ^ 2 + (4 : ℝ) ^ 2 = t ^ 2 + 16 := by ring
  rw [h1, h2, h3]
  have htne : t ≠ 0 := ne_of_gt ht
  field_simp

/-- `t³ · (Laplace transform of sin⁴ at t)` simplifies to a difference of two Lorentzians. -/
