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

lemma stIntegral_weyl_eq_zero {m : ℕ} (hm : 1 ≤ m) : stIntegral (weyl m) = 0 := by
  have key : ∀ t : ℝ, weyl m t * stDensity t
      = (1 / π) * (Real.cos (m * t) - Real.cos ((m + 2) * t)) := by
    intro t
    have h := Chebyshev.U_real_cos t (m : ℤ)
    have hU : weyl m t * Real.sin t = Real.sin (((m : ℝ) + 1) * t) := by
      unfold weyl
      rw [show (Chebyshev.U ℝ (m : ℕ)) = Chebyshev.U ℝ (m : ℤ) by norm_cast]
      exact_mod_cast h
    have e1 : Real.cos ((m : ℝ) * t) = Real.cos (((m : ℝ) + 1) * t) * Real.cos t
        + Real.sin (((m : ℝ) + 1) * t) * Real.sin t := by
      rw [show (m : ℝ) * t = ((m : ℝ) + 1) * t - t by ring, Real.cos_sub]
    have e2 : Real.cos (((m : ℝ) + 2) * t) = Real.cos (((m : ℝ) + 1) * t) * Real.cos t
        - Real.sin (((m : ℝ) + 1) * t) * Real.sin t := by
      rw [show ((m : ℝ) + 2) * t = ((m : ℝ) + 1) * t + t by ring, Real.cos_add]
    unfold stDensity
    rw [e1, e2]
    rw [show weyl m t * (2 / π * Real.sin t ^ 2)
        = 2 / π * ((weyl m t * Real.sin t) * Real.sin t) by ring, hU]
    field_simp
    ring
  unfold stIntegral
  simp only [key]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub]
  · rw [integral_cos_nat_mul hm, show ((m : ℝ) + 2) = ((m + 2 : ℕ) : ℝ) by push_cast; ring]
    rw [integral_cos_nat_mul (by omega : 1 ≤ m + 2)]
    simp
  · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _

