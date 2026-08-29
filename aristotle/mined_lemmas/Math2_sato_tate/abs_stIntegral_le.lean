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

lemma abs_stIntegral_le {f : ℝ → ℝ} {C : ℝ} (hf : Continuous f)
    (h : ∀ t ∈ Icc (0:ℝ) π, |f t| ≤ C) : |stIntegral f| ≤ C := by
  have hpi : (0:ℝ) ≤ π := Real.pi_pos.le
  have h1 : |stIntegral f| ≤ ∫ t in (0:ℝ)..π, |f t * stDensity t| :=
    intervalIntegral.abs_integral_le_integral_abs hpi
  have h2 : (∫ t in (0:ℝ)..π, |f t * stDensity t|) ≤ ∫ t in (0:ℝ)..π, C * stDensity t := by
    apply intervalIntegral.integral_mono_on hpi
    · exact ((hf.mul continuous_stDensity).abs).intervalIntegrable _ _
    · exact (continuous_const.mul continuous_stDensity).intervalIntegrable _ _
    · intro t ht
      rw [abs_mul, abs_of_nonneg (stDensity_nonneg t)]
      exact mul_le_mul_of_nonneg_right (h t ht) (stDensity_nonneg t)
  have h3 : (∫ t in (0:ℝ)..π, C * stDensity t) = C := by
    have hc := stIntegral_const_mul C (fun _ => 1)
    simp only [mul_one, stIntegral_one] at hc
    exact hc
  linarith

/-! ### Basic properties of prime averages -/

