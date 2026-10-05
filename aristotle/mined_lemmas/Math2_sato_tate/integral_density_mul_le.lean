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

open Filter Topology Set MeasureTheory intervalIntegral
open scoped Real

namespace Math2

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma integral_density_mul_le {u v : ℝ} (huv : u ≤ v) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφ1 : ∀ x, φ x ≤ 1) :
    (∫ x in u..v, satoTateDensity x * φ x) ≤ 2 / Real.pi * (v - u) := by
  have h : (∫ x in u..v, satoTateDensity x * φ x) ≤ ∫ _x in u..v, (2 / Real.pi : ℝ) := by
    apply intervalIntegral.integral_mono_on huv
      ((continuous_satoTateDensity.mul hφ).intervalIntegrable _ _)
      (intervalIntegral.intervalIntegrable_const)
    intro x _
    simp only [Pi.mul_apply]
    have h1 := satoTateDensity_le x
    have h2 := satoTateDensity_nonneg x
    nlinarith [hφ1 x]
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  linarith [h, (by ring : (v - u) * (2 / Real.pi : ℝ) = 2 / Real.pi * (v - u))]

