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

lemma cell_bound {u v : ℝ} (huv : u ≤ v) {f : ℝ → ℝ} (hf : Continuous f) {y c : ℝ}
    (h : ∀ x ∈ Icc u v, |f y - f x| ≤ c) :
    |f y * (∫ x in u..v, satoTateDensity x) - ∫ x in u..v, satoTateDensity x * f x|
      ≤ c * ∫ x in u..v, satoTateDensity x := by
  have hint1 : IntervalIntegrable (fun x => satoTateDensity x * f y) MeasureTheory.volume u v :=
    (continuous_satoTateDensity.mul continuous_const).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun x => satoTateDensity x * f x) MeasureTheory.volume u v :=
    (continuous_satoTateDensity.mul hf).intervalIntegrable _ _
  have e1 : f y * (∫ x in u..v, satoTateDensity x) = ∫ x in u..v, satoTateDensity x * f y := by
    rw [intervalIntegral.integral_mul_const]; ring
  have e2 : (∫ x in u..v, satoTateDensity x * f y) - (∫ x in u..v, satoTateDensity x * f x)
      = ∫ x in u..v, (satoTateDensity x * f y - satoTateDensity x * f x) :=
    (intervalIntegral.integral_sub hint1 hint2).symm
  rw [e1, e2]
  have habs : |∫ x in u..v, (satoTateDensity x * f y - satoTateDensity x * f x)|
      ≤ ∫ x in u..v, |satoTateDensity x * f y - satoTateDensity x * f x| :=
    intervalIntegral.abs_integral_le_integral_abs huv
  have hmono : (∫ x in u..v, |satoTateDensity x * f y - satoTateDensity x * f x|)
      ≤ ∫ x in u..v, satoTateDensity x * c := by
    apply intervalIntegral.integral_mono_on huv (hint1.sub hint2).abs
      ((continuous_satoTateDensity.mul continuous_const).intervalIntegrable _ _)
    intro x hx
    have hd := satoTateDensity_nonneg x
    have habs' : |satoTateDensity x * f y - satoTateDensity x * f x|
        = satoTateDensity x * |f y - f x| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hd]
    rw [habs']
    exact mul_le_mul_of_nonneg_left (h x hx) hd
  rw [intervalIntegral.integral_mul_const] at hmono
  calc |∫ x in u..v, (satoTateDensity x * f y - satoTateDensity x * f x)| ≤ _ := habs
    _ ≤ (∫ x in u..v, satoTateDensity x) * c := hmono
    _ = c * ∫ x in u..v, satoTateDensity x := by ring

/-- The uniform grid `0 = t₀ < t₁ < ⋯ < tₙ = π` on `[0, π]`. -/
