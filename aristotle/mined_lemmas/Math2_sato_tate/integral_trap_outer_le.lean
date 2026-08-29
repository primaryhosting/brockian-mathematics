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

lemma integral_trap_outer_le {a b δ : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π) :
    (∫ x in (0:ℝ)..π, trap (a - δ) (b + δ) δ x * stDensity x)
      ≤ (stCDF b - stCDF a) + (4 / π) * δ := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  set f : ℝ → ℝ := fun x => trap (a - δ) (b + δ) δ x * stDensity x with hf
  have hcont : Continuous f := (continuous_trap _ _ _).mul continuous_stDensity
  set c : ℝ := max 0 (a - δ) with hc
  set d : ℝ := min π (b + δ) with hd
  have hc0 : 0 ≤ c := le_max_left _ _
  have hdpi : d ≤ π := min_le_left _ _
  have hcd : c ≤ d := by
    refine max_le (le_min hpi.le (by linarith)) (le_min (by linarith) (by linarith))
  have hsplit : (∫ x in (0:ℝ)..c, f x) + (∫ x in c..d, f x) + (∫ x in d..π, f x)
      = ∫ x in (0:ℝ)..π, f x := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hzero1 : (∫ x in (0:ℝ)..c, f x) = 0 := by
    rcases le_or_gt (a - δ) 0 with h | h
    · rw [show c = 0 from max_eq_left h, intervalIntegral.integral_same]
    · have hce : c = a - δ := max_eq_right h.le
      rw [hce]
      have heq : (∫ x in (0:ℝ)..(a - δ), f x) = ∫ _ in (0:ℝ)..(a - δ), (0:ℝ) := by
        refine intervalIntegral.integral_congr ?_
        intro x hx
        rw [Set.uIcc_of_le h.le] at hx
        simp only [hf]
        rw [trap_eq_zero_left hδ hx.2, zero_mul]
      simp [heq]
  have hzero2 : (∫ x in d..π, f x) = 0 := by
    rcases le_or_gt π (b + δ) with h | h
    · rw [show d = π from min_eq_left h, intervalIntegral.integral_same]
    · have hde : d = b + δ := min_eq_right h.le
      rw [hde]
      have heq : (∫ x in (b + δ)..π, f x) = ∫ _ in (b + δ)..π, (0:ℝ) := by
        refine intervalIntegral.integral_congr ?_
        intro x hx
        rw [Set.uIcc_of_le h.le] at hx
        simp only [hf]
        rw [trap_eq_zero_right hδ hx.1, zero_mul]
      simp [heq]
  have hmid : (∫ x in c..d, f x) ≤ stCDF d - stCDF c := by
    rw [← integral_stDensity]
    refine intervalIntegral.integral_mono_on hcd (hcont.intervalIntegrable _ _)
      (continuous_stDensity.intervalIntegrable _ _) ?_
    intro x _
    exact mul_le_of_le_one_left (stDensity_nonneg x) (trap_le_one _ _ _ _)
  have hmono1 : stCDF d ≤ stCDF (b + δ) := stCDF_mono (min_le_right _ _)
  have hmono2 : stCDF (a - δ) ≤ stCDF c := stCDF_mono (le_max_right _ _)
  have e1 : stCDF (b + δ) - stCDF b ≤ (2 / π) * δ := by
    have := stCDF_sub_le (show b ≤ b + δ by linarith)
    have hbd : b + δ - b = δ := by ring
    rw [hbd] at this
    exact this
  have e2 : stCDF a - stCDF (a - δ) ≤ (2 / π) * δ := by
    have := stCDF_sub_le (show a - δ ≤ a by linarith)
    have had : a - (a - δ) = δ := by ring
    rw [had] at this
    exact this
  have esum : (2 / π) * δ + (2 / π) * δ = (4 / π) * δ := by ring
  linarith [hsplit, hzero1, hzero2, hmid, hmono1, hmono2, e1, e2]

