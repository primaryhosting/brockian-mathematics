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

lemma integral_trap_lower {α β ε : ℝ} (hε : 0 < ε) (hα : 0 ≤ α) (hαβ : α ≤ β)
    (hβ : β ≤ Real.pi) :
    (∫ x in α..β, satoTateDensity x) - 4 / Real.pi * ε
      ≤ ∫ x in (0 : ℝ)..Real.pi, satoTateDensity x * trap α β ε x := by
  have hpi : (0 : ℝ) < 2 / Real.pi := by positivity
  set F := fun x => satoTateDensity x * trap α β ε x with hF
  show (∫ x in α..β, satoTateDensity x) - 4 / Real.pi * ε ≤ ∫ x in (0 : ℝ)..Real.pi, F x
  have key : (∫ x in α..β, satoTateDensity x) - 4 / Real.pi * ε ≤ ∫ x in α..β, F x := by
    rcases le_or_gt (β - α) (2 * ε) with hcase | hcase
    · have h0 : 0 ≤ ∫ x in α..β, F x :=
        integral_density_mul_nonneg hαβ fun x => trap_nonneg _ _ _ x
      have h1 : (∫ x in α..β, satoTateDensity x) ≤ 2 / Real.pi * (β - α) :=
        integral_density_le hαβ
      have h2 : 2 / Real.pi * (β - α) ≤ 2 / Real.pi * (2 * ε) :=
        mul_le_mul_of_nonneg_left hcase hpi.le
      have h3 : 2 / Real.pi * (2 * ε) = 4 / Real.pi * ε := by ring
      linarith
    · have hab : α + ε ≤ β - ε := by linarith
      have mid : (∫ x in (α + ε)..(β - ε), F x) = ∫ x in (α + ε)..(β - ε), satoTateDensity x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hab] at hx
        show satoTateDensity x * trap α β ε x = satoTateDensity x
        rw [trap_eq_one hε hx.1 hx.2, mul_one]
      have a1 : (∫ x in α..(α + ε), F x) + (∫ x in (α + ε)..β, F x) = ∫ x in α..β, F x :=
        intervalIntegral.integral_add_adjacent_intervals
          (dens_trap_intervalIntegrable _ _ _ _ _) (dens_trap_intervalIntegrable _ _ _ _ _)
      have a2 : (∫ x in (α + ε)..(β - ε), F x) + (∫ x in (β - ε)..β, F x)
          = ∫ x in (α + ε)..β, F x :=
        intervalIntegral.integral_add_adjacent_intervals
          (dens_trap_intervalIntegrable _ _ _ _ _) (dens_trap_intervalIntegrable _ _ _ _ _)
      have d1 : (∫ x in α..(α + ε), satoTateDensity x) + (∫ x in (α + ε)..β, satoTateDensity x)
          = ∫ x in α..β, satoTateDensity x :=
        intervalIntegral.integral_add_adjacent_intervals
          (continuous_satoTateDensity.intervalIntegrable _ _)
          (continuous_satoTateDensity.intervalIntegrable _ _)
      have d2 : (∫ x in (α + ε)..(β - ε), satoTateDensity x)
            + (∫ x in (β - ε)..β, satoTateDensity x) = ∫ x in (α + ε)..β, satoTateDensity x :=
        intervalIntegral.integral_add_adjacent_intervals
          (continuous_satoTateDensity.intervalIntegrable _ _)
          (continuous_satoTateDensity.intervalIntegrable _ _)
      have e1 : (∫ x in α..(α + ε), satoTateDensity x) ≤ 2 / Real.pi * ε := by
        have := integral_density_le (u := α) (v := α + ε) (by linarith)
        simpa using this.trans_eq (by ring)
      have e2 : (∫ x in (β - ε)..β, satoTateDensity x) ≤ 2 / Real.pi * ε := by
        have := integral_density_le (u := β - ε) (v := β) (by linarith)
        simpa using this.trans_eq (by ring)
      have p1 : 0 ≤ ∫ x in α..(α + ε), F x :=
        integral_density_mul_nonneg (by linarith) fun x => trap_nonneg _ _ _ x
      have p2 : 0 ≤ ∫ x in (β - ε)..β, F x :=
        integral_density_mul_nonneg (by linarith) fun x => trap_nonneg _ _ _ x
      have h4 : 4 / Real.pi * ε = 2 / Real.pi * ε + 2 / Real.pi * ε := by ring
      linarith
  have outer1 : 0 ≤ ∫ x in (0 : ℝ)..α, F x :=
    integral_density_mul_nonneg hα fun x => trap_nonneg _ _ _ x
  have outer2 : 0 ≤ ∫ x in β..Real.pi, F x :=
    integral_density_mul_nonneg hβ fun x => trap_nonneg _ _ _ x
  have t1 : (∫ x in (0 : ℝ)..α, F x) + (∫ x in α..β, F x) = ∫ x in (0 : ℝ)..β, F x :=
    intervalIntegral.integral_add_adjacent_intervals
      (dens_trap_intervalIntegrable _ _ _ _ _) (dens_trap_intervalIntegrable _ _ _ _ _)
  have t2 : (∫ x in (0 : ℝ)..β, F x) + (∫ x in β..Real.pi, F x) = ∫ x in (0 : ℝ)..Real.pi, F x :=
    intervalIntegral.integral_add_adjacent_intervals
      (dens_trap_intervalIntegrable _ _ _ _ _) (dens_trap_intervalIntegrable _ _ _ _ _)
  linarith

/-! ### Counting estimates -/

