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

lemma integral_trap_upper {α β ε : ℝ} (hε : 0 < ε) (hαβ : α ≤ β) :
    (∫ x in (0 : ℝ)..Real.pi, satoTateDensity x * trap (α - ε) (β + ε) ε x)
      ≤ (∫ x in α..β, satoTateDensity x) + 4 / Real.pi * ε := by
  set F := fun x => satoTateDensity x * trap (α - ε) (β + ε) ε x with hF
  show (∫ x in (0 : ℝ)..Real.pi, F x) ≤ (∫ x in α..β, satoTateDensity x) + 4 / Real.pi * ε
  set A := min 0 (α - ε) with hA
  set B := max Real.pi (β + ε) with hB
  have hA0 : A ≤ 0 := min_le_left _ _
  have hAae : A ≤ α - ε := min_le_right _ _
  have hBpi : Real.pi ≤ B := le_max_left _ _
  have hBbe : β + ε ≤ B := le_max_right _ _
  have step1 : (∫ x in (0 : ℝ)..Real.pi, F x) ≤ ∫ x in A..B, F x := by
    have h1 : (∫ x in A..(0 : ℝ), F x) + (∫ x in (0 : ℝ)..Real.pi, F x) = ∫ x in A..Real.pi, F x :=
      intervalIntegral.integral_add_adjacent_intervals
        (dens_trap_intervalIntegrable _ _ _ _ _) (dens_trap_intervalIntegrable _ _ _ _ _)
    have h2 : (∫ x in A..Real.pi, F x) + (∫ x in Real.pi..B, F x) = ∫ x in A..B, F x :=
      intervalIntegral.integral_add_adjacent_intervals
        (dens_trap_intervalIntegrable _ _ _ _ _) (dens_trap_intervalIntegrable _ _ _ _ _)
    have p1 : 0 ≤ ∫ x in A..(0 : ℝ), F x :=
      integral_density_mul_nonneg hA0 fun x => trap_nonneg _ _ _ x
    have p2 : 0 ≤ ∫ x in Real.pi..B, F x :=
      integral_density_mul_nonneg hBpi fun x => trap_nonneg _ _ _ x
    linarith
  have s1 : (∫ x in A..(α - ε), F x) = 0 := by
    have h : (∫ x in A..(α - ε), F x) = ∫ _x in A..(α - ε), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hAae] at hx
      show satoTateDensity x * trap (α - ε) (β + ε) ε x = 0
      rw [trap_eq_zero_left hε hx.2, mul_zero]
    simp [h]
  have s2 : (∫ x in (β + ε)..B, F x) = 0 := by
    have h : (∫ x in (β + ε)..B, F x) = ∫ _x in (β + ε)..B, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hBbe] at hx
      show satoTateDensity x * trap (α - ε) (β + ε) ε x = 0
      rw [trap_eq_zero_right hε hx.1, mul_zero]
    simp [h]
  have add1 : (∫ x in A..(α - ε), F x) + (∫ x in (α - ε)..α, F x) = ∫ x in A..α, F x :=
    intervalIntegral.integral_add_adjacent_intervals
      (dens_trap_intervalIntegrable _ _ _ _ _) (dens_trap_intervalIntegrable _ _ _ _ _)
  have add2 : (∫ x in A..α, F x) + (∫ x in α..β, F x) = ∫ x in A..β, F x :=
    intervalIntegral.integral_add_adjacent_intervals
      (dens_trap_intervalIntegrable _ _ _ _ _) (dens_trap_intervalIntegrable _ _ _ _ _)
  have add3 : (∫ x in A..β, F x) + (∫ x in β..(β + ε), F x) = ∫ x in A..(β + ε), F x :=
    intervalIntegral.integral_add_adjacent_intervals
      (dens_trap_intervalIntegrable _ _ _ _ _) (dens_trap_intervalIntegrable _ _ _ _ _)
  have add4 : (∫ x in A..(β + ε), F x) + (∫ x in (β + ε)..B, F x) = ∫ x in A..B, F x :=
    intervalIntegral.integral_add_adjacent_intervals
      (dens_trap_intervalIntegrable _ _ _ _ _) (dens_trap_intervalIntegrable _ _ _ _ _)
  have b1 : (∫ x in (α - ε)..α, F x) ≤ 2 / Real.pi * ε := by
    have := integral_density_mul_le (u := α - ε) (v := α) (by linarith)
      (continuous_trap (α - ε) (β + ε) ε) fun x => trap_le_one _ _ _ x
    simpa using this.trans_eq (by ring)
  have b2 : (∫ x in β..(β + ε), F x) ≤ 2 / Real.pi * ε := by
    have := integral_density_mul_le (u := β) (v := β + ε) (by linarith)
      (continuous_trap (α - ε) (β + ε) ε) fun x => trap_le_one _ _ _ x
    simpa using this.trans_eq (by ring)
  have b3 : (∫ x in α..β, F x) ≤ ∫ x in α..β, satoTateDensity x := by
    apply intervalIntegral.integral_mono_on hαβ (dens_trap_intervalIntegrable _ _ _ _ _)
      (continuous_satoTateDensity.intervalIntegrable _ _)
    intro x _
    have := satoTateDensity_nonneg x
    nlinarith [trap_le_one (α - ε) (β + ε) ε x]
  have hfour : 4 / Real.pi * ε = 2 / Real.pi * ε + 2 / Real.pi * ε := by ring
  linarith

