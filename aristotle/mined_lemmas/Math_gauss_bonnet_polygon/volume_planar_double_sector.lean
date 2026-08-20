import RequestProject.Sector

/-!
# Volume of a wedge in three-dimensional space

The main result of this file is `SphericalArea.volume_wedge`: for a unit vector `u` and two
linearly independent vectors `s`, `t` orthogonal to `u`, the set of points of the open unit ball
whose orthogonal projection to `u^⊥` lies in the double wedge spanned by `s` and `t` has volume
`4 * angle s t / 3`.
-/

open MeasureTheory Real Set Metric InnerProductGeometry
open scoped ENNReal Real RealInnerProductSpace

namespace SphericalArea

/-- Coordinates of `EuclideanSpace ℝ (Fin 3)` as a product `ℝ × (ℝ × ℝ)`. -/

lemma volume_planar_double_sector (α R2 : ℝ) (hα0 : 0 ≤ α) (hαπ : α ≤ π) :
    volume {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < R2 ∧
        0 < p.2 * (p.1 * Real.sin α - p.2 * Real.cos α)} = ENNReal.ofReal (α * R2) := by
  set S : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < R2 ∧
      0 < p.2 * (p.1 * Real.sin α - p.2 * Real.cos α)} with hSdef
  have hSopen : IsOpen S := by
    have hS : S = {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < R2} ∩
        {p : ℝ × ℝ | 0 < p.2 * (p.1 * Real.sin α - p.2 * Real.cos α)} := rfl
    rw [hS]
    exact (isOpen_lt (by fun_prop) continuous_const).inter
      (isOpen_lt continuous_const (by fun_prop))
  have hmeas : MeasurableSet S := hSopen.measurableSet
  set A : Set ℝ := {ψ : ℝ | 0 < Real.sin ψ * Real.sin (α - ψ)} with hAdef
  have hAmeas : MeasurableSet A :=
    (isOpen_lt continuous_const (by fun_prop : Continuous fun ψ : ℝ =>
      Real.sin ψ * Real.sin (α - ψ))).measurableSet
  set F : ℝ → ℝ≥0∞ := fun r => if r ^ 2 < R2 then ENNReal.ofReal r else 0 with hFdef
  set G : ℝ → ℝ≥0∞ := A.indicator 1 with hGdef
  rw [← lintegral_indicator_one hmeas, ← lintegral_comp_polarCoord_symm]
  have key : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • S.indicator 1 (polarCoord.symm p) = F p.1 * G p.2 := by
    rintro ⟨r, ψ⟩ hp
    simp only [polarCoord_target, mem_prod, mem_Ioi, mem_Ioo] at hp
    obtain ⟨hr, -⟩ := hp
    have hsymm : polarCoord.symm (r, ψ) = (r * Real.cos ψ, r * Real.sin ψ) := rfl
    have hcond : (polarCoord.symm (r, ψ)) ∈ S ↔ (r ^ 2 < R2 ∧ ψ ∈ A) := by
      rw [hsymm]
      simp only [hSdef, hAdef, mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · nlinarith [Real.sin_sq_add_cos_sq ψ]
        · have : r * Real.sin ψ * (r * Real.cos ψ * Real.sin α - r * Real.sin ψ * Real.cos α)
              = r ^ 2 * (Real.sin ψ * Real.sin (α - ψ)) := by
            rw [Real.sin_sub]; ring
          rw [this] at h2
          nlinarith [sq_nonneg r]
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · nlinarith [Real.sin_sq_add_cos_sq ψ]
        · have : r * Real.sin ψ * (r * Real.cos ψ * Real.sin α - r * Real.sin ψ * Real.cos α)
              = r ^ 2 * (Real.sin ψ * Real.sin (α - ψ)) := by
            rw [Real.sin_sub]; ring
          rw [this]
          positivity
    simp only [hFdef, hGdef]
    by_cases h1 : r ^ 2 < R2
    · by_cases h2 : ψ ∈ A
      · rw [Set.indicator_of_mem (hcond.2 ⟨h1, h2⟩), Set.indicator_of_mem h2, if_pos h1]
        simp
      · rw [Set.indicator_of_notMem (fun hc => h2 (hcond.1 hc).2),
          Set.indicator_of_notMem h2]
        simp
    · rw [Set.indicator_of_notMem (fun hc => h1 (hcond.1 hc).1), if_neg h1]
      simp
  have hFmeas : Measurable F := by
    apply Measurable.ite _ (by fun_prop) measurable_const
    exact (measurableSet_lt (by fun_prop) measurable_const)
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet key, polarCoord_target,
    Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul hFmeas.aemeasurable
      ((measurable_one.indicator hAmeas).aemeasurable),
    hFdef, lintegral_radial R2, lintegral_indicator hAmeas]
  simp only [Pi.one_apply, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, one_mul]
  rw [Measure.restrict_apply hAmeas]
  have hAI : A ∩ Ioo (-π) π = {ψ : ℝ | ψ ∈ Ioo (-π) π ∧ 0 < Real.sin ψ * Real.sin (α - ψ)} := by
    ext ψ; simp only [hAdef, mem_inter_iff, mem_setOf_eq]; tauto
  rw [hAI, volume_angleSet α hα0 hαπ]
  rcases le_or_gt R2 0 with h | h
  · rw [ENNReal.ofReal_eq_zero.2 (by linarith : R2 / 2 ≤ 0), zero_mul]
    exact (ENNReal.ofReal_eq_zero.2 (by nlinarith)).symm
  · rw [← ENNReal.ofReal_mul (by linarith)]
    congr 1
    ring

end SphericalArea

import Mathlib
import RequestProject.Wedge

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

/-!
# Girard's theorem / the Gauss-Bonnet formula for a spherical triangle

The angle sum of a geodesic triangle on the unit sphere in `ℝ³` exceeds `π` exactly by the
area of the triangle.
-/

open MeasureTheory Metric Real Set InnerProductGeometry
open scoped RealInnerProductSpace ENNReal

namespace Math

/-- Three dimensional Euclidean space. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The cone over a subset `S` of the unit sphere: all points `r • y` with `y ∈ S` and
`0 < r < 1`. -/
