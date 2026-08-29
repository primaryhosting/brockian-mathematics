/-
Volume of a wedge of the unit ball of `EuclideanSpace ℝ (Fin 3)` in standard position.

This is an auxiliary file for the Gauss-Bonnet (Girard) theorem for spherical triangles.
-/
import RequestProject.Sector

open MeasureTheory Metric Set Real
open scoped ENNReal

namespace Math

/-- Euclidean 3-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The wedge of the unit ball cut out by the half-spaces with inner normals
`(1,0,0)` and `(cos t, sin t, 0)`. -/

theorem volume_planeSector (t : ℝ) (ht0 : 0 ≤ t) (htpi : t ≤ π) (R : ℝ) (hR : 0 ≤ R) :
    volume (planeSector t R) = ENNReal.ofReal ((π - t) / 2 * R ^ 2) := by
  classical
  have hSmeas : MeasurableSet (planeSector t R) := measurableSet_planeSector t R
  have hpre : MeasurableSet (polarCoord.symm ⁻¹' planeSector t R) :=
    hSmeas.preimage (by fun_prop)
  have h1 : volume (planeSector t R)
      = ∫⁻ p, (planeSector t R).indicator (fun _ => (1 : ℝ≥0∞)) p := by
    rw [lintegral_indicator hSmeas]; simp
  rw [h1, ← lintegral_comp_polarCoord_symm]
  have h2 : ∀ p : ℝ × ℝ,
      ENNReal.ofReal p.1 • (planeSector t R).indicator (fun _ => (1 : ℝ≥0∞))
          (polarCoord.symm p)
        = (polarCoord.symm ⁻¹' planeSector t R).indicator (fun q => ENNReal.ofReal q.1) p := by
    intro p
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h : polarCoord.symm p ∈ planeSector t R
    · simp [Set.mem_preimage]
    · simp [Set.mem_preimage]
  simp_rw [h2]
  rw [lintegral_indicator hpre, Measure.restrict_restrict hpre,
    polar_preimage_planeSector t ht0 htpi R hR, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have key := lintegral_prod_mul (μ := volume.restrict (Ioc (0 : ℝ) R))
      (ν := volume.restrict (Ioo (t - π / 2) (π / 2))) (f := fun x => ENNReal.ofReal x)
      (g := fun _ => (1 : ℝ≥0∞)) (by fun_prop) (by fun_prop)
  simp only [mul_one, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioo, one_mul] at key
  rw [key, lintegral_ofReal_Ioc R hR, ← ENNReal.ofReal_mul (by positivity)]
  ring_nf

end Math

/-
The cells cut out of the unit ball of `ℝ³` by three planes through the origin.

This is an auxiliary file for the Gauss-Bonnet (Girard) theorem for spherical triangles.
-/
import RequestProject.Lune

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- The open half-space with inner normal `n`. -/
