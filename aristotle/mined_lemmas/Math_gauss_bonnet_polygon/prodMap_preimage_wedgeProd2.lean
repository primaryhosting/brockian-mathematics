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

private theorem prodMap_preimage_wedgeProd2 (t : ℝ) :
    (Prod.map id (MeasurableEquiv.finTwoArrow (α := ℝ))) ⁻¹' (wedgeProd2 t) = wedgeProd t := by
  ext p
  simp only [Set.mem_preimage, wedgeProd2, wedgeProd, Prod.map, Set.mem_setOf_eq,
    MeasurableEquiv.finTwoArrow_apply]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by simp at h1 ⊢; linarith, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨by simp at h1 ⊢; linarith, h2, h3⟩

