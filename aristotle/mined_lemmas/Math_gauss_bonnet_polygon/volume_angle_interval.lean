import RequestProject.Sector

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The volume of the standard solid wedge of dihedral angle `psi` inside the unit ball:
the axis of the wedge is the first coordinate axis, and the wedge is described in the plane
of the last two coordinates as the cone spanned by `(1,0)` and `(cos psi, sin psi)`. -/

theorem volume_angle_interval (psi : ℝ) (hpi : psi ≤ π) :
    volume (Ioo (-π) π ∩ Icc 0 psi) = ENNReal.ofReal psi := by
  have hsub1 : Ico (0 : ℝ) psi ⊆ Ioo (-π) π ∩ Icc 0 psi := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨⟨by linarith [pi_pos], by linarith⟩, hx1, hx2.le⟩
  refine le_antisymm ?_ ?_
  · calc volume (Ioo (-π) π ∩ Icc 0 psi) ≤ volume (Icc (0 : ℝ) psi) := measure_mono inter_subset_right
      _ = ENNReal.ofReal psi := by rw [Real.volume_Icc]; simp
  · calc ENNReal.ofReal psi = volume (Ico (0 : ℝ) psi) := by rw [Real.volume_Ico]; simp
      _ ≤ _ := measure_mono hsub1

/-- The area of the planar circular sector of radius `rho` and angle `psi ∈ [0, π]`,
described as the set of points of the open disc of radius `rho` lying in the convex cone
spanned by the directions `(1, 0)` and `(cos psi, sin psi)`. -/
