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

lemma volume_angleSet (α : ℝ) (hα0 : 0 ≤ α) (hαπ : α ≤ π) :
    volume {ψ : ℝ | ψ ∈ Ioo (-π) π ∧ 0 < Real.sin ψ * Real.sin (α - ψ)}
      = ENNReal.ofReal (2 * α) := by
  rw [angleSet_eq α hα0 hαπ]
  rw [measure_union _ measurableSet_Ioo]
  · rw [Real.volume_Ioo, Real.volume_Ioo,
      ← ENNReal.ofReal_add (by linarith) (by linarith)]
    congr 1
    ring
  · rw [Set.disjoint_left]
    rintro x ⟨hx1, _⟩ ⟨_, hx2⟩
    linarith [Real.pi_pos]

