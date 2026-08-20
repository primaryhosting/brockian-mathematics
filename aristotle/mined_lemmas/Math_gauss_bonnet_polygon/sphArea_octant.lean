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

theorem sphArea_octant :
    sphArea (sphTriangle (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
      (EuclideanSpace.single 2 1)) = π / 2 := by
  set u : E3 := EuclideanSpace.single 0 1 with hudef
  set v : E3 := EuclideanSpace.single 1 1 with hvdef
  set w : E3 := EuclideanSpace.single 2 1 with hwdef
  have hnorm : ∀ i : Fin 3, ‖(EuclideanSpace.single i (1 : ℝ) : E3)‖ = 1 := by
    intro i; rw [EuclideanSpace.norm_single]; norm_num
  have hinner : ∀ i j : Fin 3, i ≠ j →
      ⟪(EuclideanSpace.single i (1 : ℝ) : E3), EuclideanSpace.single j 1⟫ = 0 := by
    intro i j hij
    rw [EuclideanSpace.inner_single_left]
    simp [EuclideanSpace.single_apply, hij]
  have huv : ⟪u, v⟫ = 0 := hinner 0 1 (by decide)
  have huw : ⟪u, w⟫ = 0 := hinner 0 2 (by decide)
  have hvw : ⟪v, w⟫ = 0 := hinner 1 2 (by decide)
  have hvu : ⟪v, u⟫ = 0 := by rw [real_inner_comm]; exact huv
  have hwu : ⟪w, u⟫ = 0 := by rw [real_inner_comm]; exact huw
  have hwv : ⟪w, v⟫ = 0 := by rw [real_inner_comm]; exact hvw
  have hind : LinearIndependent ℝ ![u, v, w] := by
    have h : ![u, v, w] = ⇑(EuclideanSpace.basisFun (Fin 3) ℝ).toBasis := by
      funext i
      fin_cases i <;> simp [hudef, hvdef, hwdef, EuclideanSpace.basisFun] <;> rfl
    rw [h]
    exact (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.linearIndependent
  have key := gauss_bonnet_polygon u v w (hnorm 0) (hnorm 1) (hnorm 2) hind
  rw [sphAngle_of_orthogonal u v w huv huw hvw,
    sphAngle_of_orthogonal v u w hvu hvw huw,
    sphAngle_of_orthogonal w u v hwu hwv huv] at key
  linarith

end Math

