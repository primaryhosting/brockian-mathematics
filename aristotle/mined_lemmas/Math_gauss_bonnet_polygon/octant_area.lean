import RequestProject.Wedge

/-!
# Girard's relation for a solid cone over a spherical triangle

Given three vectors `u v w` in `ℝ³` in general position, the region
`Reg u v w`, the part of the unit ball where the three linear forms `⟪u,·⟫`, `⟪v,·⟫`, `⟪w,·⟫`
are nonnegative, has volume `((π - angle v w) + (π - angle u w) + (π - angle u v) - π)/3`.

This is Girard's theorem in disguise: the three quantities `π - angle · ·` are the dihedral
angles of the cone, and three times the volume of the cone is the area of the spherical
triangle it cuts out on the unit sphere.
-/

open MeasureTheory Metric Set Real InnerProductGeometry

namespace Math

/-- The closed half-space with inner normal `n`. -/

theorem octant_area :
    (volume.toSphere (sphericalTriangle (EuclideanSpace.single 0 (1 : ℝ))
      (EuclideanSpace.single 1 (1 : ℝ)) (EuclideanSpace.single 2 (1 : ℝ)))).toReal = π / 2 := by
  set e0 : E3 := EuclideanSpace.single 0 (1 : ℝ) with he0
  set e1 : E3 := EuclideanSpace.single 1 (1 : ℝ) with he1
  set e2 : E3 := EuclideanSpace.single 2 (1 : ℝ) with he2
  have hinner : ∀ i j : Fin 3, (inner ℝ (EuclideanSpace.single i (1 : ℝ) : E3)
      (EuclideanSpace.single j (1 : ℝ)) : ℝ) = if i = j then 1 else 0 := by
    intro i j
    simp [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  have hnorm : ∀ i : Fin 3, ‖(EuclideanSpace.single i (1 : ℝ) : E3)‖ = 1 := by
    intro i; simp
  have hli : LinearIndependent ℝ ![e0, e1, e2] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hcoord := congrFun (congrArg WithLp.ofLp hg) i
    simp [he0, he1, he2, Fin.sum_univ_three, EuclideanSpace.single_apply] at hcoord
    fin_cases i <;> simp_all
  have key : ∀ x y z : E3, (inner ℝ x y : ℝ) = 0 → (inner ℝ x z : ℝ) = 0 →
      (inner ℝ y z : ℝ) = 0 → sphAngle x y z = π / 2 := by
    intro x y z h1 h2 h3
    rw [sphAngle, h1, h2]
    simp only [zero_smul, sub_zero]
    exact (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two y z).1 h3
  rw [gauss_bonnet_polygon e0 e1 e2 (hnorm 0) (hnorm 1) (hnorm 2) hli,
    key e0 e1 e2 (by simp [he0, he1, hinner]) (by simp [he0, he2, hinner])
      (by simp [he1, he2, hinner]),
    key e1 e0 e2 (by simp [he0, he1, hinner]) (by simp [he1, he2, hinner])
      (by simp [he0, he2, hinner]),
    key e2 e0 e1 (by simp [he0, he2, hinner]) (by simp [he1, he2, hinner])
      (by simp [he0, he1, hinner])]
  ring

end Math

