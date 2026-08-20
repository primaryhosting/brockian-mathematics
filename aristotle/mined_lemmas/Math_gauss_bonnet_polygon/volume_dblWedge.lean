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

lemma volume_dblWedge (u v w : E3) (hu : ‖u‖ = 1)
    (hst : ∀ a b : ℝ, a • (v - ⟪u, v⟫ • u) + b • (w - ⟪u, w⟫ • u) = 0 → a = 0 ∧ b = 0) :
    volume (dblWedge u v w ∩ ball 0 1) = ENNReal.ofReal (4 * sphAngle u v w / 3) := by
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hus : ⟪u, v - ⟪u, v⟫ • u⟫ = 0 := by
    rw [inner_sub_right, real_inner_smul_right, huu]; ring
  have hut : ⟪u, w - ⟪u, w⟫ • u⟫ = 0 := by
    rw [inner_sub_right, real_inner_smul_right, huu]; ring
  have hset : dblWedge u v w ∩ ball 0 1 = {x : E3 | ‖x‖ < 1 ∧
      ∃ β γ : ℝ, 0 < β * γ ∧
        x - ⟪u, x⟫ • u = β • (v - ⟪u, v⟫ • u) + γ • (w - ⟪u, w⟫ • u)} := by
    ext x
    simp only [dblWedge, mem_inter_iff, mem_setOf_eq, mem_ball_zero_iff]
    constructor
    · rintro ⟨⟨a, b, c, hbc, rfl⟩, hnorm⟩
      refine ⟨hnorm, b, c, hbc, ?_⟩
      have hinner : ⟪u, a • u + b • v + c • w⟫ = a + b * ⟪u, v⟫ + c * ⟪u, w⟫ := by
        rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
          real_inner_smul_right, huu]
        ring
      rw [hinner]
      module
    · rintro ⟨hnorm, β, γ, hβγ, heq⟩
      refine ⟨⟨⟪u, x⟫ - β * ⟪u, v⟫ - γ * ⟪u, w⟫, β, γ, hβγ, ?_⟩, hnorm⟩
      have hx : x = ⟪u, x⟫ • u + (β • (v - ⟪u, v⟫ • u) + γ • (w - ⟪u, w⟫ • u)) := by
        rw [← heq]; abel
      nth_rewrite 1 [hx]
      module
  rw [hset, sphAngle]
  exact SphericalArea.volume_wedge hu hus hut hst

/-! ### A counting identity for signs -/

/-- If `A`, `B`, `C` are nonzero reals, then exactly one of the three products `BC`, `AC`, `AB`
is positive, unless `A`, `B`, `C` all have the same sign, in which case all three are. -/
