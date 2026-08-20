import RequestProject.Sector

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The volume of the standard solid wedge of dihedral angle `psi` inside the unit ball:
the axis of the wedge is the first coordinate axis, and the wedge is described in the plane
of the last two coordinates as the cone spanned by `(1,0)` and `(cos psi, sin psi)`. -/

theorem lune_volume (u v w : E3) (hw : ‖w‖ = 1) (hind : LinearIndependent ℝ ![u, v, w]) :
    volume ({x : E3 | ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • u + b • v + c • w} ∩ ball 0 1)
      = ENNReal.ofReal (2 * sphAngle w u v / 3) := by
  set p : E3 := u - ⟪w, u⟫ • w with hp
  set q : E3 := v - ⟪w, v⟫ • w with hq
  have hww : ⟪w, w⟫ = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have hwp : ⟪w, p⟫ = (0 : ℝ) := by
    rw [hp, inner_sub_right, real_inner_smul_right, hww]; ring
  have hwq : ⟪w, q⟫ = (0 : ℝ) := by
    rw [hq, inner_sub_right, real_inner_smul_right, hww]; ring
  -- linear independence of the two projections
  have hpq : LinearIndependent ℝ ![p, q] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h3 : s • u + t • v + (-(s * ⟪w, u⟫ + t * ⟪w, v⟫)) • w = 0 := by
      rw [← hst, hp, hq]
      simp only [smul_sub, smul_smul, neg_smul, add_smul]
      abel
    have := (Fintype.linearIndependent_iff.1 hind) ![s, t, -(s * ⟪w, u⟫ + t * ⟪w, v⟫)] (by
      rw [Fin.sum_univ_three]
      simpa using h3)
    exact ⟨this 0, this 1⟩
  -- the lune is the wedge with axis `w` spanned by the projections `p` and `q`
  have hset : {x : E3 | ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • u + b • v + c • w}
      = {x : E3 | ∃ s t r : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ x = s • p + t • q + r • w} := by
    ext x
    constructor
    · rintro ⟨a, b, c, ha, hb, rfl⟩
      refine ⟨a, b, c + a * ⟪w, u⟫ + b * ⟪w, v⟫, ha, hb, ?_⟩
      rw [hp, hq]
      simp only [smul_sub, smul_smul, add_smul]
      abel
    · rintro ⟨s, t, r, hs, ht, rfl⟩
      refine ⟨s, t, r - s * ⟪w, u⟫ - t * ⟪w, v⟫, hs, ht, ?_⟩
      rw [hp, hq]
      simp only [smul_sub, smul_smul, sub_smul]
      abel
  rw [hset, volume_wedge w p q hw hwp hwq hpq]
  rfl

/-- The area defined above is the surface measure of the unit sphere provided by Mathlib. -/
