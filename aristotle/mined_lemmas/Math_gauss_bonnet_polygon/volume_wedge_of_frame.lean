import RequestProject.Sector

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The volume of the standard solid wedge of dihedral angle `psi` inside the unit ball:
the axis of the wedge is the first coordinate axis, and the wedge is described in the plane
of the last two coordinates as the cone spanned by `(1,0)` and `(cos psi, sin psi)`. -/

theorem volume_wedge_of_frame (a b1 b2 : E3) (psi np nq : ℝ)
    (ha : ‖a‖ = 1) (hb1 : ‖b1‖ = 1) (hb2 : ‖b2‖ = 1)
    (hab1 : ⟪a, b1⟫ = (0 : ℝ)) (hab2 : ⟪a, b2⟫ = (0 : ℝ)) (hb12 : ⟪b1, b2⟫ = (0 : ℝ))
    (hnp : 0 < np) (hnq : 0 < nq) (h0 : 0 ≤ psi) (hpi : psi ≤ π) (hsin : 0 < Real.sin psi) :
    volume ({x : E3 | ∃ s t r : ℝ, 0 ≤ s ∧ 0 ≤ t ∧
        x = s • (np • b1) + t • ((nq * Real.cos psi) • b1 + (nq * Real.sin psi) • b2) + r • a}
      ∩ ball 0 1) = ENNReal.ofReal (2 * psi / 3) := by
  have hb1a : ⟪b1, a⟫ = (0 : ℝ) := by rw [real_inner_comm]; exact hab1
  have hb2a : ⟪b2, a⟫ = (0 : ℝ) := by rw [real_inner_comm]; exact hab2
  have hb2b1 : ⟪b2, b1⟫ = (0 : ℝ) := by rw [real_inner_comm]; exact hb12
  have hb1b1 : ⟪b1, b1⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hb1]; norm_num
  have hb2b2 : ⟪b2, b2⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hb2]; norm_num
  have hon : Orthonormal ℝ ![a, b1, b2] := by
    constructor
    · intro i; fin_cases i <;> simpa
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ E3 := by simp
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range ![a, b1, b2]) := by
    rw [← coe_basisOfLinearIndependentOfCardEqFinrank hon.linearIndependent hcard]
    exact (Module.Basis.span_eq _).ge
  let B : OrthonormalBasis (Fin 3) ℝ E3 := OrthonormalBasis.mk hon hspan
  have hB0 : B 0 = a := by simp [B, OrthonormalBasis.coe_mk]
  have hB1 : B 1 = b1 := by simp [B, OrthonormalBasis.coe_mk]
  have hB2 : B 2 = b2 := by simp [B, OrthonormalBasis.coe_mk]
  have hsum : ∀ x : E3, ⟪a, x⟫ • a + ⟪b1, x⟫ • b1 + ⟪b2, x⟫ • b2 = x := by
    intro x
    have hx := B.sum_repr x
    rw [Fin.sum_univ_three, B.repr_apply_apply, B.repr_apply_apply, B.repr_apply_apply,
      hB0, hB1, hB2] at hx
    exact hx
  have hsets : ({x : E3 | ∃ s t r : ℝ, 0 ≤ s ∧ 0 ≤ t ∧
        x = s • (np • b1) + t • ((nq * Real.cos psi) • b1 + (nq * Real.sin psi) • b2) + r • a}
      ∩ ball 0 1)
      = B.repr ⁻¹' {y : E3 | ‖y‖ < 1 ∧ 0 ≤ y 2 ∧
          0 ≤ y 1 * Real.sin psi - y 2 * Real.cos psi} := by
    ext x
    have hn : ‖B.repr x‖ = ‖x‖ := B.repr.norm_map x
    have e1 : (B.repr x) 1 = ⟪b1, x⟫ := by rw [B.repr_apply_apply, hB1]
    have e2 : (B.repr x) 2 = ⟪b2, x⟫ := by rw [B.repr_apply_apply, hB2]
    simp only [mem_inter_iff, mem_setOf_eq, mem_preimage, mem_ball_zero_iff, hn, e1, e2]
    constructor
    · rintro ⟨⟨s, t, r, hs, ht, rfl⟩, hball⟩
      have hx1 : ⟪b1, s • (np • b1) + t • ((nq * Real.cos psi) • b1 + (nq * Real.sin psi) • b2)
            + r • a⟫ = s * np + t * (nq * Real.cos psi) := by
        simp only [inner_add_right, real_inner_smul_right, hb1b1, hb12, hb1a]
        ring
      have hx2 : ⟪b2, s • (np • b1) + t • ((nq * Real.cos psi) • b1 + (nq * Real.sin psi) • b2)
            + r • a⟫ = t * (nq * Real.sin psi) := by
        simp only [inner_add_right, real_inner_smul_right, hb2b1, hb2b2, hb2a]
        ring
      refine ⟨hball, ?_, ?_⟩
      · rw [hx2]; positivity
      · rw [hx1, hx2]
        have hid : (s * np + t * (nq * Real.cos psi)) * Real.sin psi
            - t * (nq * Real.sin psi) * Real.cos psi = s * np * Real.sin psi := by ring
        rw [hid]; positivity
    · rintro ⟨hball, h2, h3⟩
      refine ⟨⟨(⟪b1, x⟫ * Real.sin psi - ⟪b2, x⟫ * Real.cos psi) / (np * Real.sin psi),
          ⟪b2, x⟫ / (nq * Real.sin psi), ⟪a, x⟫,
          div_nonneg h3 (by positivity), div_nonneg h2 (by positivity), ?_⟩, hball⟩
      conv_lhs => rw [← hsum x]
      match_scalars
      all_goals (field_simp; try ring)
  rw [hsets, (B.measurePreserving_repr).measure_preimage
      (measurableSet_wedge_std psi).nullMeasurableSet, volume_wedge_std psi h0 hpi]

/-- The volume of a solid wedge inside the unit ball: given a unit vector `a` (the axis)
and two linearly independent vectors `p q` orthogonal to `a`, the wedge is the set of
points `s • p + t • q + r • a` with `s, t ≥ 0`.  Its volume is `2/3` times the dihedral
angle, which is the angle between `p` and `q`. -/
