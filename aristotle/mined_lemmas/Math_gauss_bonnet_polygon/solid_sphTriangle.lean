import RequestProject.GaussBonnet.WedgeGeneral
import RequestProject.GaussBonnet.Angle
import RequestProject.GaussBonnet.Girard

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

**Girard's theorem** (the Gauss–Bonnet theorem for a geodesic triangle on the unit sphere):
the sum of the three interior angles of a spherical triangle exceeds `π` by its area.
-/

open MeasureTheory Real InnerProductGeometry RealInnerProductSpace Metric

namespace Math

/-- The inward normal to the side `BC` of the spherical triangle `ABC`, normalised so that
`⟪A, nrm A B C⟫ = 1`. -/

theorem solid_sphTriangle (A B C : E3) (hind : LinearIndependent ℝ ![A, B, C]) :
    solid (sphTriangle A B C) = octantSet (nrm A B C) (nrm B C A) (nrm C A B) := by
  have hd := det_ne_zero A B C hind
  have hd2 : ⟪B, cross C A⟫ ≠ 0 := by rw [det_cyclic]; exact hd
  have hd3 : ⟪C, cross A B⟫ ≠ 0 := by rw [det_cyclic, det_cyclic]; exact hd
  obtain ⟨h1, h2, h3⟩ := inner_nrm A B C hd
  obtain ⟨k1, k2, k3⟩ := inner_nrm B C A hd2
  obtain ⟨l1, l2, l3⟩ := inner_nrm C A B hd3
  have key : ∀ x : E3, (∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ x = a • A + b • B + c • C) ↔
      (0 ≤ ⟪x, nrm A B C⟫ ∧ 0 ≤ ⟪x, nrm B C A⟫ ∧ 0 ≤ ⟪x, nrm C A B⟫) := by
    intro x
    constructor
    · rintro ⟨a, b, c, ha, hb, hc, rfl⟩
      simp only [inner_add_left, real_inner_smul_left, h1, h2, h3, k1, k2, k3, l1, l2, l3]
      exact ⟨by linarith, by linarith, by linarith⟩
    · rintro ⟨p, q, r⟩
      exact ⟨_, _, _, p, q, r, coords A B C hind x⟩
  ext x
  simp only [solid, octantSet, sphTriangle, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    rcases h with rfl | h
    · simp
    · have hx : x ≠ 0 := by rintro rfl; simp at h
      have hpos : 0 < ‖x‖⁻¹ := by
        have : ‖x‖ > 0 := norm_pos_iff.2 hx
        positivity
      obtain ⟨-, hmem⟩ := h
      have hthis := (key _).1 hmem
      simp only [real_inner_smul_left] at hthis
      refine ⟨?_, ?_, ?_⟩ <;> nlinarith [hthis.1, hthis.2.1, hthis.2.2]
  · rintro ⟨hn, hc⟩
    refine ⟨hn, ?_⟩
    by_cases hx : x = 0
    · exact Or.inl hx
    · right
      have hpos : 0 < ‖x‖⁻¹ := by
        have : ‖x‖ > 0 := norm_pos_iff.2 hx
        positivity
      refine ⟨by simp [norm_smul]; field_simp, ?_⟩
      apply (key _).2
      simp only [real_inner_smul_left]
      exact ⟨mul_nonneg hpos.le hc.1, mul_nonneg hpos.le hc.2.1, mul_nonneg hpos.le hc.2.2⟩

/-- The analytic core of Girard's theorem, in terms of the three (nonzero) normal vectors. -/
