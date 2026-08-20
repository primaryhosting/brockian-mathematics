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

theorem std_wedge_volume (θ : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ < π) :
    volume {x : E3 | ‖x‖ < 1 ∧ 0 ≤ x 0 ∧ 0 ≤ cos θ * x 0 + sin θ * x 1}
      = ENNReal.ofReal (2 / 3 * (π - θ)) := by
  have hpi := Real.pi_pos
  set B : Set (ℝ × (ℝ × ℝ)) := {q : ℝ × (ℝ × ℝ) | q.2.1 ^ 2 + q.2.2 ^ 2 + q.1 ^ 2 < 1 ∧
    0 ≤ q.2.1 ∧ 0 ≤ cos θ * q.2.1 + sin θ * q.2.2} with hB
  have hBmeas : MeasurableSet B := by
    have : B = ({q : ℝ × (ℝ × ℝ) | q.2.1 ^ 2 + q.2.2 ^ 2 + q.1 ^ 2 < 1} ∩
        {q : ℝ × (ℝ × ℝ) | 0 ≤ q.2.1}) ∩
        {q : ℝ × (ℝ × ℝ) | 0 ≤ cos θ * q.2.1 + sin θ * q.2.2} := by
      ext q; simp [hB, and_assoc]
    rw [this]
    exact ((measurableSet_lt (by fun_prop) measurable_const).inter
      (measurableSet_le measurable_const (by fun_prop))).inter
      (measurableSet_le measurable_const (by fun_prop))
  have hpre : {x : E3 | ‖x‖ < 1 ∧ 0 ≤ x 0 ∧ 0 ≤ cos θ * x 0 + sin θ * x 1} = E3toProd ⁻¹' B := by
    ext x
    simp only [mem_setOf_eq, mem_preimage, hB, E3toProd_apply]
    rw [norm_lt_one_iff]
  rw [hpre, measurePreserving_E3toProd.measure_preimage hBmeas.nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_apply hBmeas]
  have hslice : ∀ z : ℝ, volume (Prod.mk z ⁻¹' B) = ENNReal.ofReal ((π - θ) / 2 * (1 - z ^ 2)) := by
    intro z
    have : Prod.mk z ⁻¹' B = {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1 - z ^ 2 ∧ 0 ≤ p.1 ∧
        0 ≤ cos θ * p.1 + sin θ * p.2} := by
      ext p
      simp only [hB, mem_preimage, mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, h2, h3⟩
    rw [this, sector_area θ hθ0 hθπ]
  simp_rw [hslice]
  rw [lintegral_one_sub_sq _ (by linarith)]
  congr 1
  ring

/-- The volume of the intersection of the unit ball with two half-spaces through the origin,
with inner normals `u` and `v`: it is `2/3` times the dihedral angle `π - angle u v`. -/
