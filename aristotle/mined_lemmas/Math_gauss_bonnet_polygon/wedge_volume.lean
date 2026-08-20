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

theorem wedge_volume (u v : E3) (hu : u ≠ 0) (hne : ∀ r : ℝ, v ≠ r • u) :
    volume (ball (0 : E3) 1 ∩ {x | 0 ≤ inner ℝ u x} ∩ {x | 0 ≤ inner ℝ v x})
      = ENNReal.ofReal (2 / 3 * (π - InnerProductGeometry.angle u v)) := by
  have hv : v ≠ 0 := by simpa using hne 0
  have hnu : (0 : ℝ) < ‖u‖ := norm_pos_iff.2 hu
  have hnv : (0 : ℝ) < ‖v‖ := norm_pos_iff.2 hv
  set θ := InnerProductGeometry.angle u v with hθ
  have hθ0 : 0 < θ := lt_of_le_of_ne (InnerProductGeometry.angle_nonneg u v) fun h => by
    obtain ⟨-, r, -, hr⟩ := InnerProductGeometry.angle_eq_zero_iff.1 h.symm
    exact hne r hr
  have hθπ : θ < π := lt_of_le_of_ne (InnerProductGeometry.angle_le_pi u v) fun h => by
    obtain ⟨-, r, -, hr⟩ := InnerProductGeometry.angle_eq_pi_iff.1 h
    exact hne r hr
  set e0 : E3 := ‖u‖⁻¹ • u with he0def
  have he0 : ‖e0‖ = 1 := by
    rw [he0def, norm_smul]; simp [inv_mul_cancel₀ (ne_of_gt hnu)]
  set c : ℝ := inner ℝ e0 v with hcdef
  have hc : c = ‖v‖ * cos θ := by
    rw [hcdef, he0def, real_inner_smul_left, hθ, InnerProductGeometry.cos_angle]
    field_simp
  set w : E3 := v - c • e0 with hwdef
  have hwnorm : ‖w‖ = ‖v‖ * sin θ := by
    have hsin : 0 ≤ sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0.le hθπ.le
    have h1 : ‖w‖ ^ 2 = ‖v‖ ^ 2 - c ^ 2 := by
      have h : (inner ℝ v e0 : ℝ) = c := by rw [real_inner_comm]
      rw [hwdef, norm_sub_sq_real, real_inner_smul_right, norm_smul, he0, h]
      simp only [Real.norm_eq_abs, mul_one, sq_abs]
      ring
    have h2 : ‖v‖ ^ 2 - c ^ 2 = (‖v‖ * sin θ) ^ 2 := by
      rw [hc]
      have := Real.sin_sq_add_cos_sq θ
      nlinarith
    nlinarith [norm_nonneg w, mul_nonneg hnv.le hsin, h1, h2]
  have hwpos : (0 : ℝ) < ‖w‖ := by
    rw [hwnorm]; exact mul_pos hnv (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ)
  have hwne : w ≠ 0 := norm_pos_iff.1 hwpos
  set e1 : E3 := ‖w‖⁻¹ • w with he1def
  have he1 : ‖e1‖ = 1 := by
    rw [he1def, norm_smul]; simp [inv_mul_cancel₀ (ne_of_gt hwpos)]
  have h01 : inner ℝ e0 e1 = (0 : ℝ) := by
    rw [he1def, real_inner_smul_right, hwdef, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, he0]
    simp [hcdef]
  obtain ⟨b, hb0, hb1⟩ : ∃ b : OrthonormalBasis (Fin 3) ℝ E3, b 0 = e0 ∧ b 1 = e1 := by
    have horth : Orthonormal ℝ (({0, 1} : Set (Fin 3)).restrict ![e0, e1, 0]) := by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
      have h10 : inner ℝ e1 e0 = (0 : ℝ) := by rw [real_inner_comm]; exact h01
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
        simp [Set.restrict, he0, he1, h01, h10, Subtype.ext_iff]
    obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq
      (by simp : Module.finrank ℝ E3 = Fintype.card (Fin 3))
    exact ⟨b, by simpa using hb 0 (by simp), by simpa using hb 1 (by simp)⟩
  set R := b.repr with hR
  have hR0 : ∀ x : E3, (R x) 0 = ‖u‖⁻¹ * inner ℝ u x := by
    intro x
    rw [hR, OrthonormalBasis.repr_apply_apply, hb0, he0def, real_inner_smul_left]
  have hR1 : ∀ x : E3, (R x) 1 = ‖w‖⁻¹ * (inner ℝ v x - c * (inner ℝ e0 x)) := by
    intro x
    rw [hR, OrthonormalBasis.repr_apply_apply, hb1, he1def, real_inner_smul_left, hwdef,
      inner_sub_left, real_inner_smul_left]
  have hui : (0 : ℝ) < ‖u‖⁻¹ := inv_pos.2 hnu
  have hvi : (0 : ℝ) < ‖v‖⁻¹ := inv_pos.2 hnv
  have hpre : (ball (0 : E3) 1 ∩ {x | 0 ≤ inner ℝ u x} ∩ {x | 0 ≤ inner ℝ v x})
      = R ⁻¹' {y : E3 | ‖y‖ < 1 ∧ 0 ≤ y 0 ∧ 0 ≤ cos θ * y 0 + sin θ * y 1} := by
    ext x
    have key : cos θ * (‖u‖⁻¹ * inner ℝ u x) +
        sin θ * (‖w‖⁻¹ * (inner ℝ v x - c * inner ℝ e0 x)) = ‖v‖⁻¹ * inner ℝ v x := by
      have hie0 : (inner ℝ e0 x : ℝ) = ‖u‖⁻¹ * inner ℝ u x := by
        rw [he0def, real_inner_smul_left]
      have hs : sin θ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ)
      rw [hie0, hwnorm, hc]
      field_simp
      ring
    simp only [mem_inter_iff, mem_ball_zero_iff, mem_setOf_eq, mem_preimage,
      R.norm_map x, hR0 x, hR1 x, and_assoc, key, mul_nonneg_iff_of_pos_left hui,
      mul_nonneg_iff_of_pos_left hvi]
  have hAmeas : MeasurableSet {y : E3 | ‖y‖ < 1 ∧ 0 ≤ y 0 ∧ 0 ≤ cos θ * y 0 + sin θ * y 1} := by
    have : {y : E3 | ‖y‖ < 1 ∧ 0 ≤ y 0 ∧ 0 ≤ cos θ * y 0 + sin θ * y 1} =
        {y : E3 | ‖y‖ < 1} ∩ ({y : E3 | 0 ≤ y 0} ∩ {y : E3 | 0 ≤ cos θ * y 0 + sin θ * y 1}) := by
      ext y; simp
    rw [this]
    exact (measurableSet_lt (by fun_prop) measurable_const).inter
      ((measurableSet_le measurable_const (by fun_prop)).inter
        (measurableSet_le measurable_const (by fun_prop)))
  rw [hpre, (LinearIsometryEquiv.measurePreserving R).measure_preimage hAmeas.nullMeasurableSet,
    std_wedge_volume θ hθ0.le hθπ]

end Math

import Mathlib

/-!
# Area of a plane circular sector

This file computes the Lebesgue measure of a plane sector
`{p | ‖p‖² < s ∧ 0 ≤ p.1 ∧ 0 ≤ cos θ * p.1 + sin θ * p.2}`, the intersection of a disc of
squared radius `s` with two half-planes whose bounding lines meet at an angle `π - θ`.
-/

open MeasureTheory Metric Set Real

namespace Math

/-- Characterisation of the angular sector cut out by two half planes. -/
