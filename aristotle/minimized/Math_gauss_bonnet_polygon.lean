import RequestProject.Sector

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The volume of the standard solid wedge of dihedral angle `psi` inside the unit ball:
the axis of the wedge is the first coordinate axis, and the wedge is described in the plane
of the last two coordinates as the cone spanned by `(1,0)` and `(cos psi, sin psi)`. -/

theorem volume_wedge_std (psi : ℝ) (h0 : 0 ≤ psi) (hpi : psi ≤ π) :
    volume {y : E3 | ‖y‖ < 1 ∧ 0 ≤ y 2 ∧ 0 ≤ y 1 * Real.sin psi - y 2 * Real.cos psi}
      = ENNReal.ofReal (2 * psi / 3) := by
  set S : Set E3 := {y : E3 | ‖y‖ < 1 ∧ 0 ≤ y 2 ∧ 0 ≤ y 1 * Real.sin psi - y 2 * Real.cos psi}
    with hSdef
  set W : Set (ℝ × (Fin 2 → ℝ)) := {p | p.1 ^ 2 + (p.2 0) ^ 2 + (p.2 1) ^ 2 < 1 ∧ 0 ≤ p.2 1 ∧
      0 ≤ p.2 0 * Real.sin psi - p.2 1 * Real.cos psi} with hWdef
  have hSm : MeasurableSet S := by rw [hSdef]; measurability
  have hWm : MeasurableSet W := by rw [hWdef]; measurability
  -- transfer the problem to `ℝ × (Fin 2 → ℝ)`, splitting off the axis coordinate
  have h1 : volume S = volume ((WithLp.toLp 2 : (Fin 3 → ℝ) → E3) ⁻¹' S) :=
    ((PiLp.volume_preserving_toLp (Fin 3)).measure_preimage hSm.nullMeasurableSet).symm
  have h2 : ((WithLp.toLp 2 : (Fin 3 → ℝ) → E3) ⁻¹' S)
      = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0) ⁻¹' W := by
    ext y
    have hnorm : ‖(WithLp.toLp 2 y : E3)‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      simp [Fin.sum_univ_three]
    have hlt : ‖(WithLp.toLp 2 y : E3)‖ < 1 ↔ y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 < 1 := by
      constructor
      · intro hh; nlinarith [norm_nonneg (WithLp.toLp 2 y : E3)]
      · intro hh; nlinarith [norm_nonneg (WithLp.toLp 2 y : E3)]
    simp only [mem_preimage, hSdef, hWdef, mem_setOf_eq, hlt]
    rfl
  have h3 : volume ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0) ⁻¹' W) = volume W :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).measure_preimage
      hWm.nullMeasurableSet
  -- each horizontal slice is a circular sector
  have hslice : ∀ t : ℝ, volume (Prod.mk t ⁻¹' W) = ENNReal.ofReal (psi * (1 - t ^ 2) / 2) := by
    intro t
    rcases le_or_gt (t ^ 2) 1 with hle | hgt
    · have hrho : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by linarith)
      have hset : Prod.mk t ⁻¹' W = (MeasurableEquiv.finTwoArrow) ⁻¹'
          {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 < Real.sqrt (1 - t ^ 2) ^ 2 ∧ 0 ≤ z.2 ∧
            0 ≤ z.1 * Real.sin psi - z.2 * Real.cos psi} := by
        ext z
        show (t ^ 2 + (z 0) ^ 2 + (z 1) ^ 2 < 1 ∧ 0 ≤ z 1 ∧
            0 ≤ z 0 * Real.sin psi - z 1 * Real.cos psi) ↔
          ((z 0) ^ 2 + (z 1) ^ 2 < Real.sqrt (1 - t ^ 2) ^ 2 ∧ 0 ≤ z 1 ∧
            0 ≤ z 0 * Real.sin psi - z 1 * Real.cos psi)
        rw [hrho]
        constructor
        · rintro ⟨ha, hb, hc⟩; exact ⟨by linarith, hb, hc⟩
        · rintro ⟨ha, hb, hc⟩; exact ⟨by linarith, hb, hc⟩
      rw [hset, (volume_preserving_finTwoArrow ℝ).measure_preimage (by measurability),
        volume_sector psi _ h0 hpi (Real.sqrt_nonneg _), hrho]
    · have hempty : Prod.mk t ⁻¹' W = ∅ := by
        ext z
        simp only [mem_preimage, hWdef, mem_setOf_eq, mem_empty_iff_false, iff_false]
        rintro ⟨ha, -, -⟩
        nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
      rw [hempty, measure_empty, eq_comm, ENNReal.ofReal_eq_zero]
      have hneg : 1 - t ^ 2 ≤ 0 := by nlinarith
      have := mul_nonneg h0 (neg_nonneg.2 hneg)
      linarith
  rw [h1, h2, h3, Measure.volume_eq_prod, Measure.prod_apply hWm]
  simp only [hslice]
  -- integrate the slice areas
  have hfun : (fun t : ℝ => ENNReal.ofReal (psi * (1 - t ^ 2) / 2))
      = (Icc (-1 : ℝ) 1).indicator (fun t => ENNReal.ofReal (psi * (1 - t ^ 2) / 2)) := by
    funext t
    by_cases ht : t ∈ Icc (-1 : ℝ) 1
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, ENNReal.ofReal_eq_zero]
      simp only [mem_Icc, not_and_or, not_le] at ht
      have hneg : 1 - t ^ 2 ≤ 0 := by rcases ht with hh | hh <;> nlinarith
      have := mul_nonneg h0 (neg_nonneg.2 hneg)
      linarith
  rw [hfun, lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    congr 1
    simp [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, mul_sub]
    ring
  · apply Continuous.integrableOn_Icc; fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    simp only [mem_Icc] at hy
    show (0 : ℝ) ≤ psi * (1 - y ^ 2) / 2
    have hpos : 0 ≤ 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
    have := mul_nonneg h0 hpos
    linarith

theorem measurableSet_wedge_std (psi : ℝ) :
    MeasurableSet {y : E3 | ‖y‖ < 1 ∧ 0 ≤ y 2 ∧
      0 ≤ y 1 * Real.sin psi - y 2 * Real.cos psi} := by measurability

/-- The angle between two linearly independent vectors lies strictly between `0` and `π`. -/

theorem sin_angle_pos (p q : E3) (hpq : LinearIndependent ℝ ![p, q]) :
    0 < Real.sin (angle p q) := by
  have hpq' := LinearIndependent.pair_iff.1 hpq
  refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
  · rcases (angle_nonneg p q).lt_or_eq with h | h
    · exact h
    · exfalso
      obtain ⟨-, r, hr, hqr⟩ := angle_eq_zero_iff.1 h.symm
      have := hpq' r (-1) (by rw [hqr]; module)
      linarith [this.2]
  · rcases (angle_le_pi p q).lt_or_eq with h | h
    · exact h
    · exfalso
      obtain ⟨-, r, hr, hqr⟩ := angle_eq_pi_iff.1 h
      have := hpq' r (-1) (by rw [hqr]; module)
      linarith [this.2]

/-- An orthonormal frame adapted to a wedge: `b1` is the direction of `p`, and `b2` is the
direction of the component of `q` orthogonal to `p`. -/

theorem wedge_frame (a p q : E3) (hp : ⟪a, p⟫ = 0) (hq : ⟪a, q⟫ = 0)
    (hpq : LinearIndependent ℝ ![p, q]) :
    ∃ b1 b2 : E3, ‖b1‖ = 1 ∧ ‖b2‖ = 1 ∧ ⟪a, b1⟫ = 0 ∧ ⟪a, b2⟫ = 0 ∧ ⟪b1, b2⟫ = 0 ∧
      p = ‖p‖ • b1 ∧
      q = (‖q‖ * Real.cos (angle p q)) • b1 + (‖q‖ * Real.sin (angle p q)) • b2 := by
  have hp0 : p ≠ 0 := hpq.ne_zero 0
  have hq0 : q ≠ 0 := hpq.ne_zero 1
  have hnp : 0 < ‖p‖ := norm_pos_iff.2 hp0
  have hnq : 0 < ‖q‖ := norm_pos_iff.2 hq0
  have hsin : 0 < Real.sin (angle p q) := sin_angle_pos p q hpq
  obtain ⟨b1, hb1def⟩ : ∃ v : E3, v = ‖p‖⁻¹ • p := ⟨_, rfl⟩
  have hb1 : ‖b1‖ = 1 := by
    rw [hb1def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnp.ne']
  have hb1b1 : ⟪b1, b1⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hb1]; norm_num
  have hab1 : ⟪a, b1⟫ = (0 : ℝ) := by rw [hb1def, real_inner_smul_right, hp, mul_zero]
  have hpb1 : p = ‖p‖ • b1 := by
    rw [hb1def, smul_smul, mul_inv_cancel₀ hnp.ne', one_smul]
  have hc : ⟪b1, q⟫ = ‖q‖ * Real.cos (angle p q) := by
    rw [hb1def, real_inner_smul_left, ← cos_angle_mul_norm_mul_norm p q]
    field_simp
  have hc' : ⟪q, b1⟫ = ‖q‖ * Real.cos (angle p q) := by rw [real_inner_comm]; exact hc
  obtain ⟨w, hwdef⟩ : ∃ v : E3, v = q - (‖q‖ * Real.cos (angle p q)) • b1 := ⟨_, rfl⟩
  have hb1w : ⟪b1, w⟫ = (0 : ℝ) := by
    rw [hwdef, inner_sub_right, hc, real_inner_smul_right, hb1b1]; ring
  have haw : ⟪a, w⟫ = (0 : ℝ) := by
    rw [hwdef, inner_sub_right, hq, real_inner_smul_right, hab1]; ring
  have hww : ⟪w, w⟫ = ‖q‖ ^ 2 * (Real.sin (angle p q)) ^ 2 := by
    have hqq : ⟪q, q⟫ = ‖q‖ ^ 2 := real_inner_self_eq_norm_sq q
    rw [hwdef]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hc, hc', hb1b1, hqq]
    have := Real.sin_sq_add_cos_sq (angle p q)
    nlinarith
  have hnw : ‖w‖ = ‖q‖ * Real.sin (angle p q) := by
    have h1 : ‖w‖ ^ 2 = (‖q‖ * Real.sin (angle p q)) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hww]; ring
    have hnn : 0 ≤ ‖q‖ * Real.sin (angle p q) := by positivity
    nlinarith [norm_nonneg w]
  have hnw0 : 0 < ‖w‖ := by rw [hnw]; positivity
  obtain ⟨b2, hb2def⟩ : ∃ v : E3, v = ‖w‖⁻¹ • w := ⟨_, rfl⟩
  refine ⟨b1, b2, hb1, ?_, hab1, ?_, ?_, hpb1, ?_⟩
  · rw [hb2def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnw0.ne']
  · rw [hb2def, real_inner_smul_right, haw, mul_zero]
  · rw [hb2def, real_inner_smul_right, hb1w, mul_zero]
  · rw [← hnw, hb2def, smul_smul, mul_inv_cancel₀ hnw0.ne', one_smul, hwdef]
    abel

/-- The volume of a solid wedge inside the unit ball, in terms of an adapted orthonormal
frame `a, b1, b2`. -/

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

theorem volume_wedge (a p q : E3) (ha : ‖a‖ = 1) (hp : ⟪a, p⟫ = 0) (hq : ⟪a, q⟫ = 0)
    (hpq : LinearIndependent ℝ ![p, q]) :
    volume ({x : E3 | ∃ s t r : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ x = s • p + t • q + r • a} ∩ ball 0 1)
      = ENNReal.ofReal (2 * angle p q / 3) := by
  obtain ⟨b1, b2, hb1, hb2, hab1, hab2, hb12, hpb, hqb⟩ := wedge_frame a p q hp hq hpq
  have hnp : 0 < ‖p‖ := norm_pos_iff.2 (hpq.ne_zero 0)
  have hnq : 0 < ‖q‖ := norm_pos_iff.2 (hpq.ne_zero 1)
  have hsin : 0 < Real.sin (angle p q) := sin_angle_pos p q hpq
  have hset : {x : E3 | ∃ s t r : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ x = s • p + t • q + r • a}
      = {x : E3 | ∃ s t r : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ x = s • (‖p‖ • b1) +
          t • ((‖q‖ * Real.cos (angle p q)) • b1 + (‖q‖ * Real.sin (angle p q)) • b2)
          + r • a} := by
    conv_lhs => rw [hpb, hqb]
  rw [hset]
  exact volume_wedge_of_frame a b1 b2 (angle p q) ‖p‖ ‖q‖ ha hb1 hb2 hab1 hab2 hb12 hnp hnq
    (angle_nonneg p q) (angle_le_pi p q) hsin

end Math

import Mathlib

open MeasureTheory Set Real
open scoped ENNReal

namespace Math

/-- The measure of the intersection of `Ioo (-π) π` with `Icc 0 psi`, for `0 ≤ psi ≤ π`. -/

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

theorem volume_sector (psi rho : ℝ) (h0 : 0 ≤ psi) (hpi : psi ≤ π) (hr : 0 ≤ rho) :
    volume {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 < rho ^ 2 ∧ 0 ≤ z.2 ∧
        0 ≤ z.1 * Real.sin psi - z.2 * Real.cos psi} = ENNReal.ofReal (psi * rho ^ 2 / 2) := by
  set S : Set (ℝ × ℝ) := {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 < rho ^ 2 ∧ 0 ≤ z.2 ∧
        0 ≤ z.1 * Real.sin psi - z.2 * Real.cos psi} with hS
  have hSm : MeasurableSet S := by rw [hS]; measurability
  have hAm : MeasurableSet (polarCoord.symm ⁻¹' S) :=
    hSm.preimage continuous_polarCoord_symm.measurable
  -- pass to polar coordinates
  have key := lintegral_comp_polarCoord_symm (S.indicator (1 : ℝ × ℝ → ℝ≥0∞))
  rw [lintegral_indicator_one hSm] at key
  have hpre : ∀ p : ℝ × ℝ, S.indicator (1 : ℝ × ℝ → ℝ≥0∞) (polarCoord.symm p)
      = (polarCoord.symm ⁻¹' S).indicator (1 : ℝ × ℝ → ℝ≥0∞) p := by
    intro p
    by_cases hp : polarCoord.symm p ∈ S
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (Set.mem_preimage.2 hp)]; rfl
    · rw [Set.indicator_of_notMem hp,
        Set.indicator_of_notMem (fun hc => hp (Set.mem_preimage.1 hc))]
  have step : ∫⁻ (p : ℝ × ℝ) in polarCoord.target, ENNReal.ofReal p.1 •
      S.indicator (1 : ℝ × ℝ → ℝ≥0∞) (polarCoord.symm p)
      = ∫⁻ p in (polarCoord.symm ⁻¹' S) ∩ polarCoord.target, ENNReal.ofReal p.1 := by
    simp only [hpre, smul_eq_mul]
    rw [show (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * (polarCoord.symm ⁻¹' S).indicator 1 p)
        = (polarCoord.symm ⁻¹' S).indicator (fun p : ℝ × ℝ => ENNReal.ofReal p.1) from ?_]
    · rw [lintegral_indicator hAm, Measure.restrict_restrict hAm]
    · funext p
      by_cases hp : p ∈ (polarCoord.symm ⁻¹' S) <;> simp [hp]
  -- the polar preimage of the sector is a rectangle
  have hregion : (polarCoord.symm ⁻¹' S) ∩ polarCoord.target
      = (Ioo 0 rho) ×ˢ (Ioo (-π) π ∩ Icc 0 psi) := by
    ext ⟨r, phi⟩
    simp only [polarCoord_target, polarCoord_symm_apply, mem_inter_iff, mem_prod, mem_Ioi,
      mem_Ioo, mem_Icc, mem_preimage, hS, mem_setOf_eq]
    constructor
    · rintro ⟨⟨hball, hsin, hsec⟩, hr0, hphi1, hphi2⟩
      have hsq : (r * cos phi) ^ 2 + (r * sin phi) ^ 2 = r ^ 2 := by
        have := sin_sq_add_cos_sq phi; nlinarith
      rw [hsq] at hball
      have hrlt : r < rho := by nlinarith
      have hsin' : 0 ≤ sin phi := nonneg_of_mul_nonneg_right hsin hr0
      have hphi0 : 0 ≤ phi := by
        by_contra hc
        push_neg at hc
        exact absurd hsin' (not_le.2 (sin_neg_of_neg_of_neg_pi_lt hc hphi1))
      have hsec' : 0 ≤ sin (psi - phi) := by
        have hexp : r * sin (psi - phi) = r * cos phi * sin psi - r * sin phi * cos psi := by
          rw [Real.sin_sub]; ring
        nlinarith [hsec]
      have hle : phi ≤ psi := by
        by_contra hc
        push_neg at hc
        exact absurd hsec' (not_le.2 (sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)))
      exact ⟨⟨hr0, hrlt⟩, ⟨hphi1, hphi2⟩, hphi0, hle⟩
    · rintro ⟨⟨hr0, hrlt⟩, ⟨hphi1, hphi2⟩, hphi0, hle⟩
      have hsq : (r * cos phi) ^ 2 + (r * sin phi) ^ 2 = r ^ 2 := by
        have := sin_sq_add_cos_sq phi; nlinarith
      have hsin' : 0 ≤ sin phi := sin_nonneg_of_nonneg_of_le_pi hphi0 (by linarith)
      have hsec' : 0 ≤ sin (psi - phi) :=
        sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      refine ⟨⟨by rw [hsq]; nlinarith, by positivity, ?_⟩, hr0, hphi1, hphi2⟩
      have hexp : r * sin (psi - phi) = r * cos phi * sin psi - r * sin phi * cos psi := by
        rw [Real.sin_sub]; ring
      nlinarith
  -- compute the resulting integral over the rectangle
  rw [← key, step, hregion, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod _ (by fun_prop)]
  simp only [setLIntegral_const, volume_angle_interval psi hpi]
  rw [lintegral_mul_const _ (by fun_prop)]
  have hradial : ∫⁻ x in Ioo (0 : ℝ) rho, ENNReal.ofReal x = ENNReal.ofReal (rho ^ 2 / 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr, integral_id]
      norm_num
    · exact ((continuous_id).integrableOn_Icc).mono_set Ioo_subset_Icc_self
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy using hy.1.le
  rw [hradial, ← ENNReal.ofReal_mul (by positivity)]
  ring_nf

end Math

import RequestProject.Wedge

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace Pointwise

namespace Math

/-! ## Definitions -/

/-- The (surface) area of a subset `S` of the unit sphere of `ℝ³`, defined as three times
the Lebesgue measure of the solid cone `{t • x : 0 < t < 1, x ∈ S}` that it subtends.
This is the standard surface measure; see `Math.sphericalArea_eq_toSphere`. -/

noncomputable def sphericalArea (S : Set E3) : ℝ := 3 * (volume (Ioo (0 : ℝ) 1 • S)).toReal

/-- The geodesic (spherical) triangle with vertices `u`, `v`, `w` on the unit sphere: the
points of the sphere lying in the convex cone spanned by `u`, `v` and `w`. -/

def sphericalTriangle (u v w : E3) : Set E3 :=
  {x | ‖x‖ = 1 ∧ ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ x = a • u + b • v + c • w}

/-- The angle at the vertex `p` of the geodesic triangle with vertices `p`, `a`, `b`: the
angle between the initial velocities at `p` of the geodesics from `p` to `a` and from `p`
to `b`, i.e. between the projections of `a` and `b` to the tangent space at `p`. -/

noncomputable def sphAngle (p a b : E3) : ℝ :=
  angle (a - ⟪p, a⟫ • p) (b - ⟪p, b⟫ • p)

/-! ## Auxiliary lemmas -/

/-- Coordinates with respect to three linearly independent vectors of `ℝ³`. -/

theorem coords (u v w : E3) (hind : LinearIndependent ℝ ![u, v, w]) :
    ∃ f g h : E3 →ₗ[ℝ] ℝ,
      (∀ x : E3, (f x) • u + (g x) • v + (h x) • w = x) ∧
      (∀ a b c : ℝ, f (a • u + b • v + c • w) = a) ∧
      (∀ a b c : ℝ, g (a • u + b • v + c • w) = b) ∧
      (∀ a b c : ℝ, h (a • u + b • v + c • w) = c) := by
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ E3 := by simp
  set B : Module.Basis (Fin 3) ℝ E3 := basisOfLinearIndependentOfCardEqFinrank hind hcard with hBdef
  have hB : ⇑B = ![u, v, w] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have h0 : B 0 = u := by rw [hB]; rfl
  have h1 : B 1 = v := by rw [hB]; rfl
  have h2 : B 2 = w := by rw [hB]; rfl
  refine ⟨B.coord 0, B.coord 1, B.coord 2, ?_, ?_, ?_, ?_⟩
  · intro x
    have := B.sum_repr x
    rw [Fin.sum_univ_three, h0, h1, h2] at this
    simpa [Module.Basis.coord_apply] using this
  all_goals
    intro a b c
    simp [Module.Basis.coord_apply, ← h0, ← h1, ← h2, Module.Basis.repr_self]

theorem measurableSet_halfspace (k : E3 →ₗ[ℝ] ℝ) : MeasurableSet {x : E3 | 0 ≤ k x} :=
  measurableSet_le measurable_const (k.continuous_of_finiteDimensional).measurable

/-- A nonzero linear functional splits any measurable set into two halves. -/

theorem volume_split (A : Set E3) (hA : MeasurableSet A) (k : E3 →ₗ[ℝ] ℝ) (hk : k ≠ 0) :
    volume A = volume (A ∩ {x | 0 ≤ k x}) + volume (A ∩ {x | 0 ≤ (-k) x}) := by
  have hnull : volume ((A ∩ {x : E3 | 0 ≤ k x}) ∩ (A ∩ {x : E3 | 0 ≤ (-k) x})) = 0 := by
    refine measure_mono_null (fun x hx => ?_)
      (Measure.addHaar_submodule volume (LinearMap.ker k) ?_)
    · simp only [mem_inter_iff, mem_setOf_eq, LinearMap.neg_apply] at hx
      exact SetLike.mem_coe.2 (LinearMap.mem_ker.2 (le_antisymm (by linarith [hx.2.2]) hx.1.2))
    · intro hker
      exact hk (by ext x; exact LinearMap.mem_ker.1 (hker ▸ Submodule.mem_top))
  have hsplit := measure_union_add_inter (μ := volume) (A ∩ {x : E3 | 0 ≤ k x})
    (hA.inter (measurableSet_halfspace (-k)))
  rw [hnull, add_zero] at hsplit
  rw [← hsplit]
  congr 1
  ext x
  simp only [mem_union, mem_inter_iff, mem_setOf_eq, LinearMap.neg_apply]
  constructor
  · intro hx
    rcases le_total 0 (k x) with hx' | hx'
    · exact Or.inl ⟨hx, hx'⟩
    · exact Or.inr ⟨hx, by linarith⟩
  · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx

theorem volume_ball_E3 : volume (ball (0 : E3) 1) = ENNReal.ofReal (4 * π / 3) := by
  rw [EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, one_pow, ENNReal.ofReal_one, one_mul]
  congr 1
  rw [show ((3 : ℕ) : ℝ) / 2 + 1 = 3 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq, show Real.sqrt π ^ 3 = π * Real.sqrt π by
      rw [pow_succ, Real.sq_sqrt Real.pi_nonneg]]
  have hpos : Real.sqrt π > 0 := Real.sqrt_pos.2 Real.pi_pos
  field_simp
  ring

theorem cone_subset_ball (S : Set E3) (hS : S ⊆ sphere 0 1) : Ioo (0 : ℝ) 1 • S ⊆ ball 0 1 := by
  rintro _ ⟨t, ht, x, hx, rfl⟩
  have hx1 : ‖x‖ = 1 := by simpa using hS hx
  simp [norm_smul, hx1, abs_of_pos ht.1, ht.2]

/-! ### Solid lunes and octants cut out by half spaces -/

/-- The solid lune of the unit ball determined by two linear functionals. -/

def lune (k l : E3 →ₗ[ℝ] ℝ) : Set E3 := ball 0 1 ∩ {x | 0 ≤ k x} ∩ {x | 0 ≤ l x}

/-- The solid octant of the unit ball determined by three linear functionals. -/

def octant (k l m : E3 →ₗ[ℝ] ℝ) : Set E3 := lune k l ∩ {x | 0 ≤ m x}

theorem octant_subset_ball (k l m : E3 →ₗ[ℝ] ℝ) : octant k l m ⊆ ball 0 1 :=
  fun _ hx => hx.1.1.1

theorem measurableSet_lune (k l : E3 →ₗ[ℝ] ℝ) : MeasurableSet (lune k l) :=
  ((measurableSet_ball).inter (measurableSet_halfspace k)).inter (measurableSet_halfspace l)

theorem volume_lune_split (k l m : E3 →ₗ[ℝ] ℝ) (hm : m ≠ 0) :
    volume (lune k l) = volume (octant k l m) + volume (octant k l (-m)) :=
  volume_split _ (measurableSet_lune k l) m hm

theorem octant_swap₂₃ (k l m : E3 →ₗ[ℝ] ℝ) : octant k l m = octant k m l := by
  ext x; simp only [octant, lune, mem_inter_iff, mem_setOf_eq]; tauto

theorem octant_swap₁₂ (k l m : E3 →ₗ[ℝ] ℝ) : octant k l m = octant l k m := by
  ext x; simp only [octant, lune, mem_inter_iff, mem_setOf_eq]; tauto

theorem volume_octant_neg (k l m : E3 →ₗ[ℝ] ℝ) :
    volume (octant (-k) (-l) (-m)) = volume (octant k l m) := by
  have : octant (-k) (-l) (-m) = (fun x : E3 => -x) ⁻¹' octant k l m := by
    ext x
    simp only [octant, lune, mem_inter_iff, mem_setOf_eq, mem_preimage, LinearMap.neg_apply,
      map_neg, mem_ball_zero_iff, norm_neg]
  rw [this, Measure.measure_preimage_neg]

/-- The volume of the solid lune cut out by the two half spaces spanned by `u, w` and by
`v, w`: it is `2/3` times the angle of the spherical triangle at the vertex `w`. -/

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

theorem sphericalArea_eq_toSphere (S : Set (sphere (0 : E3) 1)) (hS : MeasurableSet S) :
    ENNReal.ofReal (sphericalArea (Subtype.val '' S)) = volume.toSphere S := by
  have hsub : (Subtype.val '' S : Set E3) ⊆ sphere 0 1 := by
    rintro _ ⟨x, hx, rfl⟩; exact x.2
  have hfin : volume (Ioo (0 : ℝ) 1 • (Subtype.val '' S : Set E3)) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (cone_subset_ball _ hsub))
  rw [Measure.toSphere_apply' _ hS, sphericalArea, ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_toReal hfin]
  norm_num

/-! ## The Gauss-Bonnet theorem for a spherical triangle -/

/-- **Girard's theorem** (the Gauss-Bonnet theorem for a geodesic triangle on the unit
sphere): the sum of the angles of a geodesic triangle on the unit sphere exceeds `π` by
exactly the area of the triangle. -/

theorem gauss_bonnet_polygon (u v w : E3) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hind : LinearIndependent ℝ ![u, v, w]) :
    sphericalArea (sphericalTriangle u v w)
      = sphAngle u v w + sphAngle v u w + sphAngle w u v - π := by
  obtain ⟨f, g, h, hdec, hcf, hcg, hch⟩ := coords u v w hind
  -- the coordinate functionals are nonzero
  have hf0 : f ≠ 0 := by
    intro hcon; have := hcf 1 0 0; rw [hcon] at this; simp at this
  have hg0 : g ≠ 0 := by
    intro hcon; have := hcg 1 1 0; rw [hcon] at this; simp at this
  have hh0 : h ≠ 0 := by
    intro hcon; have := hch 1 1 1; rw [hcon] at this; simp at this
  have hfin : ∀ k l m : E3 →ₗ[ℝ] ℝ, volume (octant k l m) ≠ ⊤ := fun k l m =>
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (octant_subset_ball k l m))
  -- permuted linear independence
  have hind₂ : LinearIndependent ℝ ![u, w, v] := by
    have := hind.comp ![0, 2, 1] (by decide)
    convert this using 1
    funext i; fin_cases i <;> rfl
  have hind₃ : LinearIndependent ℝ ![v, w, u] := by
    have := hind.comp ![1, 2, 0] (by decide)
    convert this using 1
    funext i; fin_cases i <;> rfl
  -- the three lunes
  have hLfg : lune f g
      = {x : E3 | ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • u + b • v + c • w} ∩ ball 0 1 := by
    ext x
    simp only [lune, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨⟨hb, hx1⟩, hx2⟩
      exact ⟨⟨f x, g x, h x, hx1, hx2, (hdec x).symm⟩, hb⟩
    · rintro ⟨⟨a, b, c, ha, hb, rfl⟩, hball⟩
      exact ⟨⟨hball, by rw [hcf]; exact ha⟩, by rw [hcg]; exact hb⟩
  have hLfh : lune f h
      = {x : E3 | ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • u + b • w + c • v} ∩ ball 0 1 := by
    ext x
    simp only [lune, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨⟨hb, hx1⟩, hx2⟩
      refine ⟨⟨f x, h x, g x, hx1, hx2, ?_⟩, hb⟩
      conv_lhs => rw [← hdec x]
      abel
    · rintro ⟨⟨a, b, c, ha, hb, rfl⟩, hball⟩
      have he : a • u + b • w + c • v = a • u + c • v + b • w := by abel
      rw [he]
      exact ⟨⟨by rwa [he] at hball, by rw [hcf]; exact ha⟩, by rw [hch]; exact hb⟩
  have hLgh : lune g h
      = {x : E3 | ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • v + b • w + c • u} ∩ ball 0 1 := by
    ext x
    simp only [lune, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨⟨hb, hx1⟩, hx2⟩
      refine ⟨⟨g x, h x, f x, hx1, hx2, ?_⟩, hb⟩
      conv_lhs => rw [← hdec x]
      abel
    · rintro ⟨⟨a, b, c, ha, hb, rfl⟩, hball⟩
      have he : a • v + b • w + c • u = c • u + a • v + b • w := by abel
      rw [he]
      exact ⟨⟨by rwa [he] at hball, by rw [hcg]; exact ha⟩, by rw [hch]; exact hb⟩
  have hvLfg : volume (lune f g) = ENNReal.ofReal (2 * sphAngle w u v / 3) := by
    rw [hLfg]; exact lune_volume u v w hw hind
  have hvLfh : volume (lune f h) = ENNReal.ofReal (2 * sphAngle v u w / 3) := by
    rw [hLfh]; exact lune_volume u w v hv hind₂
  have hvLgh : volume (lune g h) = ENNReal.ofReal (2 * sphAngle u v w / 3) := by
    rw [hLgh]; exact lune_volume v w u hu hind₃
  -- splitting a lune into two octants, in real form
  have hsplitR : ∀ (k l m : E3 →ₗ[ℝ] ℝ) (θ : ℝ), m ≠ 0 → 0 ≤ θ →
      volume (lune k l) = ENNReal.ofReal θ →
      (volume (octant k l m)).toReal + (volume (octant k l (-m))).toReal = θ := by
    intro k l m θ hm hθ hlv
    have hsp := volume_lune_split k l m hm
    rw [hlv] at hsp
    have := congrArg ENNReal.toReal hsp.symm
    rwa [ENNReal.toReal_add (hfin _ _ _) (hfin _ _ _), ENNReal.toReal_ofReal hθ] at this
  have hang₁ : 0 ≤ sphAngle u v w := angle_nonneg _ _
  have hang₂ : 0 ≤ sphAngle v u w := angle_nonneg _ _
  have hang₃ : 0 ≤ sphAngle w u v := angle_nonneg _ _
  have e₁ := hsplitR f g h _ hh0 (by linarith) hvLfg
  have e₂ := hsplitR f h g _ hg0 (by linarith) hvLfh
  have e₃ := hsplitR g h f _ hf0 (by linarith) hvLgh
  -- reorder the octants appearing in `e₂` and `e₃`
  rw [octant_swap₂₃ f h g, octant_swap₂₃ f h (-g)] at e₂
  rw [octant_swap₂₃ g h f, octant_swap₁₂ g f h, octant_swap₂₃ g h (-f),
    octant_swap₁₂ g (-f) h] at e₃
  -- the total volume of the ball is the sum of the eight octants
  have htot : volume (ball (0 : E3) 1)
      = (volume (octant f g h) + volume (octant f g (-h)))
        + (volume (octant f (-g) h) + volume (octant f (-g) (-h)))
        + ((volume (octant (-f) g h) + volume (octant (-f) g (-h)))
          + (volume (octant (-f) (-g) h) + volume (octant (-f) (-g) (-h)))) := by
    have h1 : volume (ball (0 : E3) 1)
        = volume (ball (0 : E3) 1 ∩ {x | 0 ≤ f x}) + volume (ball (0 : E3) 1 ∩ {x | 0 ≤ (-f) x}) :=
      volume_split _ measurableSet_ball f hf0
    have h2 : volume (ball (0 : E3) 1 ∩ {x | 0 ≤ f x})
        = volume (lune f g) + volume (lune f (-g)) :=
      volume_split _ (measurableSet_ball.inter (measurableSet_halfspace f)) g hg0
    have h3 : volume (ball (0 : E3) 1 ∩ {x | 0 ≤ (-f) x})
        = volume (lune (-f) g) + volume (lune (-f) (-g)) :=
      volume_split _ (measurableSet_ball.inter (measurableSet_halfspace (-f))) g hg0
    rw [h1, h2, h3, volume_lune_split f g h hh0, volume_lune_split f (-g) h hh0,
      volume_lune_split (-f) g h hh0, volume_lune_split (-f) (-g) h hh0]
  -- the antipodal symmetry
  have a₁ := congrArg ENNReal.toReal (volume_octant_neg f g h)
  have a₂ := congrArg ENNReal.toReal (volume_octant_neg f g (-h))
  have a₃ := congrArg ENNReal.toReal (volume_octant_neg f (-g) h)
  have a₄ := congrArg ENNReal.toReal (volume_octant_neg (-f) g h)
  simp only [neg_neg] at a₂ a₃ a₄
  -- convert the total volume identity to real numbers
  have htotR : (volume (octant f g h)).toReal + (volume (octant f g (-h))).toReal
      + ((volume (octant f (-g) h)).toReal + (volume (octant f (-g) (-h))).toReal)
      + (((volume (octant (-f) g h)).toReal + (volume (octant (-f) g (-h))).toReal)
        + ((volume (octant (-f) (-g) h)).toReal + (volume (octant (-f) (-g) (-h))).toReal))
      = 4 * π / 3 := by
    rw [volume_ball_E3] at htot
    have hres := congrArg ENNReal.toReal htot.symm
    rw [ENNReal.toReal_ofReal (by positivity)] at hres
    rw [← hres]
    simp only [ENNReal.toReal_add, hfin, ENNReal.add_ne_top, and_self, ne_eq, not_false_eq_true]
  -- identify the area of the triangle with the volume of the octant
  have hT : Ioo (0 : ℝ) 1 • sphericalTriangle u v w = octant f g h \ {0} := by
    ext y
    constructor
    · rintro ⟨t, ht, x, ⟨hx1, a, b, c, ha, hb, hc, rfl⟩, rfl⟩
      have hnorm : ‖t • (a • u + b • v + c • w)‖ = t := by
        rw [norm_smul, hx1, Real.norm_eq_abs, abs_of_pos ht.1, mul_one]
      refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · exact mem_ball_zero_iff.2 (by rw [hnorm]; exact ht.2)
      · show 0 ≤ f _
        rw [map_smul, hcf, smul_eq_mul]
        exact mul_nonneg ht.1.le ha
      · show 0 ≤ g _
        rw [map_smul, hcg, smul_eq_mul]
        exact mul_nonneg ht.1.le hb
      · show 0 ≤ h _
        rw [map_smul, hch, smul_eq_mul]
        exact mul_nonneg ht.1.le hc
      · simp only [mem_singleton_iff]
        intro hcon
        rw [hcon, norm_zero] at hnorm
        exact (ne_of_gt ht.1) hnorm.symm
    · rintro ⟨⟨⟨⟨hball, hfx⟩, hgx⟩, hhx⟩, hy0⟩
      have hy0' : y ≠ 0 := by simpa using hy0
      have hnp : 0 < ‖y‖ := norm_pos_iff.2 hy0'
      have hfx' : 0 ≤ f y := hfx
      have hgx' : 0 ≤ g y := hgx
      have hhx' : 0 ≤ h y := hhx
      refine ⟨‖y‖, ⟨hnp, mem_ball_zero_iff.1 hball⟩, ‖y‖⁻¹ • y, ⟨?_, ?_⟩, ?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hnp), inv_mul_cancel₀ hnp.ne']
      · refine ⟨f (‖y‖⁻¹ • y), g (‖y‖⁻¹ • y), h (‖y‖⁻¹ • y), ?_, ?_, ?_, (hdec _).symm⟩
        · rw [map_smul, smul_eq_mul]
          exact mul_nonneg (inv_pos.2 hnp).le hfx'
        · rw [map_smul, smul_eq_mul]
          exact mul_nonneg (inv_pos.2 hnp).le hgx'
        · rw [map_smul, smul_eq_mul]
          exact mul_nonneg (inv_pos.2 hnp).le hhx'
      · show ‖y‖ • ‖y‖⁻¹ • y = y
        rw [smul_smul, mul_inv_cancel₀ hnp.ne', one_smul]
  have harea : sphericalArea (sphericalTriangle u v w) = 3 * (volume (octant f g h)).toReal := by
    rw [sphericalArea, hT, measure_diff_null (measure_singleton 0)]
  rw [harea]
  linarith [e₁, e₂, e₃, htotR, a₁, a₂, a₃, a₄]

end Math

#print axioms Math.gauss_bonnet_polygon

import Mathlib
import RequestProject.GaussBonnet

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false
