/-
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Metric Set Module Real
open scoped RealInnerProductSpace ENNReal Pointwise

namespace Math

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The cross product of two vectors of `ℝ³`. -/

theorem volume_lune {u v : E3} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (h1 : u ≠ v) (h2 : u ≠ -v) :
    volume (hemiCone u ∩ hemiCone v) =
      ENNReal.ofReal (2 * (π - InnerProductGeometry.angle u v) / 3) := by
  set θ := InnerProductGeometry.angle u v with hθ
  have hcos : Real.cos θ = ⟪u, v⟫ := by
    rw [hθ, InnerProductGeometry.cos_angle, hu, hv]; norm_num
  have h0 : 0 < θ := by
    rcases lt_or_eq_of_le (InnerProductGeometry.angle_nonneg u v) with h | h
    · exact h
    · exfalso
      obtain ⟨-, r, hr, hrv⟩ := (InnerProductGeometry.angle_eq_zero_iff (x := u) (y := v)).mp h.symm
      have hr1 : r = 1 := by
        have : ‖v‖ = r * ‖u‖ := by rw [hrv, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
        rw [hu, hv] at this; linarith
      exact h1 (by rw [hrv, hr1, one_smul])
  have hpi : θ < π := by
    rcases lt_or_eq_of_le (InnerProductGeometry.angle_le_pi u v) with h | h
    · exact h
    · exfalso
      obtain ⟨-, r, hr, hrv⟩ := (InnerProductGeometry.angle_eq_pi_iff (x := u) (y := v)).mp h
      have hr1 : r = -1 := by
        have : ‖v‖ = |r| * ‖u‖ := by rw [hrv, norm_smul, Real.norm_eq_abs]
        rw [hu, hv, abs_of_neg hr] at this; linarith
      exact h2 (by rw [hrv, hr1]; module)
  have hs0 : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hpi
  set e3 : E3 := (Real.sin θ)⁻¹ • (v - ⟪u, v⟫ • u) with he3def
  have hnormv : ‖v - ⟪u, v⟫ • u‖^2 = Real.sin θ ^ 2 := by
    have hpy := Real.sin_sq_add_cos_sq θ
    have hc : ⟪v, u⟫ = ⟪u, v⟫ := real_inner_comm u v
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hu, hv, Real.norm_eq_abs, mul_one,
      sq_abs, hc, ← hcos]
    nlinarith
  have hne3 : ‖e3‖ = 1 := by
    rw [he3def, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < (Real.sin θ)⁻¹)]
    have hnv : ‖v - ⟪u, v⟫ • u‖ = Real.sin θ := by
      nlinarith [norm_nonneg (v - ⟪u, v⟫ • u), hnormv]
    rw [hnv, inv_mul_cancel₀ hs0.ne']
  have hue3 : ⟪u, e3⟫ = 0 := by
    rw [he3def, real_inner_smul_right, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hu]
    ring
  have he3u : ⟪e3, u⟫ = 0 := by rw [real_inner_comm]; exact hue3
  have hvdecomp : v = Real.cos θ • u + Real.sin θ • e3 := by
    rw [he3def, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul, hcos]
    module
  set e1 : E3 := cross u e3 with he1def
  have hne1 : ‖e1‖ = 1 := by
    rw [he1def, norm_cross_right e3 u hne3, he3u]
    simp [hu]
  have hi1 : ⟪e1, u⟫ = 0 := inner_cross_left u e3
  have hi2 : ⟪e1, e3⟫ = 0 := inner_cross_right u e3
  have hi1' : ⟪u, e1⟫ = 0 := by rw [real_inner_comm]; exact hi1
  have hi2' : ⟪e3, e1⟫ = 0 := by rw [real_inner_comm]; exact hi2
  have horth : Orthonormal ℝ ![e1, u, e3] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hne1, hu, hne3, hi1, hi2, hi1', hi2', hue3, he3u]
  obtain ⟨B, hB⟩ : ∃ B : OrthonormalBasis (Fin 3) ℝ E3, ∀ i, B i = ![e1, u, e3] i := by
    refine ⟨(basisOfLinearIndependentOfCardEqFinrank horth.linearIndependent
      (by simp)).toOrthonormalBasis ?_, ?_⟩
    · simpa [coe_basisOfLinearIndependentOfCardEqFinrank] using horth
    · intro i; simp [Basis.coe_toOrthonormalBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hR := B.measurePreserving_repr
  have hW : IsOpen {y : E3 | ‖y‖ < 1 ∧ 0 < y 1 ∧ 0 < Real.cos θ * y 1 + Real.sin θ * y 2} := by
    have hset : {y : E3 | ‖y‖ < 1 ∧ 0 < y 1 ∧ 0 < Real.cos θ * y 1 + Real.sin θ * y 2}
        = ({y : E3 | ‖y‖ < 1} ∩ {y : E3 | 0 < y 1})
          ∩ {y : E3 | 0 < Real.cos θ * y 1 + Real.sin θ * y 2} := by
      ext y; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
    rw [hset]
    exact ((isOpen_lt (by fun_prop) (by fun_prop)).inter
      (isOpen_lt (by fun_prop) (by fun_prop))).inter (isOpen_lt (by fun_prop) (by fun_prop))
  have hpre : hemiCone u ∩ hemiCone v = B.repr ⁻¹'
      {y : E3 | ‖y‖ < 1 ∧ 0 < y 1 ∧ 0 < Real.cos θ * y 1 + Real.sin θ * y 2} := by
    ext x
    have h1x : (B.repr x) 1 = ⟪u, x⟫ := by
      rw [B.repr_apply_apply, hB 1]; simp
    have h2x : (B.repr x) 2 = ⟪e3, x⟫ := by
      rw [B.repr_apply_apply, hB 2]; simp
    have hvx : ⟪v, x⟫ = Real.cos θ * ⟪u, x⟫ + Real.sin θ * ⟪e3, x⟫ := by
      conv_lhs => rw [hvdecomp]
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, hemiCone,
      h1x, h2x, hvx, B.repr.norm_map]
    tauto
  rw [hpre, hR.measure_preimage hW.measurableSet.nullMeasurableSet, volume_stdWedge θ h0 hpi]

