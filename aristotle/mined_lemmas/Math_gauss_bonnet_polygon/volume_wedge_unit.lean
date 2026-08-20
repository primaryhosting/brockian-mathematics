import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma volume_wedge_unit (m n : E3) (hm : ‖m‖ = 1) (hn : ‖n‖ = 1)
    (h0 : 0 < InnerProductGeometry.angle m n) (hπ : InnerProductGeometry.angle m n < π) :
    volume {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, m⟫ ∧ 0 ≤ ⟪x, n⟫}
      = ENNReal.ofReal (2 * (π - InnerProductGeometry.angle m n) / 3) := by
  set ψ := InnerProductGeometry.angle m n with hψ
  have hsin : 0 < sin ψ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hcosmn : ⟪m, n⟫ = cos ψ := by
    rw [hψ, InnerProductGeometry.cos_angle, hm, hn]; ring
  have hcosnm : ⟪n, m⟫ = cos ψ := by rw [real_inner_comm]; exact hcosmn
  set e1 : E3 := (sin ψ)⁻¹ • (n - cos ψ • m) with he1def
  have hnsub : ‖n - cos ψ • m‖ = sin ψ := by
    have h2 : ‖n - cos ψ • m‖ ^ 2 = (sin ψ) ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, hn, hm, real_inner_smul_right, hcosnm, Real.norm_eq_abs]
      have := Real.sin_sq_add_cos_sq ψ
      simp only [mul_one]
      nlinarith [sq_abs (cos ψ)]
    nlinarith [norm_nonneg (n - cos ψ • m), hsin]
  have he1norm : ‖e1‖ = 1 := by
    rw [he1def, norm_smul, hnsub]
    simp [abs_of_pos hsin, inv_mul_cancel₀ (ne_of_gt hsin)]
  have he1m : ⟪e1, m⟫ = 0 := by
    rw [he1def, real_inner_smul_left, inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hm, hcosnm]
    ring
  have hn_eq : n = cos ψ • m + sin ψ • e1 := by
    rw [he1def, smul_inv_smul₀ (ne_of_gt hsin)]
    abel
  obtain ⟨b, hb0, hb1⟩ := exists_orthonormalBasis_pair m e1 hm he1norm he1m
  have hpre : {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, m⟫ ∧ 0 ≤ ⟪x, n⟫}
      = b.repr ⁻¹'
        {y : EuclideanSpace ℝ (Fin 3) | ‖y‖ ≤ 1 ∧ 0 ≤ y 0 ∧ 0 ≤ cos ψ * y 0 + sin ψ * y 1} := by
    ext x
    have e0' : (b.repr x) 0 = ⟪x, m⟫ := by
      rw [show ((b.repr x) 0 : ℝ) = (b.repr x).ofLp 0 from rfl, b.repr_apply_apply, hb0,
        real_inner_comm]
    have e1' : (b.repr x) 1 = ⟪x, e1⟫ := by
      rw [show ((b.repr x) 1 : ℝ) = (b.repr x).ofLp 1 from rfl, b.repr_apply_apply, hb1,
        real_inner_comm]
    have hnorm : ‖b.repr x‖ = ‖x‖ := b.repr.norm_map x
    have hinn : ⟪x, n⟫ = cos ψ * ⟪x, m⟫ + sin ψ * ⟪x, e1⟫ := by
      rw [hn_eq, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    simp only [mem_preimage, mem_setOf_eq, e0', e1', hnorm, hinn]
  rw [hpre, (b.measurePreserving_repr).measure_preimage
      (measurableSet_standard_wedge ψ).nullMeasurableSet, volume_standard_wedge ψ h0 hπ]

/-- The volume of the wedge of the unit ball cut out by two half-spaces with (nonzero)
normals `m` and `n`. -/
