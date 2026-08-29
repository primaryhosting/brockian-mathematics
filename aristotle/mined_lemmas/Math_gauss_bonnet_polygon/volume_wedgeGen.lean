/-
Volume of a wedge of the unit ball of `EuclideanSpace ℝ (Fin 3)` in standard position.

This is an auxiliary file for the Gauss-Bonnet (Girard) theorem for spherical triangles.
-/
import RequestProject.Sector

open MeasureTheory Metric Set Real
open scoped ENNReal

namespace Math

/-- Euclidean 3-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The wedge of the unit ball cut out by the half-spaces with inner normals
`(1,0,0)` and `(cos t, sin t, 0)`. -/

theorem volume_wedgeGen (n m : E3) (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hlt : ⟪n, m⟫ ^ 2 < 1) :
    volume (wedgeGen n m) = ENNReal.ofReal (2 * (π - angle n m) / 3) := by
  set c : ℝ := ⟪n, m⟫ with hc
  set s : ℝ := Real.sqrt (1 - c ^ 2) with hs
  have hspos : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hmn : ⟪m, n⟫ = c := by rw [hc, real_inner_comm]
  have hnormsq : ‖m - c • n‖ ^ 2 = 1 - c ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hn, hm, hmn, Real.norm_eq_abs,
      mul_one, sq_abs]
    ring
  have hnormeq : ‖m - c • n‖ = s := by
    rw [hs, show (1 : ℝ) - c ^ 2 = ‖m - c • n‖ ^ 2 from hnormsq.symm, Real.sqrt_sq (norm_nonneg _)]
  set u : E3 := s⁻¹ • (m - c • n) with hu
  have hnu : ‖u‖ = 1 := by
    rw [hu, norm_smul, hnormeq]
    simp [abs_of_pos hspos, inv_mul_cancel₀ hspos.ne']
  have hortho : ⟪n, u⟫ = 0 := by
    rw [hu, real_inner_smul_right, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hn, ← hc]
    simp
  obtain ⟨b, hb0, hb1⟩ := exists_orthonormalBasis_pair n u hn hnu hortho
  -- the angle `t`
  set t : ℝ := angle n m with ht
  have hcos : Real.cos t = c := by
    rw [ht, angle, hn, hm, ← hc]
    simp only [mul_one, div_one]
    exact Real.cos_arccos (by nlinarith) (by nlinarith)
  have hsin : Real.sin t = s := by
    rw [ht, angle, hn, hm, ← hc]
    simp only [mul_one, div_one]
    rw [Real.sin_arccos, hs]
  have ht0 : 0 ≤ t := by
    rw [ht, angle]; exact Real.arccos_nonneg _
  have htpi : t ≤ π := by
    rw [ht, angle]; exact Real.arccos_le_pi _
  -- `m` in terms of the basis
  have hmb : m = c • b 0 + s • b 1 := by
    rw [hb0, hb1, hu, smul_smul, mul_inv_cancel₀ hspos.ne', one_smul]
    abel
  have hset : wedgeGen n m = b.repr ⁻¹' (wedgeStd t) := by
    ext x
    have h0 : (b.repr x) 0 = ⟪n, x⟫ := by rw [b.repr_apply_apply, hb0]
    have h1 : (b.repr x) 1 = ⟪u, x⟫ := by rw [b.repr_apply_apply, hb1]
    have hmx : ⟪m, x⟫ = c * ⟪n, x⟫ + s * ⟪u, x⟫ := by
      rw [hmb, inner_add_left, real_inner_smul_left, real_inner_smul_left, hb0, hb1]
    simp only [wedgeGen, wedgeStd, Set.mem_setOf_eq, Set.mem_preimage, h0, h1, hcos, hsin,
      LinearIsometryEquiv.norm_map, hmx]
    constructor
    · rintro ⟨ha, hb', hc'⟩
      exact ⟨ha, hb', by linarith [hc']⟩
    · rintro ⟨ha, hb', hc'⟩
      exact ⟨ha, hb', by linarith [hc']⟩
  rw [hset, b.measurePreserving_repr.measure_preimage
    (measurableSet_wedgeStd t).nullMeasurableSet, volume_wedgeStd t ht0 htpi]

end Math

