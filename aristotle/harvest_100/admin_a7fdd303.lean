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
noncomputable def toProd : EuclideanSpace ℝ (Fin 3) → ℝ × (ℝ × ℝ) := fun x => (x 2, (x 0, x 1))

lemma measurePreserving_toProd : MeasurePreserving toProd volume volume := by
  have e1 : MeasurePreserving (@WithLp.ofLp 2 (Fin 3 → ℝ)) volume volume :=
    PiLp.volume_preserving_ofLp _
  have e2 := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2
  have e3 : MeasurePreserving
      (Prod.map (id : ℝ → ℝ) (MeasurableEquiv.finTwoArrow (α := ℝ))) volume volume :=
    (MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)
  convert (e3.comp (e2.comp e1)) using 1

lemma norm_sq_eq (x : EuclideanSpace ℝ (Fin 3)) :
    ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_three, sq_abs]

/-- **Volume of a standard double wedge**: the set of points of the open unit ball lying in the
double wedge around the third axis, spanned by the directions of angle `0` and `α`. -/
lemma volume_standard_wedge (α : ℝ) (hα0 : 0 ≤ α) (hαπ : α ≤ π) :
    volume {x : EuclideanSpace ℝ (Fin 3) |
        ‖x‖ < 1 ∧ 0 < x 1 * (x 0 * Real.sin α - x 1 * Real.cos α)}
      = ENNReal.ofReal (4 * α / 3) := by
  set A : Set (ℝ × (ℝ × ℝ)) := {q | q.2.1 ^ 2 + q.2.2 ^ 2 < 1 - q.1 ^ 2 ∧
      0 < q.2.2 * (q.2.1 * Real.sin α - q.2.2 * Real.cos α)} with hAdef
  have hAopen : IsOpen A := by
    have : A = {q : ℝ × (ℝ × ℝ) | q.2.1 ^ 2 + q.2.2 ^ 2 < 1 - q.1 ^ 2} ∩
        {q : ℝ × (ℝ × ℝ) | 0 < q.2.2 * (q.2.1 * Real.sin α - q.2.2 * Real.cos α)} := rfl
    rw [this]
    exact (isOpen_lt (by fun_prop) (by fun_prop)).inter (isOpen_lt continuous_const (by fun_prop))
  have hpre : {x : EuclideanSpace ℝ (Fin 3) |
      ‖x‖ < 1 ∧ 0 < x 1 * (x 0 * Real.sin α - x 1 * Real.cos α)} = toProd ⁻¹' A := by
    ext x
    simp only [mem_setOf_eq, mem_preimage, hAdef, toProd]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have : ‖x‖ ^ 2 < 1 := by nlinarith [norm_nonneg x]
      rw [norm_sq_eq] at this
      linarith
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have hn : ‖x‖ ^ 2 < 1 := by rw [norm_sq_eq]; linarith
      nlinarith [norm_nonneg x]
  rw [hpre, measurePreserving_toProd.measure_preimage hAopen.measurableSet.nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_apply hAopen.measurableSet]
  have hslice : ∀ z : ℝ, volume (Prod.mk z ⁻¹' A) = ENNReal.ofReal (α * (1 - z ^ 2)) := by
    intro z
    have : Prod.mk z ⁻¹' A = {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1 - z ^ 2 ∧
        0 < p.2 * (p.1 * Real.sin α - p.2 * Real.cos α)} := rfl
    rw [this, volume_planar_double_sector α (1 - z ^ 2) hα0 hαπ]
  simp only [hslice]
  have hmeasf : Measurable fun z : ℝ => ENNReal.ofReal (α * (1 - z ^ 2)) := by fun_prop
  rw [← lintegral_add_compl _ (measurableSet_Ioo : MeasurableSet (Ioo (-1 : ℝ) 1))]
  have hzero : ∫⁻ z in (Ioo (-1 : ℝ) 1)ᶜ, ENNReal.ofReal (α * (1 - z ^ 2)) = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ioo.compl (g := fun _ => 0) ?_, lintegral_zero]
    intro z hz
    simp only [mem_compl_iff, mem_Ioo, not_and_or, not_lt] at hz
    have : 1 - z ^ 2 ≤ 0 := by
      rcases hz with hz | hz
      · nlinarith
      · nlinarith
    exact ENNReal.ofReal_eq_zero.2 (by nlinarith)
  rw [hzero, add_zero]
  have hint : IntegrableOn (fun z : ℝ => α * (1 - z ^ 2)) (Ioo (-1) 1) volume :=
    ((Continuous.locallyIntegrable (by fun_prop) (μ := volume)).integrableOn_isCompact
      (isCompact_Icc (a := (-1 : ℝ)) (b := 1))).mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Ioo (fun z hz => by
      have h1 : z ^ 2 < 1 := by nlinarith [hz.1, hz.2]
      show (0 : ℝ) ≤ α * (1 - z ^ 2)
      nlinarith))]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num)]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (by exact (intervalIntegral.intervalIntegrable_pow 2))]
  simp [integral_pow]
  ring

set_option maxHeartbeats 1000000 in
/-- **Volume of a double wedge**: for a unit vector `u` and two linearly independent vectors
`s`, `t` orthogonal to `u`, the set of points of the open unit ball whose orthogonal projection
onto `u^⟂` is a combination `β • s + γ • t` with `β * γ > 0` has volume `4 * angle s t / 3`. -/
theorem volume_wedge {u s t : EuclideanSpace ℝ (Fin 3)} (hu : ‖u‖ = 1)
    (hus : ⟪u, s⟫ = 0) (hut : ⟪u, t⟫ = 0)
    (hst : ∀ a b : ℝ, a • s + b • t = 0 → a = 0 ∧ b = 0) :
    volume {x : EuclideanSpace ℝ (Fin 3) | ‖x‖ < 1 ∧
        ∃ β γ : ℝ, 0 < β * γ ∧ x - ⟪u, x⟫ • u = β • s + γ • t}
      = ENNReal.ofReal (4 * angle s t / 3) := by
  -- Gram-Schmidt: build an orthonormal basis `f0, f1, u` adapted to the wedge.
  have hs0 : s ≠ 0 := by
    intro h
    simpa using (hst 1 0 (by simp [h])).1
  have ht0 : t ≠ 0 := by
    intro h
    simpa using (hst 0 1 (by simp [h])).2
  obtain ⟨ns, hnsdef⟩ : ∃ r : ℝ, r = ‖s‖ := ⟨_, rfl⟩
  obtain ⟨ntt, hnttdef⟩ : ∃ r : ℝ, r = ‖t‖ := ⟨_, rfl⟩
  have hns : (0:ℝ) < ns := by rw [hnsdef]; exact norm_pos_iff.2 hs0
  have hntt : (0:ℝ) < ntt := by rw [hnttdef]; exact norm_pos_iff.2 ht0
  obtain ⟨f0, hf0def⟩ : ∃ z : EuclideanSpace ℝ (Fin 3), z = ns⁻¹ • s := ⟨_, rfl⟩
  have hsf0 : s = ns • f0 := by
    rw [hf0def, smul_smul, mul_inv_cancel₀ hns.ne', one_smul]
  have hf0n : ‖f0‖ = 1 := by
    rw [hf0def, norm_smul, ← hnsdef, Real.norm_eq_abs, abs_inv, abs_of_pos hns,
      inv_mul_cancel₀ hns.ne']
  have hf0f0 : ⟪f0, f0⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hf0n]; norm_num
  obtain ⟨c, hcdef⟩ : ∃ r : ℝ, r = ⟪f0, t⟫ := ⟨_, rfl⟩
  obtain ⟨t', ht'def⟩ : ∃ z : EuclideanSpace ℝ (Fin 3), z = t - c • f0 := ⟨_, rfl⟩
  have hf0t' : ⟪f0, t'⟫ = 0 := by
    rw [ht'def, inner_sub_right, real_inner_smul_right, hf0f0, ← hcdef]; ring
  have ht'0 : t' ≠ 0 := by
    intro h
    rw [ht'def, sub_eq_zero] at h
    have hzero : (-(c * ns⁻¹)) • s + (1:ℝ) • t = 0 := by rw [h, hf0def]; module
    simpa using (hst _ _ hzero).2
  obtain ⟨nt, hntdef⟩ : ∃ r : ℝ, r = ‖t'‖ := ⟨_, rfl⟩
  have hnt : (0:ℝ) < nt := by rw [hntdef]; exact norm_pos_iff.2 ht'0
  obtain ⟨f1, hf1def⟩ : ∃ z : EuclideanSpace ℝ (Fin 3), z = nt⁻¹ • t' := ⟨_, rfl⟩
  have ht'f1 : t' = nt • f1 := by
    rw [hf1def, smul_smul, mul_inv_cancel₀ hnt.ne', one_smul]
  have hf1n : ‖f1‖ = 1 := by
    rw [hf1def, norm_smul, ← hntdef, Real.norm_eq_abs, abs_inv, abs_of_pos hnt,
      inv_mul_cancel₀ hnt.ne']
  have hf1f1 : ⟪f1, f1⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hf1n]; norm_num
  have hf0f1 : ⟪f0, f1⟫ = 0 := by rw [hf1def, real_inner_smul_right, hf0t', mul_zero]
  have hf1f0 : ⟪f1, f0⟫ = 0 := by rw [real_inner_comm]; exact hf0f1
  have htf1 : t = c • f0 + nt • f1 := by rw [← ht'f1, ht'def]; abel
  have huf0 : ⟪u, f0⟫ = 0 := by rw [hf0def, real_inner_smul_right, hus, mul_zero]
  have hut' : ⟪u, t'⟫ = 0 := by
    rw [ht'def, inner_sub_right, real_inner_smul_right, huf0, hut]; ring
  have huf1 : ⟪u, f1⟫ = 0 := by rw [hf1def, real_inner_smul_right, hut', mul_zero]
  have hf0u : ⟪f0, u⟫ = 0 := by rw [real_inner_comm]; exact huf0
  have hf1u : ⟪f1, u⟫ = 0 := by rw [real_inner_comm]; exact huf1
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hv : Orthonormal ℝ ![f0, f1, u] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hf0n, hf1n, hu, hf0f1, hf1f0, huf0, huf1, hf0u, hf1u]
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range ![f0, f1, u]) := by
    rw [hv.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)]
  obtain ⟨b, hb0, hb1, hb2⟩ : ∃ b : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)),
      b 0 = f0 ∧ b 1 = f1 ∧ b 2 = u :=
    ⟨OrthonormalBasis.mk hv hspan, by rw [OrthonormalBasis.coe_mk]; rfl,
      by rw [OrthonormalBasis.coe_mk]; rfl, by rw [OrthonormalBasis.coe_mk]; rfl⟩
  -- coefficients with respect to `f0`, `f1` are unique
  have hcoef : ∀ p q p' q' : ℝ, p • f0 + q • f1 = p' • f0 + q' • f1 → p = p' ∧ q = q' := by
    intro p q p' q' h
    have e0 := congrArg (fun m : EuclideanSpace ℝ (Fin 3) => ⟪f0, m⟫) h
    have e1 := congrArg (fun m : EuclideanSpace ℝ (Fin 3) => ⟪f1, m⟫) h
    simp only [inner_add_right, real_inner_smul_right, hf0f0, hf0f1, hf1f0, hf1f1,
      mul_one, mul_zero, add_zero, zero_add] at e0 e1
    exact ⟨e0, e1⟩
  -- the orthogonal projection to `u^⟂` in coordinates
  have hproj : ∀ x : EuclideanSpace ℝ (Fin 3),
      x - ⟪u, x⟫ • u = (b.repr x 0) • f0 + (b.repr x 1) • f1 := by
    intro x
    have hsum : (b.repr x 0) • f0 + (b.repr x 1) • f1 + (b.repr x 2) • u = x := by
      have h := b.sum_repr x
      rw [Fin.sum_univ_three, hb0, hb1, hb2] at h
      exact h
    have h2 : ⟪u, x⟫ = b.repr x 2 := by rw [b.repr_apply_apply x 2, hb2]
    rw [h2, sub_eq_iff_eq_add]
    exact hsum.symm
  -- the angle between `s` and `t`
  have hcos : Real.cos (angle s t) = c / ntt := by
    rw [cos_angle, ← hnsdef, ← hnttdef]
    have hin : ⟪s, t⟫ = ns * c := by rw [hsf0, real_inner_smul_left, ← hcdef]
    rw [hin]
    field_simp
  have hnormt2 : ntt ^ 2 = c ^ 2 + nt ^ 2 := by
    have h1 : ⟪t, t⟫ = ntt ^ 2 := by rw [hnttdef]; exact real_inner_self_eq_norm_sq t
    have h2 : ⟪t, t⟫ = c ^ 2 + nt ^ 2 := by
      rw [htf1]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hf0f0, hf1f1, hf0f1, hf1f0]
      ring
    linarith
  have hsin : Real.sin (angle s t) = nt / ntt := by
    rw [Real.sin_eq_sqrt_one_sub_cos_sq (angle_nonneg s t) (angle_le_pi s t), hcos,
      show 1 - (c / ntt) ^ 2 = (nt / ntt) ^ 2 by field_simp; nlinarith [hnormt2]]
    exact Real.sqrt_sq (by positivity)
  -- membership in the wedge in coordinates
  have hiff : ∀ x : EuclideanSpace ℝ (Fin 3),
      (∃ β γ : ℝ, 0 < β * γ ∧ x - ⟪u, x⟫ • u = β • s + γ • t) ↔
        0 < (b.repr x 1) * ((b.repr x 0) * Real.sin (angle s t) -
          (b.repr x 1) * Real.cos (angle s t)) := by
    intro x
    rw [hsin, hcos]
    constructor
    · rintro ⟨β, γ, hβγ, heq⟩
      rw [hproj x] at heq
      have heq2 : (b.repr x 0) • f0 + (b.repr x 1) • f1
          = (β * ns + γ * c) • f0 + (γ * nt) • f1 := by
        rw [heq, hsf0, htf1]; module
      obtain ⟨hA, hB⟩ := hcoef _ _ _ _ heq2
      rw [hA, hB]
      have hval : γ * nt * ((β * ns + γ * c) * (nt / ntt) - γ * nt * (c / ntt))
          = (β * γ) * (ns * nt ^ 2 / ntt) := by
        field_simp
        ring
      rw [hval]
      positivity
    · intro hpos
      have hkey : 0 < (b.repr x 1) * ((b.repr x 0) * nt - (b.repr x 1) * c) := by
        have h' : (b.repr x 1) * ((b.repr x 0) * (nt / ntt) - (b.repr x 1) * (c / ntt))
            = ((b.repr x 1) * ((b.repr x 0) * nt - (b.repr x 1) * c)) / ntt := by
          field_simp
        rw [h'] at hpos
        rcases div_pos_iff.mp hpos with ⟨h, -⟩ | ⟨-, h⟩
        · exact h
        · linarith
      refine ⟨((b.repr x 0) * nt - (b.repr x 1) * c) / (ns * nt), (b.repr x 1) / nt, ?_, ?_⟩
      · have hval : ((b.repr x 0) * nt - (b.repr x 1) * c) / (ns * nt) * ((b.repr x 1) / nt)
            = ((b.repr x 1) * ((b.repr x 0) * nt - (b.repr x 1) * c)) / (ns * nt ^ 2) := by
          field_simp
        rw [hval]
        positivity
      · rw [hproj x, hsf0, htf1]
        have h1 : ((b.repr x 0) * nt - (b.repr x 1) * c) / (ns * nt) * ns +
            (b.repr x 1) / nt * c = (b.repr x 0) := by
          field_simp
          ring
        have h2 : (b.repr x 1) / nt * nt = (b.repr x 1) := by field_simp
        rw [show (((b.repr x 0) * nt - (b.repr x 1) * c) / (ns * nt)) • (ns • f0)
              + ((b.repr x 1) / nt) • (c • f0 + nt • f1)
            = (((b.repr x 0) * nt - (b.repr x 1) * c) / (ns * nt) * ns
                + (b.repr x 1) / nt * c) • f0
              + ((b.repr x 1) / nt * nt) • f1 from by module, h1, h2]
  -- transport to the standard wedge
  have hset : {x : EuclideanSpace ℝ (Fin 3) | ‖x‖ < 1 ∧
      ∃ β γ : ℝ, 0 < β * γ ∧ x - ⟪u, x⟫ • u = β • s + γ • t} =
      b.repr ⁻¹' {y : EuclideanSpace ℝ (Fin 3) | ‖y‖ < 1 ∧
        0 < y 1 * (y 0 * Real.sin (angle s t) - y 1 * Real.cos (angle s t))} := by
    ext x
    simp only [mem_setOf_eq, mem_preimage]
    rw [b.repr.norm_map x, hiff x]
  rw [hset]
  have hopen : IsOpen {y : EuclideanSpace ℝ (Fin 3) | ‖y‖ < 1 ∧
      0 < y 1 * (y 0 * Real.sin (angle s t) - y 1 * Real.cos (angle s t))} := by
    have c0 : Continuous fun y : EuclideanSpace ℝ (Fin 3) => y 0 :=
      (EuclideanSpace.proj (0 : Fin 3)).continuous
    have c1 : Continuous fun y : EuclideanSpace ℝ (Fin 3) => y 1 :=
      (EuclideanSpace.proj (1 : Fin 3)).continuous
    have hsplit : {y : EuclideanSpace ℝ (Fin 3) | ‖y‖ < 1 ∧
        0 < y 1 * (y 0 * Real.sin (angle s t) - y 1 * Real.cos (angle s t))} =
        {y : EuclideanSpace ℝ (Fin 3) | ‖y‖ < 1} ∩
        {y : EuclideanSpace ℝ (Fin 3) |
          0 < y 1 * (y 0 * Real.sin (angle s t) - y 1 * Real.cos (angle s t))} := rfl
    rw [hsplit]
    exact (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const (by fun_prop))
  rw [b.measurePreserving_repr.measure_preimage hopen.measurableSet.nullMeasurableSet,
    volume_standard_wedge _ (angle_nonneg s t) (angle_le_pi s t)]

end SphericalArea

import Mathlib

/-!
# Area of a planar double sector

The key planar computation: the set of points of the disc of radius `√R2` lying in the
double sector spanned by the directions of angle `0` and `α` has area `α * R2`.
-/

open MeasureTheory Real Set
open scoped ENNReal Real

namespace SphericalArea

/-- The set of polar angles in `(-π, π)` belonging to the double sector of angle `α`. -/
lemma angleSet_eq (α : ℝ) (hα0 : 0 ≤ α) (hαπ : α ≤ π) :
    {ψ : ℝ | ψ ∈ Ioo (-π) π ∧ 0 < Real.sin ψ * Real.sin (α - ψ)}
      = Ioo 0 α ∪ Ioo (-π) (α - π) := by
  ext ψ
  simp only [mem_setOf_eq, mem_Ioo, mem_union]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rcases lt_trichotomy (Real.sin ψ) 0 with hs | hs | hs
    · -- sin ψ < 0, so ψ ∈ (-π, 0)
      have hψneg : ψ < 0 := by
        by_contra h
        push_neg at h
        exact absurd (Real.sin_nonneg_of_nonneg_of_le_pi h h2.le) (not_le.2 hs)
      right
      refine ⟨h1, ?_⟩
      -- sin (α - ψ) < 0
      have h4 : Real.sin (α - ψ) < 0 := by
        nlinarith [h3]
      by_contra hcon
      push_neg at hcon
      have : 0 ≤ α - ψ := by linarith
      have : α - ψ ≤ π := by linarith
      exact absurd (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) this) (not_le.2 h4)
    · simp [hs] at h3
    · -- sin ψ > 0
      have hψpos : 0 < ψ := by
        by_contra h
        push_neg at h
        have : Real.sin ψ ≤ 0 := by
          have := Real.sin_nonneg_of_nonneg_of_le_pi (x := -ψ) (by linarith) (by linarith)
          rw [Real.sin_neg] at this
          linarith
        linarith
      left
      refine ⟨hψpos, ?_⟩
      have h4 : 0 < Real.sin (α - ψ) := by nlinarith [h3]
      by_contra hcon
      push_neg at hcon
      have h5 : α - ψ ≤ 0 := by linarith
      have h6 : -π < α - ψ := by linarith
      have : Real.sin (α - ψ) ≤ 0 := by
        have := Real.sin_nonneg_of_nonneg_of_le_pi (x := ψ - α) (by linarith) (by linarith)
        rw [show ψ - α = -(α - ψ) by ring, Real.sin_neg] at this
        linarith
      linarith
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have hαpos : 0 < α := lt_of_lt_of_le h1 h2.le
      refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      have hs1 : 0 < Real.sin ψ := Real.sin_pos_of_pos_of_lt_pi h1 (by linarith)
      have hs2 : 0 < Real.sin (α - ψ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      positivity
    · refine ⟨⟨h1, by linarith⟩, ?_⟩
      have hψneg : ψ < 0 := by linarith [Real.pi_pos]
      have hs1 : Real.sin ψ < 0 := by
        have := Real.sin_pos_of_pos_of_lt_pi (x := -ψ) (by linarith) (by linarith)
        rw [Real.sin_neg] at this; linarith
      have hs2 : Real.sin (α - ψ) < 0 := by
        have := Real.sin_pos_of_pos_of_lt_pi (x := α - ψ - π) (by linarith) (by linarith)
        rw [show α - ψ - π = -(π - (α - ψ)) by ring, Real.sin_neg,
          Real.sin_pi_sub] at this
        linarith
      exact mul_pos_of_neg_of_neg hs1 hs2

lemma volume_angleSet (α : ℝ) (hα0 : 0 ≤ α) (hαπ : α ≤ π) :
    volume {ψ : ℝ | ψ ∈ Ioo (-π) π ∧ 0 < Real.sin ψ * Real.sin (α - ψ)}
      = ENNReal.ofReal (2 * α) := by
  rw [angleSet_eq α hα0 hαπ]
  rw [measure_union _ measurableSet_Ioo]
  · rw [Real.volume_Ioo, Real.volume_Ioo,
      ← ENNReal.ofReal_add (by linarith) (by linarith)]
    congr 1
    ring
  · rw [Set.disjoint_left]
    rintro x ⟨hx1, _⟩ ⟨_, hx2⟩
    linarith [Real.pi_pos]

lemma lintegral_radial (R2 : ℝ) :
    ∫⁻ r in Ioi (0:ℝ), (if r ^ 2 < R2 then ENNReal.ofReal r else 0) =
      ENNReal.ofReal (R2 / 2) := by
  rcases le_or_gt R2 0 with h | h
  · have : ∀ r ∈ Ioi (0:ℝ), (if r ^ 2 < R2 then ENNReal.ofReal r else 0) = 0 := by
      intro r hr
      rw [if_neg]
      exact not_lt.2 (le_trans h (sq_nonneg r))
    rw [setLIntegral_congr_fun measurableSet_Ioi this, lintegral_zero,
      ENNReal.ofReal_eq_zero.2 (by linarith)]
  · have hs : ∀ r ∈ Ioi (0:ℝ), (if r ^ 2 < R2 then ENNReal.ofReal r else 0) =
        (Ioo (0:ℝ) (Real.sqrt R2)).indicator (fun r => ENNReal.ofReal r) r := by
      intro r hr
      simp only [mem_Ioi] at hr
      by_cases hlt : r ^ 2 < R2
      · rw [if_pos hlt, Set.indicator_of_mem]
        refine ⟨hr, ?_⟩
        have : r = Real.sqrt (r ^ 2) := by rw [Real.sqrt_sq hr.le]
        rw [this]
        exact Real.sqrt_lt_sqrt (sq_nonneg r) hlt
      · rw [if_neg hlt, Set.indicator_of_notMem]
        intro hmem
        exact hlt (by
          have h1 : r < Real.sqrt R2 := hmem.2
          have : r ^ 2 < (Real.sqrt R2) ^ 2 := by nlinarith [hmem.1]
          rwa [Real.sq_sqrt h.le] at this)
    rw [setLIntegral_congr_fun measurableSet_Ioi hs,
      lintegral_indicator measurableSet_Ioo]
    set s := Real.sqrt R2 with hsdef
    have hspos : 0 < s := Real.sqrt_pos.2 h
    have hint : IntegrableOn (fun r : ℝ => r) (Ioo 0 s) volume :=
      ((continuous_id.locallyIntegrable (μ := volume)).integrableOn_isCompact
        (isCompact_Icc (a := (0:ℝ)) (b := s))).mono_set
        Ioo_subset_Icc_self
    have hval : ∫ r in Ioo (0:ℝ) s, r = s ^ 2 / 2 := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hspos.le,
        integral_id]
      ring
    rw [Measure.restrict_restrict measurableSet_Ioo,
      Set.inter_eq_left.2 (fun x hx => hx.1),
      ← ofReal_integral_eq_lintegral_ofReal hint
      (ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => hx.1.le)), hval,
      Real.sq_sqrt h.le]

/-- **Area of a planar double sector**: the part of the open disc of radius `√R2` lying in the
double sector bounded by the lines of angle `0` and `α` has area `α * R2`. -/
lemma volume_planar_double_sector (α R2 : ℝ) (hα0 : 0 ≤ α) (hαπ : α ≤ π) :
    volume {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < R2 ∧
        0 < p.2 * (p.1 * Real.sin α - p.2 * Real.cos α)} = ENNReal.ofReal (α * R2) := by
  set S : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < R2 ∧
      0 < p.2 * (p.1 * Real.sin α - p.2 * Real.cos α)} with hSdef
  have hSopen : IsOpen S := by
    have hS : S = {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < R2} ∩
        {p : ℝ × ℝ | 0 < p.2 * (p.1 * Real.sin α - p.2 * Real.cos α)} := rfl
    rw [hS]
    exact (isOpen_lt (by fun_prop) continuous_const).inter
      (isOpen_lt continuous_const (by fun_prop))
  have hmeas : MeasurableSet S := hSopen.measurableSet
  set A : Set ℝ := {ψ : ℝ | 0 < Real.sin ψ * Real.sin (α - ψ)} with hAdef
  have hAmeas : MeasurableSet A :=
    (isOpen_lt continuous_const (by fun_prop : Continuous fun ψ : ℝ =>
      Real.sin ψ * Real.sin (α - ψ))).measurableSet
  set F : ℝ → ℝ≥0∞ := fun r => if r ^ 2 < R2 then ENNReal.ofReal r else 0 with hFdef
  set G : ℝ → ℝ≥0∞ := A.indicator 1 with hGdef
  rw [← lintegral_indicator_one hmeas, ← lintegral_comp_polarCoord_symm]
  have key : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • S.indicator 1 (polarCoord.symm p) = F p.1 * G p.2 := by
    rintro ⟨r, ψ⟩ hp
    simp only [polarCoord_target, mem_prod, mem_Ioi, mem_Ioo] at hp
    obtain ⟨hr, -⟩ := hp
    have hsymm : polarCoord.symm (r, ψ) = (r * Real.cos ψ, r * Real.sin ψ) := rfl
    have hcond : (polarCoord.symm (r, ψ)) ∈ S ↔ (r ^ 2 < R2 ∧ ψ ∈ A) := by
      rw [hsymm]
      simp only [hSdef, hAdef, mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · nlinarith [Real.sin_sq_add_cos_sq ψ]
        · have : r * Real.sin ψ * (r * Real.cos ψ * Real.sin α - r * Real.sin ψ * Real.cos α)
              = r ^ 2 * (Real.sin ψ * Real.sin (α - ψ)) := by
            rw [Real.sin_sub]; ring
          rw [this] at h2
          nlinarith [sq_nonneg r]
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · nlinarith [Real.sin_sq_add_cos_sq ψ]
        · have : r * Real.sin ψ * (r * Real.cos ψ * Real.sin α - r * Real.sin ψ * Real.cos α)
              = r ^ 2 * (Real.sin ψ * Real.sin (α - ψ)) := by
            rw [Real.sin_sub]; ring
          rw [this]
          positivity
    simp only [hFdef, hGdef]
    by_cases h1 : r ^ 2 < R2
    · by_cases h2 : ψ ∈ A
      · rw [Set.indicator_of_mem (hcond.2 ⟨h1, h2⟩), Set.indicator_of_mem h2, if_pos h1]
        simp
      · rw [Set.indicator_of_notMem (fun hc => h2 (hcond.1 hc).2),
          Set.indicator_of_notMem h2]
        simp
    · rw [Set.indicator_of_notMem (fun hc => h1 (hcond.1 hc).1), if_neg h1]
      simp
  have hFmeas : Measurable F := by
    apply Measurable.ite _ (by fun_prop) measurable_const
    exact (measurableSet_lt (by fun_prop) measurable_const)
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet key, polarCoord_target,
    Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul hFmeas.aemeasurable
      ((measurable_one.indicator hAmeas).aemeasurable),
    hFdef, lintegral_radial R2, lintegral_indicator hAmeas]
  simp only [Pi.one_apply, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, one_mul]
  rw [Measure.restrict_apply hAmeas]
  have hAI : A ∩ Ioo (-π) π = {ψ : ℝ | ψ ∈ Ioo (-π) π ∧ 0 < Real.sin ψ * Real.sin (α - ψ)} := by
    ext ψ; simp only [hAdef, mem_inter_iff, mem_setOf_eq]; tauto
  rw [hAI, volume_angleSet α hα0 hαπ]
  rcases le_or_gt R2 0 with h | h
  · rw [ENNReal.ofReal_eq_zero.2 (by linarith : R2 / 2 ≤ 0), zero_mul]
    exact (ENNReal.ofReal_eq_zero.2 (by nlinarith)).symm
  · rw [← ENNReal.ofReal_mul (by linarith)]
    congr 1
    ring

end SphericalArea

import Mathlib
import RequestProject.Wedge

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

set_option grind.warning false

/-!
# Girard's theorem / the Gauss-Bonnet formula for a spherical triangle

The angle sum of a geodesic triangle on the unit sphere in `ℝ³` exceeds `π` exactly by the
area of the triangle.
-/

open MeasureTheory Metric Real Set InnerProductGeometry
open scoped RealInnerProductSpace ENNReal

namespace Math

/-- Three dimensional Euclidean space. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The cone over a subset `S` of the unit sphere: all points `r • y` with `y ∈ S` and
`0 < r < 1`. -/
def coneOver (S : Set E3) : Set E3 := {x : E3 | ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∃ y ∈ S, x = r • y}

/-- The area of a subset of the unit sphere, defined as three times the volume of the cone over
it.  With this normalisation the whole unit sphere has area `4 * π`,
see `Math.sphArea_unit_sphere`. -/
noncomputable def sphArea (S : Set E3) : ℝ := 3 * (volume (coneOver S)).toReal

/-- The open geodesic triangle on the unit sphere with vertices `u`, `v`, `w`: the points of the
sphere that are strictly positive combinations of the three vertices. -/
def sphTriangle (u v w : E3) : Set E3 :=
  {x : E3 | ‖x‖ = 1 ∧ ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ x = a • u + b • v + c • w}

/-- The interior angle at the vertex `u` of the geodesic triangle with vertices `u`, `v`, `w`:
the angle between the tangent directions at `u` of the two geodesic sides through `u`. -/
noncomputable def sphAngle (u v w : E3) : ℝ :=
  angle (v - ⟪u, v⟫ • u) (w - ⟪u, w⟫ • u)

/-- The solid cone spanned by `u`, `v`, `w`. -/
def posCone (u v w : E3) : Set E3 :=
  {x : E3 | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ x = a • u + b • v + c • w}

/-- The double wedge along the axis `u`, bounded by the planes spanned by `u, v` and by
`u, w`. -/
def dblWedge (u v w : E3) : Set E3 :=
  {x : E3 | ∃ a b c : ℝ, 0 < b * c ∧ x = a • u + b • v + c • w}

/-! ### The volume of the unit ball -/

lemma volume_unit_ball : volume (ball (0 : E3) 1) = ENNReal.ofReal (4 * π / 3) := by
  rw [InnerProductSpace.volume_ball]
  have hrank : Module.finrank ℝ E3 = 3 := by simp
  rw [hrank]
  have hg : Real.Gamma (3 / 2) = 1 / 2 * Real.sqrt π := by
    rw [show (3:ℝ) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
  have h1 : Real.Gamma ((5:ℝ) / 2) = 3 / 4 * Real.sqrt π := by
    rw [show (5:ℝ) / 2 = 3 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), hg]; ring
  have hs : Real.sqrt π ^ 3 = π * Real.sqrt π := by
    rw [pow_succ, Real.sq_sqrt Real.pi_nonneg]
  norm_num [h1, hs]
  congr 1
  have hpi : Real.sqrt π ≠ 0 := by positivity
  field_simp

/-! ### The area of the whole sphere -/

lemma coneOver_sphere : coneOver (sphere (0 : E3) 1) = ball (0 : E3) 1 \ {0} := by
  ext x
  simp only [coneOver, mem_setOf_eq, mem_diff, mem_ball_zero_iff, mem_singleton_iff,
    mem_sphere_zero_iff_norm]
  constructor
  · rintro ⟨r, hr0, hr1, y, hy, rfl⟩
    rw [norm_smul, hy, Real.norm_eq_abs, abs_of_pos hr0, mul_one]
    exact ⟨hr1, smul_ne_zero hr0.ne' (by rw [← norm_pos_iff, hy]; norm_num)⟩
  · rintro ⟨h1, h2⟩
    have hx : 0 < ‖x‖ := norm_pos_iff.2 h2
    refine ⟨‖x‖, hx, h1, ‖x‖⁻¹ • x, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx.ne']
    · rw [smul_smul, mul_inv_cancel₀ hx.ne', one_smul]

lemma sphArea_unit_sphere : sphArea (sphere (0 : E3) 1) = 4 * π := by
  rw [sphArea, coneOver_sphere, measure_diff_null (measure_singleton 0), volume_unit_ball,
    ENNReal.toReal_ofReal (by positivity)]
  ring

/-! ### The wedge at a vertex -/

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
lemma sign_count {A B C : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    (if 0 < B * C then (1:ℝ≥0∞) else 0) + (if 0 < A * C then 1 else 0)
      + (if 0 < A * B then 1 else 0)
      = 1 + 2 * (if (0 < A * B ∧ 0 < B * C) then 1 else 0) := by
  rcases lt_or_gt_of_ne hA with hA' | hA' <;> rcases lt_or_gt_of_ne hB with hB' | hB' <;>
    rcases lt_or_gt_of_ne hC with hC' | hC' <;>
    simp [mul_pos_iff, hA', hB', hC', hA'.asymm, hB'.asymm, hC'.asymm] <;> ring

/-! ### The main theorem -/

/-- **Girard's theorem** (the Gauss-Bonnet formula for a spherical triangle): the sum of the
three interior angles of a nondegenerate geodesic triangle on the unit sphere equals `π` plus
the area of the triangle. -/
theorem gauss_bonnet_polygon (u v w : E3) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hind : LinearIndependent ℝ ![u, v, w]) :
    sphAngle u v w + sphAngle v u w + sphAngle w u v = π + sphArea (sphTriangle u v w) := by
  classical
  -- ## The basis given by the three vertices and the associated coordinates
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ E3 := by simp
  set B : Module.Basis (Fin 3) ℝ E3 := basisOfLinearIndependentOfCardEqFinrank hind hcard
    with hBdef
  have hBcoe : ⇑B = ![u, v, w] := coe_basisOfLinearIndependentOfCardEqFinrank hind hcard
  have hB0 : B 0 = u := by rw [hBcoe]; rfl
  have hB1 : B 1 = v := by rw [hBcoe]; rfl
  have hB2 : B 2 = w := by rw [hBcoe]; rfl
  set co : Fin 3 → E3 → ℝ := fun i x => B.repr x i with hcodef
  have hrep : ∀ x : E3, (co 0 x) • u + (co 1 x) • v + (co 2 x) • w = x := by
    intro x
    have h := B.sum_repr x
    rw [Fin.sum_univ_three, hB0, hB1, hB2] at h
    exact h
  have hru : B.repr u = Finsupp.single 0 1 := by rw [← hB0, B.repr_self]
  have hrv : B.repr v = Finsupp.single 1 1 := by rw [← hB1, B.repr_self]
  have hrw : B.repr w = Finsupp.single 2 1 := by rw [← hB2, B.repr_self]
  have huniq : ∀ (a b c : ℝ) (i : Fin 3), co i (a • u + b • v + c • w) = ![a, b, c] i := by
    intro a b c i
    simp only [hcodef, map_add, map_smul, hru, hrv, hrw]
    fin_cases i <;> simp
  have hzero : ∀ p a b : ℝ, p • u + a • v + b • w = 0 → p = 0 ∧ a = 0 ∧ b = 0 := by
    intro p a b h
    have h0 := huniq p a b 0
    have h1 := huniq p a b 1
    have h2 := huniq p a b 2
    rw [h] at h0 h1 h2
    simp only [hcodef, map_zero] at h0 h1 h2
    exact ⟨by simpa using h0.symm, by simpa using h1.symm, by simpa using h2.symm⟩
  -- ## Coordinate descriptions of the cone and of the three wedges
  have hposC : ∀ x : E3, x ∈ posCone u v w ↔ (0 < co 0 x ∧ 0 < co 1 x ∧ 0 < co 2 x) := by
    intro x
    constructor
    · rintro ⟨a, b, c, ha, hb, hc, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [huniq a b c 0]; simpa using ha
      · rw [huniq a b c 1]; simpa using hb
      · rw [huniq a b c 2]; simpa using hc
    · rintro ⟨h0, h1, h2⟩
      exact ⟨co 0 x, co 1 x, co 2 x, h0, h1, h2, (hrep x).symm⟩
  have hDu : ∀ x : E3, x ∈ dblWedge u v w ↔ 0 < co 1 x * co 2 x := by
    intro x
    constructor
    · rintro ⟨a, b, c, hbc, rfl⟩
      rw [huniq a b c 1, huniq a b c 2]
      simpa using hbc
    · intro h
      exact ⟨co 0 x, co 1 x, co 2 x, h, (hrep x).symm⟩
  have hDv : ∀ x : E3, x ∈ dblWedge v u w ↔ 0 < co 0 x * co 2 x := by
    intro x
    constructor
    · rintro ⟨a, b, c, hbc, rfl⟩
      have hx : a • v + b • u + c • w = b • u + a • v + c • w := by module
      rw [hx, huniq b a c 0, huniq b a c 2]
      simpa using hbc
    · intro h
      refine ⟨co 1 x, co 0 x, co 2 x, h, ?_⟩
      conv_lhs => rw [← hrep x]
      module
  have hDw : ∀ x : E3, x ∈ dblWedge w u v ↔ 0 < co 0 x * co 1 x := by
    intro x
    constructor
    · rintro ⟨a, b, c, hbc, rfl⟩
      have hx : a • w + b • u + c • v = b • u + c • v + a • w := by module
      rw [hx, huniq b c a 0, huniq b c a 1]
      simpa using hbc
    · intro h
      refine ⟨co 2 x, co 0 x, co 1 x, h, ?_⟩
      conv_lhs => rw [← hrep x]
      module
  -- ## Continuity and measurability
  have hcocont : ∀ i, Continuous (co i) := by
    intro i
    have : co i = ⇑(B.coord i) := by
      funext x; rw [Module.Basis.coord_apply]
    rw [this]
    exact LinearMap.continuous_of_finiteDimensional _
  set Bl : Set E3 := ball 0 1 with hBl
  set Du : Set E3 := {x : E3 | 0 < co 1 x * co 2 x} with hDudef
  set Dv : Set E3 := {x : E3 | 0 < co 0 x * co 2 x} with hDvdef
  set Dww : Set E3 := {x : E3 | 0 < co 0 x * co 1 x} with hDwdef
  set Q : Set E3 := {x : E3 | 0 < co 0 x * co 1 x ∧ 0 < co 1 x * co 2 x} with hQdef
  set P : Set E3 := {x : E3 | 0 < co 0 x ∧ 0 < co 1 x ∧ 0 < co 2 x} with hPdef
  have hoDu : IsOpen Du := isOpen_lt continuous_const ((hcocont 1).mul (hcocont 2))
  have hoDv : IsOpen Dv := isOpen_lt continuous_const ((hcocont 0).mul (hcocont 2))
  have hoDw : IsOpen Dww := isOpen_lt continuous_const ((hcocont 0).mul (hcocont 1))
  have hmDu : MeasurableSet Du := hoDu.measurableSet
  have hmDv : MeasurableSet Dv := hoDv.measurableSet
  have hmDw : MeasurableSet Dww := hoDw.measurableSet
  have hmQ : MeasurableSet Q := (hoDw.inter hoDu).measurableSet
  have hmP : MeasurableSet P :=
    ((isOpen_lt continuous_const (hcocont 0)).inter
      ((isOpen_lt continuous_const (hcocont 1)).inter
        (isOpen_lt continuous_const (hcocont 2)))).measurableSet
  -- ## The coordinate hyperplanes are null
  have hker : ∀ i, volume {x : E3 | co i x = 0} = 0 := by
    intro i
    have hset : {x : E3 | co i x = 0} = (LinearMap.ker (B.coord i) : Submodule ℝ E3) := by
      ext x
      simp [LinearMap.mem_ker, Module.Basis.coord_apply, hcodef]
    rw [hset]
    refine Measure.addHaar_submodule _ _ ?_
    intro htop
    have hmem : B i ∈ LinearMap.ker (B.coord i) := by rw [htop]; trivial
    rw [LinearMap.mem_ker, Module.Basis.coord_apply, B.repr_self] at hmem
    simp at hmem
  have hNae : ∀ᵐ x : E3, co 0 x ≠ 0 ∧ co 1 x ≠ 0 ∧ co 2 x ≠ 0 := by
    have h0 : ∀ᵐ x : E3, co 0 x ≠ 0 := by rw [ae_iff]; simpa using hker 0
    have h1 : ∀ᵐ x : E3, co 1 x ≠ 0 := by rw [ae_iff]; simpa using hker 1
    have h2 : ∀ᵐ x : E3, co 2 x ≠ 0 := by rw [ae_iff]; simpa using hker 2
    filter_upwards [h0, h1, h2] with x hx0 hx1 hx2 using ⟨hx0, hx1, hx2⟩
  -- ## The counting identity
  have hcount : volume (Du ∩ Bl) + volume (Dv ∩ Bl) + volume (Dww ∩ Bl)
      = volume Bl + 2 * volume (Q ∩ Bl) := by
    have key : ∫⁻ x in Bl, (Du.indicator 1 x + Dv.indicator 1 x + Dww.indicator 1 x)
        = ∫⁻ x in Bl, ((1 : ℝ≥0∞) + 2 * Q.indicator 1 x) := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae hNae] with x hx
      simp only [Set.indicator_apply, Pi.one_apply, hDudef, hDvdef, hDwdef, hQdef,
        mem_setOf_eq]
      exact sign_count hx.1 hx.2.1 hx.2.2
    rw [lintegral_add_left ((measurable_one.indicator hmDu).add
        (measurable_one.indicator hmDv)),
      lintegral_add_left (measurable_one.indicator hmDu),
      lintegral_add_left measurable_const, lintegral_const_mul 2
        (measurable_one.indicator hmQ),
      lintegral_indicator_one hmDu, lintegral_indicator_one hmDv,
      lintegral_indicator_one hmDw, lintegral_indicator_one hmQ] at key
    simpa [Measure.restrict_apply, hmDu, hmDv, hmDw, hmQ, MeasurableSet.univ] using key
  -- ## The double cone is twice the cone
  have hQP : Q ∩ Bl = (P ∩ Bl) ∪ (-(P ∩ Bl)) := by
    ext x
    simp only [hQdef, hPdef, hBl, mem_inter_iff, mem_setOf_eq, mem_union, Set.mem_neg,
      mem_ball_zero_iff, norm_neg]
    have hco : ∀ i, co i (-x) = -co i x := by
      intro i; simp [hcodef]
    rw [hco 0, hco 1, hco 2]
    constructor
    · rintro ⟨⟨h1, h2⟩, hb⟩
      rcases lt_trichotomy (co 1 x) 0 with hc | hc | hc
      · right
        refine ⟨⟨?_, ?_, ?_⟩, hb⟩ <;> nlinarith
      · exfalso; rw [hc] at h1; simp at h1
      · left
        refine ⟨⟨?_, ?_, ?_⟩, hb⟩ <;> nlinarith
    · rintro (⟨⟨h1, h2, h3⟩, hb⟩ | ⟨⟨h1, h2, h3⟩, hb⟩)
      · exact ⟨⟨by positivity, by positivity⟩, hb⟩
      · exact ⟨⟨by nlinarith, by nlinarith⟩, hb⟩
  have hdisj : Disjoint (P ∩ Bl) (-(P ∩ Bl)) := by
    rw [Set.disjoint_left]
    rintro x ⟨hx, -⟩ hx'
    rw [Set.mem_neg] at hx'
    have hco : co 0 (-x) = -co 0 x := by simp [hcodef]
    have := hx'.1
    rw [hPdef] at hx this
    simp only [mem_setOf_eq] at hx this
    rw [hco] at this
    linarith [hx.1, this.1]
  have hQvol : volume (Q ∩ Bl) = 2 * volume (P ∩ Bl) := by
    rw [hQP, measure_union hdisj (((hmP.inter measurableSet_ball).neg)),
      Measure.measure_neg]
    ring
  -- ## The cone over the triangle
  have hcone : coneOver (sphTriangle u v w) = P ∩ Bl := by
    ext x
    simp only [coneOver, sphTriangle, mem_setOf_eq, mem_inter_iff, hBl, mem_ball_zero_iff]
    constructor
    · rintro ⟨r, hr0, hr1, y, ⟨hy1, a, b, c, ha, hb, hc, rfl⟩, rfl⟩
      constructor
      · rw [hPdef]
        have hx : r • (a • u + b • v + c • w) = (r * a) • u + (r * b) • v + (r * c) • w := by
          module
        simp only [mem_setOf_eq, hx]
        refine ⟨?_, ?_, ?_⟩
        · rw [huniq _ _ _ 0]; simpa using mul_pos hr0 ha
        · rw [huniq _ _ _ 1]; simpa using mul_pos hr0 hb
        · rw [huniq _ _ _ 2]; simpa using mul_pos hr0 hc
      · rw [norm_smul, hy1, Real.norm_eq_abs, abs_of_pos hr0, mul_one]
        exact hr1
    · rintro ⟨hxP, hxb⟩
      rw [hPdef] at hxP
      simp only [mem_setOf_eq] at hxP
      have hx0 : x ≠ 0 := by
        intro h
        rw [h] at hxP
        simp only [hcodef, map_zero] at hxP
        exact absurd hxP.1 (by simp)
      have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx0
      refine ⟨‖x‖, hnx, hxb, ‖x‖⁻¹ • x, ⟨?_, ?_⟩, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnx.ne']
      · refine ⟨‖x‖⁻¹ * co 0 x, ‖x‖⁻¹ * co 1 x, ‖x‖⁻¹ * co 2 x, ?_, ?_, ?_, ?_⟩
        · exact mul_pos (by positivity) hxP.1
        · exact mul_pos (by positivity) hxP.2.1
        · exact mul_pos (by positivity) hxP.2.2
        · rw [← smul_smul, ← smul_smul, ← smul_smul, ← smul_add, ← smul_add, hrep x]
      · rw [smul_smul, mul_inv_cancel₀ hnx.ne', one_smul]
  -- ## The volume of each wedge
  have hstu : ∀ a b : ℝ, a • (v - ⟪u, v⟫ • u) + b • (w - ⟪u, w⟫ • u) = 0 → a = 0 ∧ b = 0 := by
    intro a b h
    have h' : (-(a * ⟪u, v⟫ + b * ⟪u, w⟫)) • u + a • v + b • w = 0 := by
      rw [← h]; module
    obtain ⟨-, ha, hb⟩ := hzero _ _ _ h'
    exact ⟨ha, hb⟩
  have hstv : ∀ a b : ℝ, a • (u - ⟪v, u⟫ • v) + b • (w - ⟪v, w⟫ • v) = 0 → a = 0 ∧ b = 0 := by
    intro a b h
    have h' : a • u + (-(a * ⟪v, u⟫ + b * ⟪v, w⟫)) • v + b • w = 0 := by
      rw [← h]; module
    obtain ⟨ha, -, hb⟩ := hzero _ _ _ h'
    exact ⟨ha, hb⟩
  have hstw : ∀ a b : ℝ, a • (u - ⟪w, u⟫ • w) + b • (v - ⟪w, v⟫ • w) = 0 → a = 0 ∧ b = 0 := by
    intro a b h
    have h' : a • u + b • v + (-(a * ⟪w, u⟫ + b * ⟪w, v⟫)) • w = 0 := by
      rw [← h]; module
    obtain ⟨ha, hb, -⟩ := hzero _ _ _ h'
    exact ⟨ha, hb⟩
  have hvolDu : volume (Du ∩ Bl) = ENNReal.ofReal (4 * sphAngle u v w / 3) := by
    rw [← volume_dblWedge u v w hu hstu]
    congr 1
    ext x
    simp only [mem_inter_iff, hDudef, mem_setOf_eq, hDu x, hBl]
  have hvolDv : volume (Dv ∩ Bl) = ENNReal.ofReal (4 * sphAngle v u w / 3) := by
    rw [← volume_dblWedge v u w hv hstv]
    congr 1
    ext x
    simp only [mem_inter_iff, hDvdef, mem_setOf_eq, hDv x, hBl]
  have hvolDw : volume (Dww ∩ Bl) = ENNReal.ofReal (4 * sphAngle w u v / 3) := by
    rw [← volume_dblWedge w u v hw hstw]
    congr 1
    ext x
    simp only [mem_inter_iff, hDwdef, mem_setOf_eq, hDw x, hBl]
  -- ## Putting everything together
  have hPfin : volume (P ∩ Bl) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono Set.inter_subset_right)
    rw [hBl, volume_unit_ball]
    exact ENNReal.ofReal_ne_top
  have ha1 : 0 ≤ sphAngle u v w := angle_nonneg _ _
  have ha2 : 0 ≤ sphAngle v u w := angle_nonneg _ _
  have ha3 : 0 ≤ sphAngle w u v := angle_nonneg _ _
  have hpi : 0 < π := Real.pi_pos
  set tt : ℝ := (volume (P ∩ Bl)).toReal with httdef
  have htt0 : 0 ≤ tt := ENNReal.toReal_nonneg
  have hPeq : volume (P ∩ Bl) = ENNReal.ofReal tt := (ENNReal.ofReal_toReal hPfin).symm
  rw [hvolDu, hvolDv, hvolDw, hQvol, hPeq, hBl, volume_unit_ball,
    ← ENNReal.ofReal_add (by linarith) (by linarith),
    ← ENNReal.ofReal_add (by linarith) (by linarith)] at hcount
  have h4 : (2 : ℝ≥0∞) * (2 * ENNReal.ofReal tt) = ENNReal.ofReal (4 * tt) := by
    rw [show (4 : ℝ) * tt = 4 * tt by ring, ENNReal.ofReal_mul (by norm_num)]
    rw [show ENNReal.ofReal (4:ℝ) = 4 by
      rw [show (4:ℝ) = ((4:ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]; norm_num]
    ring
  rw [h4, ← ENNReal.ofReal_add (by linarith) (by linarith)] at hcount
  have hreal : 4 * sphAngle u v w / 3 + 4 * sphAngle v u w / 3 + 4 * sphAngle w u v / 3
      = 4 * π / 3 + 4 * tt := by
    have := (ENNReal.ofReal_eq_ofReal_iff (by linarith) (by linarith)).1 hcount
    exact this
  rw [sphArea, hcone, ← httdef]
  linarith


/-! ### An example: the positive octant -/

/-- For pairwise orthogonal vertices the interior angle at each vertex is a right angle. -/
lemma sphAngle_of_orthogonal (u v w : E3) (huv : ⟪u, v⟫ = 0) (huw : ⟪u, w⟫ = 0)
    (hvw : ⟪v, w⟫ = 0) : sphAngle u v w = π / 2 := by
  rw [sphAngle, huv, huw]
  simp only [zero_smul, sub_zero]
  exact (inner_eq_zero_iff_angle_eq_pi_div_two v w).1 hvw

/-- The spherical triangle cut out by the standard basis vectors (an octant of the unit
sphere) has area `π / 2`, one eighth of the area `4 * π` of the whole sphere. -/
theorem sphArea_octant :
    sphArea (sphTriangle (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
      (EuclideanSpace.single 2 1)) = π / 2 := by
  set u : E3 := EuclideanSpace.single 0 1 with hudef
  set v : E3 := EuclideanSpace.single 1 1 with hvdef
  set w : E3 := EuclideanSpace.single 2 1 with hwdef
  have hnorm : ∀ i : Fin 3, ‖(EuclideanSpace.single i (1 : ℝ) : E3)‖ = 1 := by
    intro i; rw [EuclideanSpace.norm_single]; norm_num
  have hinner : ∀ i j : Fin 3, i ≠ j →
      ⟪(EuclideanSpace.single i (1 : ℝ) : E3), EuclideanSpace.single j 1⟫ = 0 := by
    intro i j hij
    rw [EuclideanSpace.inner_single_left]
    simp [EuclideanSpace.single_apply, hij]
  have huv : ⟪u, v⟫ = 0 := hinner 0 1 (by decide)
  have huw : ⟪u, w⟫ = 0 := hinner 0 2 (by decide)
  have hvw : ⟪v, w⟫ = 0 := hinner 1 2 (by decide)
  have hvu : ⟪v, u⟫ = 0 := by rw [real_inner_comm]; exact huv
  have hwu : ⟪w, u⟫ = 0 := by rw [real_inner_comm]; exact huw
  have hwv : ⟪w, v⟫ = 0 := by rw [real_inner_comm]; exact hvw
  have hind : LinearIndependent ℝ ![u, v, w] := by
    have h : ![u, v, w] = ⇑(EuclideanSpace.basisFun (Fin 3) ℝ).toBasis := by
      funext i
      fin_cases i <;> simp [hudef, hvdef, hwdef, EuclideanSpace.basisFun] <;> rfl
    rw [h]
    exact (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.linearIndependent
  have key := gauss_bonnet_polygon u v w (hnorm 0) (hnorm 1) (hnorm 2) hind
  rw [sphAngle_of_orthogonal u v w huv huw hvw,
    sphAngle_of_orthogonal v u w hvu hvw huw,
    sphAngle_of_orthogonal w u v hwu hwv huv] at key
  linarith

end Math

