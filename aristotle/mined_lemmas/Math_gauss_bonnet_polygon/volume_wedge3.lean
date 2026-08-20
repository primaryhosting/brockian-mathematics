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

theorem volume_wedge3 (θ : ℝ) (h0 : 0 < θ) (hpi : θ < π) :
    volume {q : ℝ × (ℝ × ℝ) | q.1^2 + q.2.1^2 + q.2.2^2 < 1 ∧ 0 < q.2.1 ∧
      0 < Real.cos θ * q.2.1 + Real.sin θ * q.2.2} = ENNReal.ofReal (2 * (π - θ) / 3) := by
  have hTo : IsOpen {q : ℝ × (ℝ × ℝ) | q.1^2 + q.2.1^2 + q.2.2^2 < 1 ∧ 0 < q.2.1 ∧
      0 < Real.cos θ * q.2.1 + Real.sin θ * q.2.2} := by
    have hset : {q : ℝ × (ℝ × ℝ) | q.1^2 + q.2.1^2 + q.2.2^2 < 1 ∧ 0 < q.2.1 ∧
        0 < Real.cos θ * q.2.1 + Real.sin θ * q.2.2}
        = ({q : ℝ × (ℝ × ℝ) | q.1^2 + q.2.1^2 + q.2.2^2 < 1} ∩ {q : ℝ × (ℝ × ℝ) | 0 < q.2.1})
          ∩ {q : ℝ × (ℝ × ℝ) | 0 < Real.cos θ * q.2.1 + Real.sin θ * q.2.2} := by
      ext q; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
    rw [hset]
    exact ((isOpen_lt (by fun_prop) (by fun_prop)).inter
      (isOpen_lt (by fun_prop) (by fun_prop))).inter (isOpen_lt (by fun_prop) (by fun_prop))
  rw [Measure.volume_eq_prod, Measure.prod_apply hTo.measurableSet]
  have hslice : ∀ t : ℝ, volume (Prod.mk t ⁻¹' {q : ℝ × (ℝ × ℝ) |
      q.1^2 + q.2.1^2 + q.2.2^2 < 1 ∧ 0 < q.2.1 ∧
      0 < Real.cos θ * q.2.1 + Real.sin θ * q.2.2})
      = ENNReal.ofReal ((π - θ)/2 * (1 - t^2)) := by
    intro t
    have hs : (Prod.mk t ⁻¹' {q : ℝ × (ℝ × ℝ) | q.1^2 + q.2.1^2 + q.2.2^2 < 1 ∧ 0 < q.2.1 ∧
        0 < Real.cos θ * q.2.1 + Real.sin θ * q.2.2})
        = {p : ℝ × ℝ | p.1^2 + p.2^2 < 1 - t^2 ∧ 0 < p.1 ∧
            0 < Real.cos θ * p.1 + Real.sin θ * p.2} := by
      ext p
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, h2, h3⟩
    rw [hs, volume_sector θ h0 hpi]
  simp_rw [hslice]
  rw [← lintegral_add_compl _ (measurableSet_Ioo (a := (-1:ℝ)) (b := 1))]
  have hcompl : ∫⁻ t in (Ioo (-1:ℝ) 1)ᶜ, ENNReal.ofReal ((π - θ)/2 * (1 - t^2)) = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ioo.compl
      (g := fun _ => (0 : ℝ≥0∞)) ?_, lintegral_zero]
    intro t ht
    have ht2 : 1 ≤ t^2 := by
      simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt] at ht
      rcases ht with h | h <;> nlinarith
    have hnn : (π - θ)/2 ≥ 0 := by linarith
    simp only [ENNReal.ofReal_eq_zero]
    nlinarith
  rw [hcompl, add_zero]
  have hint : IntegrableOn (fun t : ℝ => (π - θ)/2 * (1 - t^2)) (Ioo (-1:ℝ) 1) :=
    (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioo_subset_Icc_self
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo (-1:ℝ) 1)] fun t : ℝ => (π - θ)/2 * (1 - t^2) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    obtain ⟨h1, h2⟩ := ht
    have h3 : (0:ℝ) ≤ (π - θ)/2 := by linarith
    have h4 : (0:ℝ) ≤ 1 - t^2 := by nlinarith
    simpa using mul_nonneg h3 h4
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegral.intervalIntegrable_pow 2)]
  simp [integral_pow]
  ring

/-- The volume of the standard wedge of the unit ball of `ℝ³`, cut out by the half-spaces
`{y 1 > 0}` and `{cos θ · y 1 + sin θ · y 2 > 0}`. -/
