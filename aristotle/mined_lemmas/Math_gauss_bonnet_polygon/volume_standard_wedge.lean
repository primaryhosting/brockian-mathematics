import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma volume_standard_wedge (ψ : ℝ) (h0 : 0 < ψ) (hπ : ψ < π) :
    volume {y : EuclideanSpace ℝ (Fin 3) | ‖y‖ ≤ 1 ∧ 0 ≤ y 0 ∧ 0 ≤ cos ψ * y 0 + sin ψ * y 1}
      = ENNReal.ofReal (2 * (π - ψ) / 3) := by
  set D : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ cos ψ * p.1 + sin ψ * p.2} with hDdef
  have hDmeas : MeasurableSet D :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_const
        ((measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd)))
  have hnm : Measurable fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖ := by fun_prop
  have hc0 : Measurable fun y : EuclideanSpace ℝ (Fin 3) => y 0 :=
    (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 3) => y 0).measurable
  have hc1 : Measurable fun y : EuclideanSpace ℝ (Fin 3) => y 1 :=
    (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 3) => y 1).measurable
  have hSmeas : MeasurableSet
      {y : EuclideanSpace ℝ (Fin 3) | ‖y‖ ≤ 1 ∧ 0 ≤ y 0 ∧ 0 ≤ cos ψ * y 0 + sin ψ * y 1} :=
    (measurableSet_le hnm measurable_const).inter
      ((measurableSet_le measurable_const hc0).inter
        (measurableSet_le measurable_const
          ((measurable_const.mul hc0).add (measurable_const.mul hc1))))
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage hSmeas.nullMeasurableSet]
  have hpre : (WithLp.toLp 2) ⁻¹'
        {y : EuclideanSpace ℝ (Fin 3) | ‖y‖ ≤ 1 ∧ 0 ≤ y 0 ∧ 0 ≤ cos ψ * y 0 + sin ψ * y 1}
      = {z : Fin 3 → ℝ | z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 ≤ 1 ∧ (z 0, z 1) ∈ D} := by
    ext z
    simp only [mem_preimage, mem_setOf_eq, hDdef]
    have hnorm : ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin 3))‖ = √(z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2) := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      rw [Fin.sum_univ_three]
      simp [sq_abs]
    rw [hnorm, Real.sqrt_le_one]
  rw [hpre, volume_pi3 D hDmeas, hDdef, lintegral_sector ψ h0 hπ]

/-- Measurability of the standard wedge. -/
