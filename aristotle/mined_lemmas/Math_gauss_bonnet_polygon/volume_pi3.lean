import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma volume_pi3 (D : Set (ℝ × ℝ)) (hD : MeasurableSet D) :
    volume {z : Fin 3 → ℝ | z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 ≤ 1 ∧ (z 0, z 1) ∈ D}
      = ∫⁻ p in D, ENNReal.ofReal (2 * √(1 - p.1 ^ 2 - p.2 ^ 2)) := by
  have hSmeas :
      MeasurableSet {z : Fin 3 → ℝ | z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 ≤ 1 ∧ (z 0, z 1) ∈ D} := by
    refine MeasurableSet.inter ?_ ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1) hD)
    have h : Measurable fun z : Fin 3 → ℝ => z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by fun_prop
    exact measurableSet_le h measurable_const
  rw [← measurePreserving_coords3.measure_preimage hSmeas.nullMeasurableSet]
  have hpre : coords3 ⁻¹' {z : Fin 3 → ℝ | z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 ≤ 1 ∧ (z 0, z 1) ∈ D}
      = {q : (ℝ × ℝ) × ℝ | q.1.1 ^ 2 + q.1.2 ^ 2 + q.2 ^ 2 ≤ 1 ∧ q.1 ∈ D} := by
    ext q
    simp [coords3]
  rw [hpre]
  have hS'meas :
      MeasurableSet {q : (ℝ × ℝ) × ℝ | q.1.1 ^ 2 + q.1.2 ^ 2 + q.2 ^ 2 ≤ 1 ∧ q.1 ∈ D} := by
    refine MeasurableSet.inter ?_ (measurable_fst hD)
    have h : Measurable fun q : (ℝ × ℝ) × ℝ => q.1.1 ^ 2 + q.1.2 ^ 2 + q.2 ^ 2 := by fun_prop
    exact measurableSet_le h measurable_const
  rw [show (volume : Measure ((ℝ × ℝ) × ℝ)) = (volume : Measure (ℝ × ℝ)).prod volume from rfl,
    Measure.prod_apply hS'meas, ← lintegral_indicator hD]
  congr 1
  funext p
  by_cases hp : p ∈ D
  · rw [Set.indicator_of_mem hp]
    have hslice : (Prod.mk p ⁻¹' {q : (ℝ × ℝ) × ℝ | q.1.1 ^ 2 + q.1.2 ^ 2 + q.2 ^ 2 ≤ 1 ∧ q.1 ∈ D})
        = {t : ℝ | t ^ 2 ≤ 1 - p.1 ^ 2 - p.2 ^ 2} := by
      ext t
      simp only [mem_preimage, mem_setOf_eq, hp, and_true]
      constructor <;> intro h <;> linarith
    rw [hslice, volume_sq_le]
  · rw [Set.indicator_of_notMem hp]
    have hslice : (Prod.mk p ⁻¹' {q : (ℝ × ℝ) × ℝ | q.1.1 ^ 2 + q.1.2 ^ 2 + q.2 ^ 2 ≤ 1 ∧ q.1 ∈ D})
        = ∅ := by
      ext t
      simp [hp]
    rw [hslice]
    simp

/-- The angular condition describing the sector. -/
