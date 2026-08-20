import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma lintegral_prod_fst (f : ℝ → ℝ≥0∞) (hf : Measurable f) (s t : Set ℝ) :
    ∫⁻ p in s ×ˢ t, f p.1 = (∫⁻ r in s, f r) * volume t := by
  rw [(by rfl : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume),
    ← Measure.prod_restrict]
  rw [show (fun p : ℝ × ℝ => f p.1) = (fun p : ℝ × ℝ => f p.1 * (fun _ : ℝ => (1:ℝ≥0∞)) p.2) by
    funext p; simp]
  rw [lintegral_prod_mul hf.aemeasurable aemeasurable_const]
  simp

/-- The planar integral over the sector cut out by two half-planes. -/
