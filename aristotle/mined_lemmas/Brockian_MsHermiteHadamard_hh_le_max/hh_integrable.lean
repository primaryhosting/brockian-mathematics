import Mathlib
namespace Brockian.MsHermiteHadamard

open MeasureTheory Set

/-- A convex function on `[a,b]` is bounded above by the max of its values at the endpoints. -/

lemma hh_integrable {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ConvexOn ℝ (Set.Icc a b) f) :
    IntervalIntegrable f volume a b := by
  have hcont : ContinuousOn f (Set.Ioo a b) := by
    have := hf.continuousOn_interior
    rwa [interior_Icc] at this
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le]
  have hfin : IsFiniteMeasure (volume.restrict (Set.Ioo a b)) := by
    constructor
    simp [Real.volume_Ioo]
  refine ⟨hcont.aestronglyMeasurable measurableSet_Ioo, ?_⟩
  refine HasFiniteIntegral.of_bounded
    (C := |max (f a) (f b)| + |2 * f ((a + b) / 2) - max (f a) (f b)|) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have h1 := hh_le_max hab.le hf (Ioo_subset_Icc_self hx)
  have h2 := hh_ge_min hab.le hf (Ioo_subset_Icc_self hx)
  have e1 := le_abs_self (max (f a) (f b))
  have e2 := neg_abs_le (2 * f ((a + b) / 2) - max (f a) (f b))
  have e3 := abs_nonneg (max (f a) (f b))
  have e4 := abs_nonneg (2 * f ((a + b) / 2) - max (f a) (f b))
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- A convex function lies below the chord joining `(a, f a)` and `(b, f b)`. -/
