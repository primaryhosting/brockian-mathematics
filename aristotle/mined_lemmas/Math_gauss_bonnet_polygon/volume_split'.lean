import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma volume_split' (S : Set E3) (hS : MeasurableSet S) (n : E3) (hn : n ≠ 0) :
    volume S = volume (S ∩ {x | 0 ≤ (1 : ℝ) * ⟪x, n⟫}) + volume (S ∩ {x | 0 ≤ (-1 : ℝ) * ⟪x, n⟫}) := by
  rw [volume_split S hS n hn]
  congr 2 <;> · ext x; simp only [mem_inter_iff, mem_setOf_eq, one_mul, neg_mul, neg_nonneg]

