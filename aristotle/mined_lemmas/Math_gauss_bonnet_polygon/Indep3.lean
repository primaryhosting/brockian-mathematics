import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma Indep3.rot {A B C : E3} (h : Indep3 A B C) : Indep3 B C A := by
  intro a b c habc
  obtain ⟨h1, h2, h3⟩ := h c a b (by rw [← habc]; module)
  exact ⟨h2, h3, h1⟩

/-! ### Two auxiliary facts about a pair of vectors -/

/-- The Gram determinant of two vectors, one nonzero and not parallel, is positive. -/
