import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma indep3_of_linearIndependent {A B C : E3} (h : LinearIndependent ℝ ![A, B, C]) :
    Indep3 A B C := by
  intro a b c habc
  rw [Fintype.linearIndependent_iff] at h
  have hz := h ![a, b, c] (by simpa [Fin.sum_univ_three] using habc)
  exact ⟨by simpa using hz 0, by simpa using hz 1, by simpa using hz 2⟩

/-- Three linearly independent vectors span `E3`. -/
