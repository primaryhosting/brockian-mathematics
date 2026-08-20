import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma exists_repr {A B C : E3} (h : LinearIndependent ℝ ![A, B, C]) (x : E3) :
    ∃ a b c : ℝ, x = a • A + b • B + c • C := by
  have hcard : Fintype.card (Fin 3) = finrank ℝ E3 := by simp
  let b := basisOfLinearIndependentOfCardEqFinrank h hcard
  have hb : ⇑b = ![A, B, C] := coe_basisOfLinearIndependentOfCardEqFinrank h hcard
  refine ⟨b.repr x 0, b.repr x 1, b.repr x 2, ?_⟩
  have hsum := b.sum_repr x
  rw [Fin.sum_univ_three, hb] at hsum
  simpa using hsum.symm

