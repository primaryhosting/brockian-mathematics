import RequestProject.Main
/-!
# Gleason's theorem fails in dimension two

This file complements `RequestProject/Main.lean`.  It constructs an explicit quantum measure on
the projection lattice of `ℂ²` which does not come from any density operator, showing that the
dimension hypothesis `3 ≤ N` in Gleason's theorem cannot be dropped.

The measure is the two-valued "lexicographic sign" measure: in dimension two the only nontrivial
orthogonality relation between projections is `Q = 1 - P` for a rank-one projection `P`, so any
function on rank-one projections satisfying `f P + f (1 - P) = 1` is finitely additive.
-/

open scoped Classical
open scoped ComplexOrder

namespace Frontier

open Matrix

/-! ## Structure of projections in dimension two -/

/-- The Cayley–Hamilton identity for `2 × 2` matrices. -/

theorem badMeasure_isQuantumMeasure : IsQuantumMeasure badMeasure := by
  refine ⟨fun P _ => ?_, badMeasure_one, fun P Q hP hQ hPQ => ?_⟩
  · rw [badMeasure]; split <;> norm_num
  by_cases hP0 : P = 0
  · subst hP0; rw [zero_add, badMeasure_zero, zero_add]
  by_cases hQ0 : Q = 0
  · subst hQ0; rw [add_zero, badMeasure_zero, add_zero]
  have hsum : P + Q = 1 := dimTwo_orthogonal_complement hP hQ hPQ hP0 hQ0
  have hQeq : Q = 1 - P := by rw [← hsum]; abel
  obtain ⟨-, hentry⟩ := dimTwo_proj_entries hP
  have hne : (P 0 0).re = 1 / 2 → ((P 0 1).re ≠ 0 ∨ (P 0 1).im ≠ 0) := by
    intro hx
    rw [hx] at hentry
    have hnsq : Complex.normSq (P 0 1) = 1 / 4 := by nlinarith [hentry]
    have hb : P 0 1 ≠ 0 := by
      intro hb0
      rw [hb0] at hnsq
      norm_num [Complex.normSq_apply] at hnsq
    by_contra hcon
    push_neg at hcon
    exact hb (Complex.ext hcon.1 hcon.2)
  have h00 : ((1 : Matrix (Fin 2) (Fin 2) ℂ) - P) 0 0 = 1 - P 0 0 := by
    simp [Matrix.sub_apply]
  have h01 : ((1 : Matrix (Fin 2) (Fin 2) ℂ) - P) 0 1 = -(P 0 1) := by
    simp [Matrix.sub_apply]
  rw [hsum, badMeasure_one, badMeasure, hQeq, badMeasure, h00, h01]
  simpa using (sgnPos_add_compl (P 0 0).re (P 0 1).re (P 0 1).im hne).symm

/-! ## The measure is not given by a density operator -/

/-- The projection onto the first coordinate axis of `ℂ²`. -/
