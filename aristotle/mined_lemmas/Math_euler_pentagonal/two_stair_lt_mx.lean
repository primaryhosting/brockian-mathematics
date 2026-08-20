/-
Franklin's involution and the combinatorial core of Euler's pentagonal number theorem.
-/
import Mathlib

namespace EulerPentagonal

open Finset

/-- The minimum of a finset of naturals (`0` for the empty set). -/

lemma two_stair_lt_mx (h0 : 0 ∉ S) (hne : S.Nonempty) (hB : stair S < mn S) (hnex : ¬ IsExc S) :
    2 * stair S < mx S := by
  have hst1 : 1 ≤ stair S := one_le_stair h0 hne
  have hstM := stair_le_mx (S := S)
  rcases eq_or_lt_of_le (stair_le_card h0 hne) with heq | hlt
  · have hSeq : S = Finset.Icc (mx S + 1 - stair S) (mx S) :=
      eq_stair_block_of_card h0 hne heq.symm
    have hmn' : mn S = mx S + 1 - stair S := by
      conv_lhs => rw [hSeq]
      exact mn_Icc (by omega)
    have hM2 : mx S ≠ 2 * stair S := by
      intro hcon
      refine hnex ⟨stair S, hst1, Or.inr ?_⟩
      have hIcc : Finset.Icc (stair S + 1) (2 * stair S)
          = Finset.Icc (mx S + 1 - stair S) (mx S) := by
        congr 1 <;> omega
      rw [hIcc]
      exact hSeq
    omega
  · have := mn_lt_of_stair_lt_card h0 hne hlt
    omega

/-- The properties of Franklin's move in case B. -/
