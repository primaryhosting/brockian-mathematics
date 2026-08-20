import Mathlib
import RequestProject.ErdosDiscrepancy
import RequestProject.ErdosDiscrepancyMathlib
import RequestProject.ErdosDiscrepancySpecialCases
import RequestProject.ErdosDiscrepancyMeasure

/-!
# The base case for completely multiplicative sequences

For a completely multiplicative `±1` sequence every homogeneous sum is `f d` times an
ordinary partial sum, so only the sums `S n = f 1 + ⋯ + f n` matter.  Tracking the four
values `f 2, f 3, f 5, f 7` shows that one of `S 4, S 6, S 8, S 10` must exceed `1` in
absolute value: for completely multiplicative sequences the length `10` already forces
discrepancy `2` (as opposed to `12` in general).
-/

namespace Frontier

/-- Unfolding the ordinary partial sums. -/

theorem discrepancy_one_classification (f : ℕ → ℤ) (hf : IsPMOne f)
    (h : ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → n * d ≤ 11 → (homogSum f d n).natAbs ≤ 1) :
    [f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11] ∈
      [[(1 : ℤ), -1, -1, 1, -1, 1, 1, -1, -1, 1, 1],
       [-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, 1],
       [1, -1, -1, 1, -1, 1, 1, -1, -1, 1, -1],
       [-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1]] := by
  set L : List ℤ := [f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11] with hL
  -- the pattern is a `±1` pattern of length `11`
  have hmem : L ∈ pmLists 11 := by
    have hall : ∀ x ∈ L, x = 1 ∨ x = -1 := by
      intro x hx
      simp only [hL, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hf _ (by norm_num)
    have := mem_pmLists L hall
    simpa [hL] using this
  -- the values of the pattern are the values of `f`
  have hseq : ∀ k : ℕ, 1 ≤ k → k ≤ 11 → listSeq L k = f k := by
    intro k h1 h2
    interval_cases k <;> rfl
  -- the pattern has discrepancy at most `1`
  have hlow : lowDisc L = true := by
    simp only [lowDisc, List.all_eq_true]
    intro d hd n hn
    simp only [List.mem_range'_1] at hd hn
    by_cases hle : n * d ≤ 11
    · simp only [if_pos hle, decide_eq_true_eq]
      have hcong : homogSum (listSeq L) d n = homogSum f d n :=
        homogSum_congr hd.1 fun k hk1 hk2 => hseq k hk1 (le_trans hk2 hle)
      rw [hcong]
      exact h d n hd.1 hn.1 hle
    · simp [hle]
  -- hence the pattern occurs in the enumerated list
  have : L ∈ (pmLists 11).filter lowDisc := List.mem_filter.mpr ⟨hmem, hlow⟩
  rwa [pmLists_filter_lowDisc] at this

/-- The discrepancy-one patterns agree, up to a global sign, on `{1, …, 10}`. -/
