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

theorem discrepancyUpTo_goodSeq_eleven : discrepancyUpTo goodSeq 11 = 1 := by
  refine le_antisymm (Finset.sup_le ?_) ?_
  · rintro ⟨n, d⟩ hp
    simp only [Finset.mem_product, Finset.mem_Icc] at hp
    by_cases hle : n * d ≤ 11
    · rw [if_pos hle]
      exact goodSeq_discrepancy_le_one d n hp.2.1 hp.1.1 hle
    · rw [if_neg hle]
      exact Nat.zero_le 1
  · have : (homogSum goodSeq 1 1).natAbs ≤ discrepancyUpTo goodSeq 11 :=
      le_discrepancyUpTo le_rfl le_rfl (by norm_num)
    simpa [homogSum, goodSeq, goodPattern] using this

/-- **The logarithmic example**: the base-`3` sequence has discrepancy at most
`log₃ N + 1` within `{1, …, N}`. -/
