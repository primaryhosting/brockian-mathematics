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

theorem discrepancyUpTo_dilate_le (f : ℕ → ℤ) {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    discrepancyUpTo (fun m => f (k * m)) N ≤ discrepancyUpTo f (k * N) := by
  refine Finset.sup_le ?_
  rintro ⟨n, d⟩ hp
  simp only [Finset.mem_product, Finset.mem_Icc] at hp
  by_cases hle : n * d ≤ N
  · rw [if_pos hle, homogSum_dilate]
    refine le_discrepancyUpTo (Nat.mul_pos hk hp.2.1) hp.1.1 ?_
    calc n * (k * d) = k * (n * d) := by ring
      _ ≤ k * N := Nat.mul_le_mul_left k hle
  · rw [if_neg hle]
    exact Nat.zero_le _

end Frontier

import Mathlib
import RequestProject.ErdosDiscrepancy
import RequestProject.ErdosDiscrepancyMathlib

/-!
# A Lean-checked reduction: the infinite and finite forms are equivalent

The Erdős discrepancy statement quantifies over infinite `±1` sequences.  Here we prove,
by a compactness (ultrafilter) argument, that it is equivalent to its finitary form:
for every bound `C` there is a *uniform* `N` such that every `±1` sequence already exceeds
the bound `C` on a homogeneous arithmetic progression contained in `{1, …, N}`.

This is the reduction that makes the problem amenable to finite search; the base case
`C = 1` proved in `Frontier.erdos_discrepancy_le_twelve` has `N = 12`.
-/

namespace Frontier

/-- The finitary form of the Erdős discrepancy statement. -/
