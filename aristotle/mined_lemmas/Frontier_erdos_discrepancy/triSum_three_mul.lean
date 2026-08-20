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

theorem triSum_three_mul : ∀ m : ℕ, triSum (3 * m) = triSum m := by
  intro m
  induction m with
  | zero => rfl
  | succ j ih =>
      have h1 : triSeq (3 * j + 1) = 1 := triSeq_mod_one (by omega)
      have h2 : triSeq (3 * j + 2) = -1 := triSeq_mod_two (by omega)
      have h3 : triSeq (3 * j + 3) = triSeq (j + 1) := by
        rw [show 3 * j + 3 = 3 * (j + 1) from by ring, triSeq_three_mul]
      have e1 : triSum (3 * j + 1) = triSum (3 * j) + triSeq (3 * j + 1) := triSum_succ _
      have e2 : triSum (3 * j + 2) = triSum (3 * j + 1) + triSeq (3 * j + 2) := triSum_succ _
      have e3 : triSum (3 * j + 3) = triSum (3 * j + 2) + triSeq (3 * j + 3) := triSum_succ _
      have e4 : triSum (j + 1) = triSum j + triSeq (j + 1) := triSum_succ _
      rw [show 3 * (j + 1) = 3 * j + 3 from by ring, e3, e2, e1, ih, h1, h2, h3, e4]
      ring

/-- One step past a multiple of `3` the partial sum increases by one. -/
