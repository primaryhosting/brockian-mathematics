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

theorem triSum_le_log : ∀ n : ℕ, triSum n ≤ Nat.log 3 n + 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      rcases Nat.lt_or_ge n 3 with hsmall | hbig
      · interval_cases n
        · norm_num [triSum, homogSum]
        · rw [show (1 : ℕ) = 0 + 1 from rfl, triSum_succ]
          norm_num [triSum, homogSum, triSeq_mod_one]
        · rw [show (2 : ℕ) = 3 * 0 + 2 from rfl, triSum_three_mul_add_two]
          norm_num [triSum, homogSum]
      · have hn : 0 < n := by omega
        have hlt : n / 3 < n := Nat.div_lt_self hn (by norm_num)
        have hlog : Nat.log 3 (n / 3) + 1 = Nat.log 3 n := by
          have h1 : Nat.log 3 (n / 3) = Nat.log 3 n - 1 := Nat.log_div_base 3 n
          have h2 : 0 < Nat.log 3 n := Nat.log_pos (by norm_num) hbig
          omega
        have h3 := (triSum_div_three n).2
        have h4 := ih (n / 3) hlt
        have : (Nat.log 3 (n / 3) : ℤ) + 1 = (Nat.log 3 n : ℤ) := by exact_mod_cast hlog
        omega

/-- **The discrepancy of the base-`3` sequence is at most `log₃ n + 1` on every homogeneous
arithmetic progression.**  Together with `triSeq_unboundedDiscrepancy` this shows that its
discrepancy is unbounded but of logarithmic order. -/
